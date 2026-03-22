#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cfst.py — CloudflareSpeedTest Python 移植版
原项目: https://github.com/XIU2/CloudflareSpeedTest
移植: 将完整 Go 实现翻译为单文件 Python 3.8+ 脚本

依赖（均为标准库，无需额外安装）:
    socket, threading, queue, csv, re, random, ipaddress,
    time, argparse, sys, os, urllib.request, struct

可选（安装后自动启用彩色输出）:
    pip install colorama
"""

import argparse
import concurrent.futures
import csv
import ipaddress
import os
import random
import re
import socket
import ssl
import sys
import threading
import time
import urllib.request
import urllib.error
from dataclasses import dataclass
from typing import List, Optional, Tuple
from urllib.parse import urlparse, urljoin

# ──────────────────────────────────────────────
# 平台线程限制检测
# iOS (a-Shell / Pythonista 等) 进程级线程数上限约 64
# 安全起见统一限制到 32（留余量给解释器自身线程）
# ──────────────────────────────────────────────
def _platform_max_routines() -> int:
    # sys.platform == 'ios' 适用于 Pythonista；
    # a-Shell 报告 'darwin' 但路径含 private/var/mobile
    if sys.platform == "ios":
        return 32
    if sys.platform == "darwin" and (
        "/var/mobile" in sys.executable or
        "/var/mobile" in (os.environ.get("HOME", ""))
    ):
        return 32
    return 1000   # 桌面 / 服务器平台不限制

# ──────────────────────────────────────────────
# 彩色输出（有 colorama 就用，否则降级为普通文本）
# ──────────────────────────────────────────────
try:
    from colorama import init as _colorama_init, Fore, Style
    _colorama_init(autoreset=True)
    def _red(s):    return Fore.RED    + str(s) + Style.RESET_ALL
    def _green(s):  return Fore.GREEN  + str(s) + Style.RESET_ALL
    def _yellow(s): return Fore.YELLOW + str(s) + Style.RESET_ALL
    def _cyan(s):   return Fore.CYAN   + Style.BRIGHT + str(s) + Style.RESET_ALL
except ImportError:
    def _red(s):    return str(s)
    def _green(s):  return str(s)
    def _yellow(s): return str(s)
    def _cyan(s):   return str(s)


# ──────────────────────────────────────────────
# 进度条（纯标准库实现）
# ──────────────────────────────────────────────
class Bar:
    _SPIN = ["↖", "↗", "↘", "↙"]

    def __init__(self, total: int, prefix: str = "", suffix: str = ""):
        self.total   = max(total, 1)
        self.prefix  = prefix
        self.suffix  = suffix
        self._count  = 0
        self._spin_i = 0
        self._lock   = threading.Lock()
        self._done   = False
        self._extra  = ""
        self._bar_width = 50

    def grow(self, n: int = 1, extra: str = ""):
        with self._lock:
            self._count  += n
            self._extra   = extra
            self._spin_i  = (self._spin_i + 1) % 4
            self._render()

    def done(self):
        with self._lock:
            self._done = True
            self._render()
            sys.stderr.write("\n")
            sys.stderr.flush()

    def _render(self):
        filled = int(self._bar_width * self._count / self.total)
        spin   = " " if self._done else self._SPIN[self._spin_i]
        bar    = "[" + "-" * filled + spin + "_" * (self._bar_width - filled) + "]"
        line   = f"\r{self._count:>5}/{self.total:<5} {bar} {self.prefix} {_green(self._extra)} {self.suffix} "
        sys.stderr.write(line)
        sys.stderr.flush()


# ──────────────────────────────────────────────
# 数据结构
# ──────────────────────────────────────────────
@dataclass
class PingData:
    ip:        str
    sent:      int   = 0
    received:  int   = 0
    delay_ms:  float = 0.0   # 平均延迟（毫秒）
    colo:      str   = ""

    @property
    def loss_rate(self) -> float:
        if self.sent == 0:
            return 1.0
        return (self.sent - self.received) / self.sent


@dataclass
class IPResult:
    ping:           PingData
    download_speed: float = 0.0   # bytes/s

    # ── 排序用（先丢包率升序，再延迟升序） ──
    def __lt__(self, other: "IPResult") -> bool:
        if self.ping.loss_rate != other.ping.loss_rate:
            return self.ping.loss_rate < other.ping.loss_rate
        return self.ping.delay_ms < other.ping.delay_ms


# ──────────────────────────────────────────────
# IP 段解析
# ──────────────────────────────────────────────
def _is_ipv4(ip: str) -> bool:
    return "." in ip

def load_ip_ranges(ip_file: str, ip_text: str, test_all: bool) -> List[str]:
    """返回所有待测速的 IP 字符串列表"""
    lines: List[str] = []

    if ip_text:
        import re as _re
        lines = [s.strip() for s in _re.split(r"[,\n\r]+", ip_text) if s.strip()]
    else:
        if not ip_file:
            ip_file = "ip.txt"
        try:
            with open(ip_file, "r", encoding="utf-8-sig") as f:
                lines = [l.strip() for l in f if l.strip()]
        except FileNotFoundError:
            sys.exit(f"[错误] 找不到 IP 数据文件: {ip_file}")

    result: List[str] = []
    for line in lines:
        # 补全单 IP 的子网掩码
        if "/" not in line:
            line += "/32" if _is_ipv4(line) else "/128"
        try:
            network = ipaddress.ip_network(line, strict=False)
        except ValueError:
            continue

        if isinstance(network, ipaddress.IPv4Network):
            result.extend(_pick_ipv4(network, test_all))
        else:
            result.extend(_pick_ipv6(network))

    return result


def _pick_ipv4(net: ipaddress.IPv4Network, test_all: bool) -> List[str]:
    """
    复现 Go 版逻辑：
    - /32  → 直接返回该 IP
    - test_all → 遍历每个 /24 子网的全部 IP（.0~.255）
    - 默认  → 每个 /24 子网随机一个 IP（含 .0 和 .255，与 Go 一致）
    """
    prefix = net.prefixlen
    if prefix == 32:
        return [str(net.network_address)]

    # 拆分为 /24 子网
    if prefix < 24:
        subnets = list(net.subnets(new_prefix=24))
    else:
        subnets = [net]

    picked: List[str] = []
    for sub in subnets:
        # Go 的 getIPRange 对 /24 返回 minIP=0, hosts=255
        # 即 IP 范围是 .0 ~ .254（randIPEndWith(255) 给出 0~254）
        # Python ipaddress.hosts() 会排除 .0 和 .255，与 Go 稍有差异
        # 此处用 int 直接操作来精确复现
        base    = int(sub.network_address)
        # Go: rand.Intn(hosts)，hosts=255 → 0~254
        max_last = 254 if sub.prefixlen == 24 else int(sub.num_addresses) - 1
        max_last = max(max_last, 0)

        if test_all:
            for i in range(max_last + 1):
                picked.append(str(ipaddress.IPv4Address(base + i)))
        else:
            picked.append(str(ipaddress.IPv4Address(base + random.randint(0, max_last))))
    return picked


def _pick_ipv6(net: ipaddress.IPv6Network) -> List[str]:
    prefix = net.prefixlen
    if prefix >= 128:
        return [str(net.network_address)]
    # 最多随机采样 128 个（IPv6 空间极大）
    count = min(128, 2 ** (128 - prefix))
    base  = int(net.network_address)
    mask  = (1 << (128 - prefix)) - 1
    picked = set()
    attempts = 0
    while len(picked) < count and attempts < count * 4:
        attempts += 1
        rand_offset = random.randint(0, mask)
        picked.add(str(ipaddress.IPv6Address(base | rand_offset)))
    return list(picked)


# ──────────────────────────────────────────────
# 地区码解析（复现 Go 版 getHeaderColo）
# ──────────────────────────────────────────────
_RE_IATA    = re.compile(r"[A-Z]{3}")
_RE_COUNTRY = re.compile(r"[A-Z]{2}")
_RE_GCORE   = re.compile(r"^[a-z]{2}")

def _get_header_colo(headers: dict) -> str:
    server = headers.get("server", "")
    if server:
        if server.lower() == "cloudflare":
            cf_ray = headers.get("cf-ray", "")
            if cf_ray:
                m = _RE_IATA.search(cf_ray)
                return m.group() if m else ""
        if server == "CDN77-Turbo":
            pop = headers.get("x-77-pop", "")
            if pop:
                m = _RE_COUNTRY.search(pop)
                return m.group() if m else ""
        if "BunnyCDN-" in server:
            trimmed = server.replace("BunnyCDN-", "")
            m = _RE_COUNTRY.search(trimmed)
            return m.group() if m else ""

    cf_pop = headers.get("x-amz-cf-pop", "")
    if cf_pop:
        m = _RE_IATA.search(cf_pop)
        return m.group() if m else ""

    x_served = headers.get("x-served-by", "")
    if x_served:
        matches = _RE_IATA.findall(x_served)
        if matches:
            return matches[-1]

    x_id_fe = headers.get("x-id-fe", "")
    if x_id_fe:
        m = _RE_GCORE.search(x_id_fe)
        if m:
            return m.group().upper()

    return ""


# ──────────────────────────────────────────────
# TCPing
# ──────────────────────────────────────────────
TCP_CONNECT_TIMEOUT = 1.0   # 秒

def _tcping_once(ip: str, port: int) -> Optional[float]:
    """返回延迟（秒），超时/失败返回 None"""
    try:
        fam = socket.AF_INET6 if ":" in ip else socket.AF_INET
        t0 = time.perf_counter()
        with socket.socket(fam, socket.SOCK_STREAM) as s:
            s.settimeout(TCP_CONNECT_TIMEOUT)
            s.connect((ip, port))
        return time.perf_counter() - t0
    except Exception:
        return None


def do_tcping(ip: str, port: int, times: int) -> PingData:
    delays = []
    for _ in range(times):
        d = _tcping_once(ip, port)
        if d is not None:
            delays.append(d)
    recv = len(delays)
    avg  = (sum(delays) / recv * 1000) if recv > 0 else 0.0
    return PingData(ip=ip, sent=times, received=recv, delay_ms=avg)


# ──────────────────────────────────────────────
# 底层 HTTP（强制 TCP 打到指定 IP）
# ──────────────────────────────────────────────
_DEFAULT_URL = "https://cf.xiu2.xyz/url"

def _raw_connect(ip: str, port: int, host: str, use_tls: bool,
                 timeout: float) -> socket.socket:
    """建立 TCP（或 TLS）连接，TCP 层强制打到 ip:port，TLS SNI 使用 host。"""
    raw = socket.create_connection((ip, port), timeout=timeout)
    if use_tls:
        ctx = ssl.create_default_context()
        raw = ctx.wrap_socket(raw, server_hostname=host)
    raw.settimeout(timeout)
    return raw


def _parse_response_head(sock: socket.socket) -> Tuple[int, dict, bytes]:
    """读取 HTTP 响应头，返回 (status_code, headers_dict, body_prefix)。"""
    raw_resp = b""
    while b"\r\n\r\n" not in raw_resp:
        chunk = sock.recv(4096)
        if not chunk:
            break
        raw_resp += chunk
        if len(raw_resp) > 65536:   # 防止头部超大
            break

    parts = raw_resp.split(b"\r\n\r\n", 1)
    header_bytes = parts[0]
    body_start   = parts[1] if len(parts) > 1 else b""

    header_text = header_bytes.decode("latin-1", errors="replace")
    lines = header_text.split("\r\n")
    try:
        status_code = int(lines[0].split(" ")[1])
    except (IndexError, ValueError):
        status_code = 0

    headers: dict = {}
    for line in lines[1:]:
        if ": " in line:
            k, v = line.split(": ", 1)
            headers[k.lower()] = v.strip()

    return status_code, headers, body_start


# ──────────────────────────────────────────────
# HTTPing（HEAD 请求，阻止重定向，与 Go 一致）
# ──────────────────────────────────────────────
HTTPING_TIMEOUT = 2.0   # 秒

def _http_head(ip: str, url: str, port: int,
               connection_close: bool = False) -> Tuple[int, dict]:
    """
    强制将 TCP 连接打到 ip:port，发送 HEAD 请求（不跟随重定向）。
    返回 (status_code, headers_dict)。
    connection_close=True 时加 Connection: close 头（Go 在最后一次 ping 时这样做）。
    """
    parsed      = urlparse(url)
    scheme      = parsed.scheme.lower()
    host        = parsed.hostname or ""
    path        = parsed.path or "/"
    if parsed.query:
        path += "?" + parsed.query

    use_tls      = (scheme == "https")
    connect_port = port if port else (443 if use_tls else 80)

    try:
        sock = _raw_connect(ip, connect_port, host, use_tls, HTTPING_TIMEOUT)
        conn_hdr = "close" if connection_close else "keep-alive"
        req = (
            f"HEAD {path} HTTP/1.1\r\n"
            f"Host: {host}\r\n"
            f"User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_12_6) "
            f"AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36\r\n"
            f"Connection: {conn_hdr}\r\n\r\n"
        )
        sock.sendall(req.encode())
        status, headers, _ = _parse_response_head(sock)
        sock.close()
        return status, headers
    except Exception:
        return 0, {}


def do_httping(ip: str, url: str, port: int, times: int,
               valid_codes: List[int], colo_filter: Optional[set],
               debug: bool) -> PingData:
    """
    先访问一次获取状态码和地区码，再循环 times 次计算平均延迟。
    Go 在最后一次请求加 Connection: close。
    """
    # 第一次：验证状态码 + 获取 colo
    status, headers = _http_head(ip, url, port, connection_close=False)
    if status == 0:
        if debug:
            print(_red(f"[调试] IP: {ip}, 延迟测速失败（连接错误）, 测速地址: {url}"))
        return PingData(ip=ip, sent=times, received=0)

    if valid_codes:
        if status not in valid_codes:
            if debug:
                print(_red(f"[调试] IP: {ip}, 延迟测速终止，HTTP 状态码: {status}, "
                           f"指定的 HTTP 状态码 {valid_codes}, 测速地址: {url}"))
            return PingData(ip=ip, sent=times, received=0)
    else:
        if status not in (200, 301, 302):
            if debug:
                print(_red(f"[调试] IP: {ip}, 延迟测速终止，HTTP 状态码: {status}, 测速地址: {url}"))
            return PingData(ip=ip, sent=times, received=0)

    colo = _get_header_colo(headers)

    if colo_filter is not None:
        matched = colo.upper() if colo.upper() in colo_filter else ""
        if not matched:
            if debug:
                print(_red(f"[调试] IP: {ip}, 地区码不匹配: {colo}"))
            return PingData(ip=ip, sent=times, received=0)
        colo = matched

    # 循环测速（最后一次加 Connection: close，与 Go 一致）
    delays = []
    for i in range(times):
        is_last = (i == times - 1)
        t0 = time.perf_counter()
        sc, _ = _http_head(ip, url, port, connection_close=is_last)
        elapsed = time.perf_counter() - t0
        if sc != 0:
            delays.append(elapsed)

    recv = len(delays)
    avg  = (sum(delays) / recv * 1000) if recv > 0 else 0.0
    return PingData(ip=ip, sent=times, received=recv, delay_ms=avg, colo=colo)


# ──────────────────────────────────────────────
# 延迟测速（多线程）
# ──────────────────────────────────────────────
def run_ping(
    ips:           List[str],
    port:          int,
    ping_times:    int,
    routines:      int,
    httping:       bool,
    url:           str,
    valid_codes:   List[int],
    colo_filter:   Optional[set],
    debug:         bool,
    min_delay_ms:  float = 0.0,
    max_delay_ms:  float = 9999.0,
    max_loss_rate: float = 1.0,
) -> List[IPResult]:
    mode = "HTTP" if httping else "TCP"
    # FIX: 显示实际的延迟范围和丢包上限（原代码硬编码了默认值）
    print(_cyan(
        f"开始延迟测速（模式：{mode}, 端口：{port}, "
        f"范围：{int(min_delay_ms)} ~ {int(max_delay_ms)} ms, "
        f"丢包：{max_loss_rate:.2f})"
    ))

    results: List[IPResult] = []
    lock    = threading.Lock()
    bar     = Bar(len(ips), "可用:", "")

    def worker(ip: str) -> None:
        try:
            if httping:
                pd = do_httping(ip, url, port, ping_times, valid_codes, colo_filter, debug)
            else:
                pd = do_tcping(ip, port, ping_times)
        except Exception:
            pd = PingData(ip=ip, sent=ping_times, received=0)

        with lock:
            now_able = len(results)
            if pd.received > 0:
                now_able += 1
                results.append(IPResult(ping=pd))
            bar.grow(1, str(now_able))

    # 使用线程池而非每 IP 单独创建线程
    # ThreadPoolExecutor 维护固定数量的工作线程，任务通过队列分发
    # 无论 IP 数量多少，OS 线程数始终 ≤ routines，不会触发 iOS 线程上限
    with concurrent.futures.ThreadPoolExecutor(max_workers=routines) as pool:
        futures = [pool.submit(worker, ip) for ip in ips]
        concurrent.futures.wait(futures)

    bar.done()
    results.sort()
    return results


# ──────────────────────────────────────────────
# 延迟 / 丢包过滤
# ──────────────────────────────────────────────
def filter_delay(results: List[IPResult], min_ms: float, max_ms: float) -> List[IPResult]:
    if min_ms == 0 and max_ms == 9999:
        return results
    out = []
    for r in results:
        if r.ping.delay_ms > max_ms:
            break   # 已按延迟升序，后续都超了（同一丢包率分组内）
        if r.ping.delay_ms < min_ms:
            continue
        out.append(r)
    return out


def filter_loss_rate(results: List[IPResult], max_loss: float) -> List[IPResult]:
    if max_loss >= 1.0:
        return results
    out = []
    for r in results:
        if r.ping.loss_rate > max_loss:
            break   # 已按丢包率升序排序
        out.append(r)
    return out


# ──────────────────────────────────────────────
# 简易 EWMA（复现 VividCortex/ewma，默认 age=15 → alpha≈0.125）
# ──────────────────────────────────────────────
class _EWMA:
    """指数加权移动平均，alpha = 2/(age+1)，与 Go VividCortex/ewma 默认值一致。"""
    _ALPHA = 2.0 / (15 + 1)   # age=15 → 0.125

    def __init__(self):
        self._value = 0.0
        self._count = 0

    def add(self, x: float):
        if self._count == 0:
            self._value = x
        else:
            self._value += self._ALPHA * (x - self._value)
        self._count += 1

    @property
    def value(self) -> float:
        return self._value


# ──────────────────────────────────────────────
# 下载测速（CRITICAL FIX：支持 HTTP 重定向，与 Go 完全对齐）
# ──────────────────────────────────────────────
BUFFER_SIZE = 1024   # bytes，与 Go 版保持一致

def _download_once(ip: str, url: str, port: int, timeout_s: float,
                   debug: bool) -> Tuple[float, str]:
    """
    返回 (speed_bytes_per_sec, colo)。

    【关键修复】原 Python 版对原始 socket 不跟随 HTTP 重定向，
    而 Go 版 http.Client 默认最多跟随 10 次重定向。
    默认下载测速地址 https://cf.xiu2.xyz/url 会先 302 跳转到实际文件，
    因此不处理重定向会导致下载速度永远为 0.00。

    本函数在跟随重定向时始终将 TCP 连接打到原始 ip:port（与 Go 保持一致）。
    """
    max_redirects   = 10
    redirect_count  = 0
    current_url     = url
    last_redirect   = ""
    colo            = ""

    # ── 处理重定向直到获得 200/206 ──
    while True:
        parsed      = urlparse(current_url)
        scheme      = parsed.scheme.lower()
        host        = parsed.hostname or ""
        path        = parsed.path or "/"
        if parsed.query:
            path += "?" + parsed.query

        use_tls      = (scheme == "https")
        connect_port = port if port else (443 if use_tls else 80)

        try:
            sock = _raw_connect(ip, connect_port, host, use_tls, timeout_s)
        except Exception as e:
            if debug:
                _print_dl_debug(ip, url, last_redirect, err=e)
            return 0.0, ""

        # 构造请求头（Go 在使用默认 URL 重定向时不带 Referer）
        headers_extra = ""
        if last_redirect and current_url != url and url != _DEFAULT_URL:
            headers_extra += f"Referer: {url}\r\n"

        req = (
            f"GET {path} HTTP/1.1\r\n"
            f"Host: {host}\r\n"
            f"User-Agent: Mozilla/5.0 (Macintosh; Intel Mac OS X 10_12_6) "
            f"AppleWebKit/537.36 (KHTML, like Gecko) Chrome/98.0.4758.80 Safari/537.36\r\n"
            f"{headers_extra}"
            f"Connection: close\r\n\r\n"
        )

        try:
            sock.sendall(req.encode())
            status_code, resp_headers, body_start = _parse_response_head(sock)
        except Exception as e:
            sock.close()
            if debug:
                _print_dl_debug(ip, url, last_redirect, err=e)
            return 0.0, ""

        # ── 3xx 重定向 ──
        if status_code in (301, 302, 307, 308):
            sock.close()
            if redirect_count >= max_redirects:
                # Go: http.ErrUseLastResponse → 停止跟随，使用最后响应
                if debug:
                    print(_red(f"[调试] IP: {ip}, 下载测速地址重定向次数过多，终止测速，"
                               f"下载测速地址: {current_url}"))
                return 0.0, ""
            location = resp_headers.get("location", "")
            if not location:
                if debug:
                    _print_dl_debug(ip, url, last_redirect, status=status_code)
                return 0.0, ""
            last_redirect  = urljoin(current_url, location)
            current_url    = last_redirect
            redirect_count += 1
            continue

        # ── 非 200/206 ──
        if status_code not in (200, 206):
            sock.close()
            if debug:
                _print_dl_debug(ip, url, last_redirect, status=status_code)
            return 0.0, ""

        # ── 成功，开始计量下载速度 ──
        colo = _get_header_colo(resp_headers)
        break

    # ── EWMA 滑动平均下载测速（完整复现 Go 版逻辑） ──
    time_start   = time.perf_counter()
    time_end     = time_start + timeout_s
    time_slice   = timeout_s / 100
    time_counter = 1
    next_time    = time_start + time_slice * time_counter
    content_read = len(body_start)
    last_read    = 0
    ewma         = _EWMA()

    while True:
        current_time = time.perf_counter()

        if current_time >= time_end:
            break

        if current_time >= next_time:
            time_counter += 1
            next_time = time_start + time_slice * time_counter
            ewma.add(float(content_read - last_read))
            last_read = content_read

        try:
            remaining = max(0.05, time_end - time.perf_counter())
            sock.settimeout(remaining)
            chunk = sock.recv(BUFFER_SIZE)
            if not chunk:
                # EOF：文件下载完成
                if resp_headers.get("content-length") == "-1":
                    # 未知大小，直接退出（与 Go contentLength==-1 分支一致）
                    break
                # 补算最后一个时间片（与 Go EOF 分支一致）
                now = time.perf_counter()
                last_slice_start = time_start + time_slice * (time_counter - 1)
                fraction = (now - last_slice_start) / time_slice if time_slice > 0 else 1.0
                fraction = max(fraction, 1e-9)
                ewma.add((content_read - last_read) / fraction)
                break
            content_read += len(chunk)
        except socket.timeout:
            break
        except Exception as e:
            if debug:
                print(_red(f"[调试] IP: {ip}, 下载测速失败，错误信息: {e}, "
                           f"下载测速地址: {url}"))
            break

    try:
        sock.close()
    except Exception:
        pass

    # 最终速度公式与 Go 完全一致：ewma_val / (timeout / 120)
    speed = ewma.value / (timeout_s / 120) if timeout_s > 0 else 0.0
    return speed, colo


def _print_dl_debug(ip: str, url: str, last_redirect: str,
                    err: Exception = None, status: int = 0):
    """统一的下载调试输出（对应 Go 版 printDownloadDebugInfo）。"""
    final_url = last_redirect if last_redirect else url
    if url != final_url:
        if status > 0:
            print(_red(f"[调试] IP: {ip}, 下载测速终止，HTTP 状态码: {status}, "
                       f"下载测速地址: {url}, 出错的重定向后地址: {final_url}"))
        else:
            print(_red(f"[调试] IP: {ip}, 下载测速失败，错误信息: {err}, "
                       f"下载测速地址: {url}, 出错的重定向后地址: {final_url}"))
    else:
        if status > 0:
            print(_red(f"[调试] IP: {ip}, 下载测速终止，HTTP 状态码: {status}, "
                       f"下载测速地址: {url}"))
        else:
            print(_red(f"[调试] IP: {ip}, 下载测速失败，错误信息: {err}, "
                       f"下载测速地址: {url}"))


# ──────────────────────────────────────────────
# 下载测速调度
# ──────────────────────────────────────────────
def run_download(
    results:      List[IPResult],
    url:          str,
    port:         int,
    timeout_s:    float,
    test_count:   int,
    min_speed:    float,       # MB/s
    debug:        bool,
) -> List[IPResult]:
    if not results:
        print(_yellow("[信息] 延迟测速结果 IP 数量为 0，跳过下载测速。"))
        return []

    min_speed_bytes = min_speed * 1024 * 1024

    # FIX: 复现 Go 版 testNum 计算逻辑（原代码逻辑相反导致 min_speed>0 时不测全部）
    # Go: testNum 默认=TestCount；当 len<TestCount 或 MinSpeed>0 时 testNum=len(ipSet)
    test_num = test_count
    if len(results) < test_count or min_speed > 0:
        test_num = len(results)
    # 若 test_num < test_count，修正 effective_count
    effective_count = min(test_count, test_num)

    print(_cyan(f"开始下载测速（下限：{min_speed:.2f} MB/s, 数量：{effective_count}, 队列：{test_num}）"))
    bar = Bar(effective_count, "     ", "")

    speed_set: List[IPResult] = []

    for i in range(test_num):
        r = results[i]
        speed, colo = _download_once(r.ping.ip, url, port, timeout_s, debug)
        r.download_speed = speed
        if r.ping.colo == "":
            r.ping.colo = colo

        if speed >= min_speed_bytes:
            bar.grow(1, "")
            speed_set.append(r)
            if len(speed_set) == effective_count:
                break

    bar.done()

    if min_speed == 0.0:
        # 不过滤，返回全部已测速结果
        final = results[:test_num]
    elif debug and len(speed_set) == 0:
        print(_yellow("[调试] 没有满足 下载速度下限 条件的 IP，"
                      "忽略条件返回所有测速数据（方便下次测速时调整条件）。"))
        final = results[:test_num]
    else:
        final = speed_set

    # 按下载速度降序排序
    final.sort(key=lambda x: x.download_speed, reverse=True)
    return final


# ──────────────────────────────────────────────
# CSV 导出
# ──────────────────────────────────────────────
def export_csv(data: List[IPResult], output: str):
    if not output or output.strip() == "":
        return
    if not data:
        return
    try:
        with open(output, "w", newline="", encoding="utf-8-sig") as f:
            writer = csv.writer(f)
            writer.writerow(["IP 地址", "已发送", "已接收", "丢包率", "平均延迟", "下载速度(MB/s)", "地区码"])
            for r in data:
                p = r.ping
                colo = p.colo if p.colo else "N/A"
                writer.writerow([
                    p.ip,
                    p.sent,
                    p.received,
                    f"{p.loss_rate:.2f}",
                    f"{p.delay_ms:.2f}",
                    f"{r.download_speed / 1024 / 1024:.2f}",
                    colo,
                ])
    except Exception as e:
        print(_red(f"[错误] 写入文件 [{output}] 失败：{e}"))


# ──────────────────────────────────────────────
# 结果打印
# ──────────────────────────────────────────────
def print_results(data: List[IPResult], print_num: int, output: str):
    if print_num == 0:
        return
    if not data:
        print("\n[信息] 完整测速结果 IP 数量为 0，跳过输出结果。")
        return

    n = min(print_num, len(data))
    # 检测是否有 IPv6
    has_v6 = any(":" in data[i].ping.ip for i in range(n))

    if has_v6:
        head_fmt = "{:<40}{:<8}{:<8}{:<8}{:<10}{:<16}{:<8}"
        data_fmt = "{:<42}{:<8}{:<8}{:<8}{:<10}{:<16}{:<8}"
    else:
        head_fmt = "{:<16}{:<8}{:<8}{:<8}{:<10}{:<16}{:<8}"
        data_fmt = "{:<18}{:<8}{:<8}{:<8}{:<10}{:<16}{:<8}"

    print()
    print(_cyan(head_fmt.format("IP 地址", "已发送", "已接收", "丢包率", "平均延迟", "下载速度(MB/s)", "地区码")))
    for i in range(n):
        r = data[i]
        p = r.ping
        colo = p.colo if p.colo else "N/A"
        print(data_fmt.format(
            p.ip,
            p.sent,
            p.received,
            f"{p.loss_rate:.2f}",
            f"{p.delay_ms:.2f}",
            f"{r.download_speed / 1024 / 1024:.2f}",
            colo,
        ))

    if output and output.strip():
        print(f"\n完整测速结果已写入 {output} 文件，可使用记事本/表格软件查看。")


# ──────────────────────────────────────────────
# 版本检查
# ──────────────────────────────────────────────
VERSION = "v1.0.0-py"

def check_update():
    try:
        req = urllib.request.Request(
            "https://api.xiu2.xyz/ver/cloudflarespeedtest.txt",
            headers={"User-Agent": "cfst-python"}
        )
        with urllib.request.urlopen(req, timeout=10) as resp:
            body = resp.read().decode().strip()
        if body and body != VERSION:
            print(_yellow(f"*** 发现新版本 [{body}]！请前往 [https://github.com/XIU2/CloudflareSpeedTest] 更新！ ***"))
        else:
            print(_green(f"当前为最新版本 [{VERSION}]！"))
    except Exception:
        pass


# ──────────────────────────────────────────────
# CLI 参数定义
# ──────────────────────────────────────────────
def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="cfst.py",
        description=f"CloudflareSpeedTest Python 移植版 {VERSION}\n"
                    "测试各个 CDN 或网站所有 IP 的延迟和速度，获取最快 IP (IPv4+IPv6)！\n"
                    "https://github.com/XIU2/CloudflareSpeedTest",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        add_help=False,
    )
    p.add_argument("-n",  type=int,   default=200,                        metavar="200",   help="延迟测速线程数（默认 200，最多 1000）")
    p.add_argument("-t",  type=int,   default=4,                          metavar="4",     help="延迟测速次数（默认 4）")
    p.add_argument("-dn", type=int,   default=10,                         metavar="10",    help="下载测速数量（默认 10）")
    p.add_argument("-dt", type=int,   default=10,                         metavar="10",    help="下载测速时间，秒（默认 10）")
    p.add_argument("-tp", type=int,   default=443,                        metavar="443",   help="指定测速端口（默认 443）")
    p.add_argument("-url",type=str,   default="https://cf.xiu2.xyz/url",  metavar="URL",   help="指定测速地址")

    p.add_argument("-httping",      action="store_true",                                   help="切换为 HTTP 延迟测速模式（默认 TCPing）")
    p.add_argument("-httping-code", type=int, default=0, dest="httping_code", metavar="200", help="HTTPing 有效 HTTP 状态码（默认 200/301/302）")
    p.add_argument("-cfcolo",       type=str, default="",                  metavar="HKG",   help="匹配指定地区（IATA/国家/城市码，逗号分隔，仅 HTTPing 可用）")

    p.add_argument("-tl",  type=float, default=9999, metavar="200",    help="平均延迟上限 ms（默认 9999）")
    p.add_argument("-tll", type=float, default=0,    metavar="40",     help="平均延迟下限 ms（默认 0）")
    p.add_argument("-tlr", type=float, default=1.0,  metavar="0.2",   help="丢包率上限（0.00~1.00，默认 1.00）")
    p.add_argument("-sl",  type=float, default=0.0,  metavar="5",     help="下载速度下限 MB/s（默认 0.00）")

    p.add_argument("-p",  type=int,   default=10,           metavar="10",         help="显示结果数量（0=不显示）")
    p.add_argument("-f",  type=str,   default="ip.txt",     metavar="ip.txt",     help="IP 段数据文件（默认 ip.txt）")
    p.add_argument("-ip", type=str,   default="",           metavar="1.1.1.1",   dest="ip_text", help="直接指定 IP 段（逗号分隔）")
    p.add_argument("-o",  type=str,   default="result.csv", metavar="result.csv", help="输出文件（空字符串禁用）")

    p.add_argument("-dd",    action="store_true",  help="禁用下载测速（结果按延迟排序）")
    p.add_argument("-allip", action="store_true",  help="测速 IP 段内全部 IP（仅 IPv4）")

    p.add_argument("-debug", action="store_true",  help="调试输出模式")
    p.add_argument("-v",     action="store_true",  help="打印版本并检查更新")
    p.add_argument("-h",     action="help",        help="打印帮助说明")
    return p


# ──────────────────────────────────────────────
# 主入口
# ──────────────────────────────────────────────
def main():
    random.seed(time.time())

    parser = build_parser()
    args   = parser.parse_args()

    # ── 版本检查 ──
    if args.v:
        print(VERSION)
        print("检查版本更新中...")
        check_update()
        sys.exit(0)

    # ── 参数校验 ──
    platform_max = _platform_max_routines()
    routines     = max(1, min(args.n, platform_max))
    if routines < args.n:
        print(_yellow(f"[提示] 当前平台线程数上限为 {platform_max}，"
                      f"-n 已自动调整为 {routines}（原设定 {args.n}）"))
    port       = args.tp if 0 < args.tp < 65535 else 443
    ping_times = max(1, args.t)
    dl_time    = max(1, args.dt)
    test_count = max(1, args.dn)

    colo_filter: Optional[set] = None
    if args.cfcolo:
        colo_filter = set(c.strip().upper() for c in args.cfcolo.split(",") if c.strip())

    valid_codes: List[int] = []
    if args.httping_code and 100 <= args.httping_code <= 599:
        valid_codes = [args.httping_code]

    if args.sl > 0 and args.tl == 9999:
        print(_yellow("[提示] 在使用 [-sl] 参数时，建议搭配 [-tl] 参数，以避免因凑不够 [-dn] 数量而一直测速..."))

    print(f"# XIU2/CloudflareSpeedTest Python 移植版 {VERSION}\n")

    # ── 加载 IP ──
    ips = load_ip_ranges(args.f, args.ip_text, args.allip)
    if not ips:
        sys.exit("[错误] 没有找到任何 IP，请检查 IP 数据文件或 -ip 参数。")

    # ── 延迟测速 ──
    ping_results = run_ping(
        ips           = ips,
        port          = port,
        ping_times    = ping_times,
        routines      = routines,
        httping       = args.httping,
        url           = args.url,
        valid_codes   = valid_codes,
        colo_filter   = colo_filter,
        debug         = args.debug,
        min_delay_ms  = args.tll,   # FIX: 传入实际参数
        max_delay_ms  = args.tl,
        max_loss_rate = args.tlr,
    )

    # ── 过滤 ──
    filtered = filter_delay(ping_results, args.tll, args.tl)
    filtered = filter_loss_rate(filtered, args.tlr)

    # ── 下载测速 ──
    if args.dd:
        # FIX: 禁用下载时返回全部过滤结果（原代码错误截断为 test_count 条）
        final = filtered
    else:
        final = run_download(
            results    = filtered,
            url        = args.url,
            port       = port,
            timeout_s  = float(dl_time),
            test_count = test_count,
            min_speed  = args.sl,
            debug      = args.debug,
        )

    # ── 输出 ──
    export_csv(final, args.o)
    print_results(final, args.p, args.o)

    # Windows 下等待回车（仅在直接运行时）
    if sys.platform == "win32" and args.p != 0 and final:
        input("\n按下 回车键 或 Ctrl+C 退出。")


if __name__ == "__main__":
    main()