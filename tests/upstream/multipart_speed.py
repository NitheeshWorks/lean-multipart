"""Reference timings for the streamed multipart bench (tests/Bench.lean, `st-*`
cases): python-multipart's MultipartParser fed the body in 64 KiB chunks, as
Starlette's MultiPartParser feeds it from the request stream, with callbacks
that do what Starlette's do with the bytes: header names and values are
joined, each part-data piece is kept (Starlette appends a field's pieces and
hands a file's pieces to its spool), and a part is closed at `on_part_end`.

The bodies are those of tests/Bench.lean:

  mp50       one 50 MiB field part of `x`
  mpMany     a million empty field parts
  file50     one 50 MiB file part of `x`
  fileBin50  one 50 MiB file part of pseudo-random bytes (xorshift, as the bench)
  nearMiss50 a 50 MiB file part of `CR LF --boundar x` repeated: every 13 bytes a
             delimiter that fails on its last byte
  crlf50     a 50 MiB file part of `CR LF` repeated

Each time is the best of 5 warm runs, on one of the machine's fastest cores, as
scripts/bench.sh runs the bench; the bounds in tests/Bench.lean take, per row,
the least of three invocations (best of 15):

  stack-tools/capped taskset -c <core> upstream-spec/.venv/bin/python -I tests/upstream/multipart_speed.py
"""
import time
from python_multipart.multipart import MultipartParser

MIB = 1024 * 1024
N = 5
CHUNK = 65536
HEAD = b"--boundary\r\nContent-Disposition: form-data; name=\"f\"\r\n\r\n"
HEADF = b"--boundary\r\nContent-Disposition: form-data; name=\"f\"; filename=\"a\"\r\n\r\n"
TAIL = b"\r\n--boundary--\r\n"


def xorshift(n):
    out = bytearray(n)
    x = 88172645463325252
    m = (1 << 64) - 1
    for i in range(n):
        x ^= (x << 13) & m
        x ^= x >> 7
        x ^= (x << 17) & m
        out[i] = (x >> 24) & 0xFF
    return bytes(out)


def rep(unit, n):
    return (unit * (n // len(unit) + 1))[:n]


def parse(body):
    parts, pieces, hname, hvalue, headers = [], [], [], [], []
    total = [0]

    def on_part_begin():
        pieces.clear(); headers.clear()

    def on_header_field(d, s, e): hname.append(d[s:e])
    def on_header_value(d, s, e): hvalue.append(d[s:e])

    def on_header_end():
        headers.append((b"".join(hname).lower(), b"".join(hvalue))); hname.clear(); hvalue.clear()

    def on_part_data(d, s, e):
        b = d[s:e]; pieces.append(b); total[0] += len(b)

    def on_part_end():
        parts.append(len(headers))

    p = MultipartParser(b"boundary", {"on_part_begin": on_part_begin, "on_header_field": on_header_field,
                                      "on_header_value": on_header_value, "on_header_end": on_header_end,
                                      "on_part_data": on_part_data, "on_part_end": on_part_end})
    for i in range(0, len(body), CHUNK):
        p.write(body[i:i + CHUNK])
    p.finalize()
    return len(parts), total[0]


def best(body):
    ts = []
    for _ in range(N):
        t0 = time.perf_counter(); out = parse(body); t1 = time.perf_counter()
        ts.append(t1 - t0)
    return min(ts) * 1000, out


BODIES = {
    "mp50": lambda: HEAD + b"x" * (50 * MIB) + TAIL,
    "mpMany": lambda: (HEAD.replace(b'"f"', b'"x"') + b"\r\n") * 1000000 + b"--boundary--\r\n",
    "file50": lambda: HEADF + b"x" * (50 * MIB) + TAIL,
    "fileBin50": lambda: HEADF + xorshift(50 * MIB) + TAIL,
    "nearMiss50": lambda: HEADF + rep(b"\r\n--boundarx", 50 * MIB) + TAIL,
    "crlf50": lambda: HEADF + rep(b"\r\n", 50 * MIB) + TAIL,
}

for name, mk in BODIES.items():
    body = mk()
    ms, out = best(body)
    print(f"st-{name} ms={ms:.2f} parts={out[0]} data={out[1]}")
