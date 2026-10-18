"""Reference timings for the urlencoded bench (tests/Bench.lean, qs* and name* cases):
python-multipart's QuerystringParser on the body, collecting the raw fields
as Starlette's FormParser does, then Starlette's
`unquote_plus(raw.decode("latin-1"))`.

Values (`a=<value>`): plain (`x`), escaped (`%41`), mixed (`ab+c%20`
repeated), of 1, 10 and 50 MiB; then fields without `%`, the common form a
browser sends: values of `hello+world` (a space as `+`) and of raw UTF-8
`café`, of 1 and 10 MiB. Names (`<name>=1`): plain (`x`) of 1, 2 and 4 MiB,
`hello+world` of 1 and 2 MiB, `hello+café` of 1 and 10 MiB. And Starlette
1.8.0 refusing a 1 MiB + 1 name at its default limits.

Each time is the best of 5 warm runs, on one of the machine's fastest cores, as
scripts/bench.sh runs the bench; the bounds in tests/Bench.lean take, per row,
the least of three invocations (best of 15), against the bench's best of up to
31:

  stack-tools/capped taskset -c <core> upstream-spec/.venv/bin/python -I tests/upstream/urlencoded_speed.py
"""
import asyncio
import time
from urllib.parse import unquote_plus
from python_multipart.multipart import QuerystringParser

MIB = 1024 * 1024
N = 5


def best(f, b):
    ts = []
    for _ in range(N):
        t0 = time.perf_counter(); out = f(b); t1 = time.perf_counter()
        ts.append(t1 - t0)
    return min(ts) * 1000, out


def parse(b):
    fields, name, value = [], [], []
    def on_field_name(d, s, e): name.append(d[s:e])
    def on_field_data(d, s, e): value.append(d[s:e])
    def on_field_end():
        fields.append((b"".join(name), b"".join(value))); name.clear(); value.clear()
    p = QuerystringParser({"on_field_name": on_field_name, "on_field_data": on_field_data, "on_field_end": on_field_end})
    for i in range(0, len(b), 65536): p.write(b[i:i + 65536])
    p.finalize()
    return [(unquote_plus(k.decode("latin-1")), unquote_plus(v.decode("latin-1"))) for k, v in fields]


def rep(unit, n):
    return (unit * (n // len(unit) + 1))[:n]


UNITS = {"plain": b"x", "escaped": b"%41", "mixed": b"ab+c%20", "plus": b"hello+world", "latin": "café".encode(),
         "fox": b"the+quick+brown+fox+jumps+over+the+lazy+dog+", "iam": b"I+am+a+man+"}

for kind, sizes in [("plain", [1, 10, 50]), ("escaped", [1, 10, 50]), ("mixed", [1, 10, 50]),
                    ("plus", [1, 10]), ("latin", [1, 10]), ("fox", [1, 10]), ("iam", [1, 10])]:
    for mib in sizes:
        ms, out = best(parse, b"a=" + rep(UNITS[kind], mib * MIB))
        print(f"qs-{kind}-{mib} ms={ms:.2f} out={len(out[0][1])}")

for row, unit, sizes in [("name", b"x", [1, 2, 4]), ("name-pw", b"hello+world", [1, 2]),
                         ("name-fox", UNITS["fox"], [1, 2]), ("name-a", b"a+", [1, 2]),
                         ("name-plus", "hello+café".encode(), [1, 10])]:
    for mib in sizes:
        ms, out = best(parse, rep(unit, mib * MIB) + b"=1")
        print(f"{row}-{mib} ms={ms:.2f} out={len(out[0][0])}")

from starlette.datastructures import Headers
from starlette.formparsers import FormParser, MultiPartException


async def refuse(b):
    async def stream():
        for i in range(0, len(b), 65536): yield b[i:i + 65536]
        yield b""
    try:
        await FormParser(Headers({"content-type": "application/x-www-form-urlencoded"}), stream()).parse()
        return "accepted"
    except MultiPartException as e:
        return str(e)

ms, r = best(lambda b: asyncio.run(refuse(b)), b"x" * (MIB + 1) + b"=1")
print(f"name-over ms={ms:.2f} {r}")
