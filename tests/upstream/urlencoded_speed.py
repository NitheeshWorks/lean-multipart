"""Reference timings for the urlencoded bench (tests/Bench.lean, qs* and name* cases):
python-multipart's QuerystringParser on `a=<value>`, collecting the raw field
as Starlette's FormParser does, then Starlette's
`unquote_plus(raw.decode("latin-1"))`. Values: plain (`x`), escaped (`%41`),
mixed (`ab+c%20` repeated), of 1, 10 and 50 MiB. Then fields without `%`, the
common form a browser sends: values of `hello+world` (a space as `+`) and of
raw UTF-8 `café`, and names of `hello+café`, each of 1 and 10 MiB.

  stack-tools/capped upstream-spec/.venv/bin/python -I tests/upstream/urlencoded_speed.py
"""
import time
from urllib.parse import unquote_plus
from python_multipart.multipart import QuerystringParser

MIB = 1024 * 1024
def body(kind, n):
    unit = {"plain": b"x", "escaped": b"%41", "mixed": b"ab+c%20"}[kind]
    return b"a=" + (unit * (n // len(unit) + 1))[:n]

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

# Plain field names of 1, 2 and 4 MiB (`xxxx...x=1`).
for mib in [1, 2, 4]:
    b = b"x" * (mib * MIB) + b"=1"
    t0 = time.perf_counter(); out = parse(b); t1 = time.perf_counter()
    print(f"name-{mib} ms={(t1 - t0) * 1000:.1f} out={len(out[0][0])}")

# Starlette 1.8.0 refusing a 1 MiB + 1 name at its default limits.
import asyncio
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
b = b"x" * (MIB + 1) + b"=1"
t0 = time.perf_counter(); r = asyncio.run(refuse(b)); t1 = time.perf_counter()
print(f"name-over ms={(t1 - t0) * 1000:.1f} {r}")

for kind in ["plain", "escaped", "mixed"]:
    for mib in [1, 10, 50]:
        b = body(kind, mib * MIB)
        t0 = time.perf_counter()
        fields, name, value = [], [], []
        def on_field_name(d, s, e): name.append(d[s:e])
        def on_field_data(d, s, e): value.append(d[s:e])
        def on_field_end():
            fields.append((b"".join(name), b"".join(value))); name.clear(); value.clear()
        p = QuerystringParser({"on_field_name": on_field_name, "on_field_data": on_field_data, "on_field_end": on_field_end})
        for i in range(0, len(b), 65536): p.write(b[i:i + 65536])
        p.finalize()
        out = [(unquote_plus(k.decode("latin-1")), unquote_plus(v.decode("latin-1"))) for k, v in fields]
        t1 = time.perf_counter()
        print(f"qs-{kind}-{mib} ms={(t1 - t0) * 1000:.1f} out={len(out[0][1])}")

units = {"plus": b"hello+world", "latin": "café".encode()}
for kind in ["plus", "latin"]:
    for mib in [1, 10]:
        b = b"a=" + (units[kind] * (mib * MIB // len(units[kind]) + 1))[:mib * MIB]
        t0 = time.perf_counter(); out = parse(b); t1 = time.perf_counter()
        print(f"qs-{kind}-{mib} ms={(t1 - t0) * 1000:.1f} out={len(out[0][1])}")
unit = "hello+café".encode()
for mib in [1, 10]:
    b = (unit * (mib * MIB // len(unit) + 1))[:mib * MIB] + b"=1"
    t0 = time.perf_counter(); out = parse(b); t1 = time.perf_counter()
    print(f"name-plus-{mib} ms={(t1 - t0) * 1000:.1f} out={len(out[0][0])}")
