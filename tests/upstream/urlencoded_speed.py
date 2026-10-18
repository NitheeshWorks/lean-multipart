"""Reference timings for the urlencoded bench (tests/Bench.lean, qs* cases):
python-multipart's QuerystringParser on `a=<value>`, collecting the raw field
as Starlette's FormParser does, then Starlette's
`unquote_plus(raw.decode("latin-1"))`. Values: plain (`x`), escaped (`%41`),
mixed (`ab+c%20` repeated), of 1, 10 and 50 MiB.

  stack-tools/capped upstream-spec/.venv/bin/python -I tests/upstream/urlencoded_speed.py
"""
import time
from urllib.parse import unquote_plus
from python_multipart.multipart import QuerystringParser

MIB = 1024 * 1024
def body(kind, n):
    unit = {"plain": b"x", "escaped": b"%41", "mixed": b"ab+c%20"}[kind]
    return b"a=" + (unit * (n // len(unit) + 1))[:n]

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
        print(f"qs-{kind}-{mib} ms={(t1 - t0) * 1000:.0f} out={len(out[0][1])}")
