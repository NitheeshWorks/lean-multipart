"""Golden cases for Starlette's field decoding, `unquote_plus(raw.decode("latin-1"))`
(LeanMultipart.unquotePlusLatin1). Writes tests/upstream/unquote_golden.txt:
one line per case, `<raw hex> <hex of the result's UTF-8>`. Seeded, so the
file is reproducible:

  upstream-spec/.venv/bin/python -I tests/upstream/unquote_golden.py
"""
import random
from pathlib import Path
from urllib.parse import unquote_plus

rng = random.Random(20261018)
pieces = [b"%", b"+", b"a", b"Z", b"0", b"9", b"f", b"F", b"g", b"%2", b"%4", b"%41", b"%e9", b"%C3%A9",
          b"%E2%82%AC", b"%F0%9F%98%80", b"%C3", b"%E2%82", b"%F0%9F", b"%ED%A0%80", b"%C0%AF", b"%F4%90%80%80",
          b"%80", b"%BF", b"%FF", b"%%", b"%+", b"%2+", b"\xe9", b"\xff", b"\x80", b" ", b"&", b"=", b"%0a", b"%00"]
cases = [b"", b"+", b"%", b"%4", b"%41", b"abc", b"\xe9", b"%C3%A9", b"%C3", b"%C3a", b"%C3\xe9", b"%E2%82%AC%"]
for _ in range(600):
    cases.append(b"".join(rng.choice(pieces) for _ in range(rng.randint(1, 12))))
for _ in range(200):
    cases.append(bytes(rng.randrange(256) for _ in range(rng.randint(1, 16))))
out = Path(__file__).with_name("unquote_golden.txt")
out.write_text("".join(f"{c.hex()} {unquote_plus(c.decode('latin-1')).encode('utf-8').hex()}\n" for c in cases))
print(f"{len(cases)} cases -> {out}")
