"""Reference outcomes for the IO objects' error paths (tests/Conformance.lean,
"parse_form errors" and "MultipartParser.create"). One line per case:
name|outcome|class|message|callbacks. Run with the upstream venv:

  upstream-spec/.venv/bin/python -I tests/upstream/io_errors.py
"""
import io, python_multipart
from python_multipart.multipart import MultipartParser

URL = "application/x-www-form-urlencoded"
def form(name, headers, body, chunk_size=1048576):
    got = []
    try:
        python_multipart.parse_form(headers, io.BytesIO(body),
            lambda f: got.append(f.field_name.decode()), lambda f: got.append(f.field_name.decode()),
            chunk_size=chunk_size)
        print(f"{name}|ok|||{','.join(got)}")
    except Exception as e:
        print(f"{name}|raise|{type(e).__name__}|{e}|{','.join(got)}")

mp = b'--B\r\nContent-Disposition: form-data; name="a"\r\n\r\nx\r\n--B\r\nBad Header: y\r\n\r\nz\r\n--B--\r\n'
form("bad header after a field", {"Content-Type": "multipart/form-data; boundary=B"}, mp)
for cl in ["-1", "x", "+3", " 3 ", "3_0", "1__0", "_3", "3_", "-0", "", "\t3\n"]:
    form(f"Content-Length {cl!r}", {"Content-Type": URL, "Content-Length": cl.encode()}, b"a=b&c=d" * 5)
form("chunk_size 0", {"Content-Type": URL}, b"a=b", chunk_size=0)
form("no boundary", {"Content-Type": "multipart/form-data"}, b"")
form("no Content-Type", {}, b"")

for name, b in [("create None", None), ("create b''", b""), ("create b'B'", b"B")]:
    try:
        p = MultipartParser(b, {})
        try:
            p.write(b"--B\r\nBad Header: y\r\n\r\nz\r\n--B--\r\n")
            print(f"{name}|ok|||")
        except Exception as e:
            print(f"{name}|raise at write|{type(e).__name__}|{e}|")
    except Exception as e:
        print(f"{name}|raise at create|{type(e).__name__}|{e}|")
