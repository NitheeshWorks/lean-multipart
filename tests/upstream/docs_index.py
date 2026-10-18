"""Reference output for examples/docs/Index.lean.

Runs the Python blocks of python-multipart's docs/index.md, read from the
upstream checkout (nothing is copied), with wsgiref's server stubbed out,
and replays the page's curl sessions in-process, printing each response in
the format `lake exe docs-index` prints. Run with the upstream venv:

  upstream-spec/.venv/bin/python -I tests/upstream/docs_index.py
"""
import io, re, sys, wsgiref.simple_server

UP = "/home/nitheesh/Official/NitheeshWorks/upstream-spec/python-multipart/docs/index.md"
blocks = re.findall(r"```python\n(.*?)```", open(UP).read(), re.S)

class _Stub:
    def serve_forever(self): pass
wsgiref.simple_server.make_server = lambda host, port, app: _Stub()

def app_of(block):
    ns = {"print": lambda *a, **k: None}
    exec(block, ns)
    return ns["simple_app"]

def curl_form(boundary, parts):
    body = "".join(f"--{boundary}\r\n{p}" for p in parts) + f"--{boundary}--\r\n"
    return {"CONTENT_TYPE": f"multipart/form-data; boundary={boundary}",
            "CONTENT_LENGTH": str(len(body.encode()))}, body.encode()

def call(app, env, body):
    env = dict(env, **{"wsgi.input": io.BytesIO(body)})
    started = {}
    def start_response(status, headers): started.update(status=status, headers=headers)
    pieces = app(env, start_response)
    out = b"".join(p if isinstance(p, bytes) else p.encode() for p in pieces)
    return started["status"], started["headers"], out

def show(title, reply):
    status, headers, body = reply
    w = sys.stdout.buffer
    w.write(f"== {title} ==\n{status}\n".encode())
    for k, v in headers: w.write(f"{k}: {v}\n".encode())
    w.write(b"\n" + body + b"\n")

env, body = curl_form("------------------------c2ef3ebd0a8a1a63",
    ['Content-Disposition: form-data; name="foo"\r\n\r\nbar\r\n'])
show("simple: curl -F foo=bar", call(app_of(blocks[0]), env, body))
show("in-depth start: curl", call(app_of(blocks[1]), {}, b""))
env, body = curl_form("------------------------8f2c63b9d2c1e7a4",
    ['Content-Disposition: form-data; name="file"; filename="test.txt"\r\nContent-Type: text/plain\r\n\r\nFoo bar\n\r\n'])
show("in-depth: curl -F file=@/tmp/test.txt", call(app_of(blocks[2]), env, body))
