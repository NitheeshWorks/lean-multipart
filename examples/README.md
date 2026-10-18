# Examples

A 1:1 port of python-multipart's own examples. The project ships no example
programs, so its examples are the Python code blocks of its documentation;
only `docs/index.md` has any. `MANIFEST.toml` maps each block to its port.

In upstream's order:

| Upstream | Lean | What it shows |
|---|---|---|
| `docs/index.md`, Quickstart, "Simple Example" | [`docs/Index.lean`](docs/Index.lean), `SimpleExample` | `parseFormStream headers environ.wsgiInput onField onFile` in a WSGI app |
| `docs/index.md`, "In-Depth Example", first code | [`docs/Index.lean`](docs/Index.lean), `InDepthStart` | the bare WSGI app |
| `docs/index.md`, "In-Depth Example", final code | [`docs/Index.lean`](docs/Index.lean), `InDepth` | `parseOptionsHeader`, `MultipartParser.create boundary callbacks`, `parser.write`, streaming each part into SHA-256 |

Run them:

```
lake exe docs-index                     # replay the page's curl sessions, print the responses
lake exe docs-index serve simple        # serve a block on port 8123, as upstream does
lake exe docs-index serve start
lake exe docs-index serve in-depth      # then: curl -ik -F file=@/tmp/test.txt http://localhost:8123/
```

The printed output is checked against upstream's (python-multipart 0.0.32,
`tests/upstream/docs_index.py`) by the conformance case
"example docs/index.md output matches upstream".

`support/` stands in for the Python standard library the examples import:
`Hashlib.lean` (`hashlib.sha256`) and `Wsgiref.lean` (`wsgiref.simple_server`
on `Std.Http`, and `wsgiref.validate.validator`). They are helpers, not ports.
