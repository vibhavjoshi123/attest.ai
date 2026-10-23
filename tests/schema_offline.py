"""A schema model without a TypeDB server.

The type bridge parses the canonical text TypeDB's `type_schema()` returns.
Offline tests need a model for the fixture domain in `tests/fixtures/`, so
this turns `.tql` source (core plus a domain) into that canonical shape:
comments and functions dropped, one clause per line, `sub` on its own line,
a relation's roles in name order — which is how TypeDB prints them, and role
order is field order in the generated Lean types.

Test infrastructure only; the live path never uses it. Its output was checked
byte for byte against Lean modules generated from a real server's schema
before it was used to generate the fixture package here, so the fixture is
what `sync` would have written.
"""

from __future__ import annotations

import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
CORE = ROOT / "attest" / "core.tql"


def _strip_comments(text: str) -> str:
    out = []
    for line in text.splitlines():
        buf, quoted = [], False
        for ch in line:
            if ch == '"':
                quoted = not quoted
            elif ch == "#" and not quoted:
                break
            buf.append(ch)
        out.append("".join(buf))
    return "\n".join(out)


def _split_top(text: str, sep: str) -> list[str]:
    """Split on `sep` outside quotes, parentheses and braces."""
    parts, buf, depth, quoted = [], [], 0, False
    for ch in text:
        if ch == '"':
            quoted = not quoted
        elif not quoted and ch in "({":
            depth += 1
        elif not quoted and ch in ")}":
            depth -= 1
        if ch == sep and not quoted and depth == 0:
            parts.append("".join(buf))
            buf = []
            continue
        buf.append(ch)
    parts.append("".join(buf))
    return parts


def _statements(text: str) -> list[str]:
    """Top-level statements, with `fun` definitions removed whole."""
    text = re.sub(r"^\s*define\b", "", text.strip())
    out, i = [], 0
    while i < len(text):
        rest = text[i:].lstrip()
        if not rest:
            break
        i = len(text) - len(rest)
        if re.match(r"fun\s", rest):
            # a function body has its own `;`s; it ends after `return …;`
            m = re.search(r"\breturn\b[^;]*;", rest, re.S)
            i += m.end()
            continue
        if re.match(r"define\b", rest):
            i += len("define")
            continue
        stmt = _split_top(rest, ";")[0]
        out.append(stmt.strip())
        i += len(stmt) + 1
    return [s for s in out if s]


def canonical(*paths: pathlib.Path) -> str:
    """Canonical schema text for core.tql plus the given domain schemas."""
    lines = ["define"]
    for path in (CORE, *paths):
        for stmt in _statements(_strip_comments(path.read_text())):
            # one clause per line, as TypeDB prints it: a clause written
            # over several lines (a long `@values(…)`) is joined back up
            clauses = [" ".join(c.split()) for c in _split_top(stmt, ",")
                       if c.strip()]
            head = clauses[0].split()
            if len(head) >= 4 and head[2] == "sub":
                clauses = [" ".join(head[:2] + head[4:]),
                           f"sub {head[3]}", *clauses[1:]]
            # TypeDB prints a relation's roles in name order, not source
            # order, and role order is field order in the generated types
            relates = sorted((c for c in clauses[1:]
                              if c.startswith("relates ")),
                             key=lambda c: c.split()[1])
            it = iter(relates)
            clauses = [clauses[0]] + [next(it) if c.startswith("relates ")
                                      else c for c in clauses[1:]]
            body = [f"  {c}" for c in clauses[1:]]
            lines.append(",\n".join([clauses[0], *body]) + ";")
    return "\n".join(lines) + "\n"


def model(*paths: pathlib.Path):
    from attest import typebridge
    return typebridge.parse(canonical(*paths))
