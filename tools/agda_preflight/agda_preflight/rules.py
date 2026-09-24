from __future__ import annotations
from dataclasses import dataclass
import re
from typing import Dict, Iterable, List, Optional, Tuple

_IDENT = r"[A-Za-z_][A-Za-z0-9_'\u2080-\u2089]*"

@dataclass
class Constructor:
    name: str
    datatype: str
    type_text: str
    line: int
    arity: int

@dataclass
class DataDecl:
    name: str
    line: int
    constructors: Dict[str, Constructor]
    indexed: bool = False

def _line_col(source: str, offset: int) -> Tuple[int, int]:
    line = source.count("\n", 0, offset) + 1
    prev = source.rfind("\n", 0, offset)
    return line, offset - prev

def _strip_comments(source: str) -> str:
    return re.sub(r"--[^\n]*", "", source)

def _split_arrows(text: str) -> List[str]:
    out, buf, depth = [], [], 0
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth = max(0, depth - 1)
        if depth == 0 and ch == "→":
            out.append("".join(buf).strip()); buf = []
        elif depth == 0 and text.startswith("->", i):
            out.append("".join(buf).strip()); buf = []; i += 1
        else:
            buf.append(ch)
        i += 1
    out.append("".join(buf).strip())
    return out

def _arity(text: str) -> int:
    parts = _split_arrows(text)
    return sum(1 for d in parts[:-1] if not d.strip().startswith("{"))

def _terminal(text: str) -> Optional[str]:
    parts = _split_arrows(text)
    if not parts:
        return None
    tail = parts[-1].strip().strip("()")
    m = re.match(r"([A-Za-z_][A-Za-z0-9_.'₀-₉ω]*|[⊤⊥])", tail)
    return m.group(1) if m else None

def _collect_data(source: str):
    lines = source.splitlines()
    data, ctors = {}, {}
    i = 0
    while i < len(lines):
        m = re.match(rf"^data\s+({_IDENT})\b(.*?)\s*:\s*(.*?)\s+where\s*$", lines[i])
        if not m:
            i += 1; continue
        name, result = m.group(1), m.group(3)
        d = DataDecl(name, i + 1, {}, "→" in result or "->" in result)
        j = i + 1
        while j < len(lines):
            line = lines[j]
            if line and not line[0].isspace():
                break
            cm = re.match(rf"^\s+({_IDENT})\s*:\s*(.*)$", line)
            if cm:
                cname = cm.group(1); parts = [cm.group(2).strip()]; k = j + 1
                while k < len(lines):
                    nxt = lines[k]
                    if nxt and not nxt[0].isspace(): break
                    if re.match(rf"^\s+{_IDENT}\s*:", nxt): break
                    if nxt.strip(): parts.append(nxt.strip())
                    k += 1
                typ = " ".join(parts)
                c = Constructor(cname, name, typ, j + 1, _arity(typ))
                d.constructors[cname] = c; ctors[cname] = c; j = k; continue
            j += 1
        data[name] = d; i = max(i + 1, j)
    return data, ctors

def _collect_top_decls(source: str):
    out = {}
    for i, line in enumerate(source.splitlines(), 1):
        if line.startswith((" ", "\t")) or line.lstrip().startswith("--"): continue
        for pat in (rf"^(?:record|data)\s+({_IDENT})\b", rf"^({_IDENT})(?:\s+{_IDENT})*\s*:"):
            m = re.match(pat, line)
            if m:
                out.setdefault(m.group(1), []).append(i); break
    return out

def _collect_clauses(source: str):
    out = {}
    for i, line in enumerate(source.splitlines(), 1):
        if line.startswith((" ", "\t")) or line.lstrip().startswith("--"): continue
        m = re.match(rf"^({_IDENT})\b(.*?)=\s*(.*)$", line)
        if m:
            out.setdefault(m.group(1), []).append((i, (m.group(1) + m.group(2)).strip(), m.group(3).strip()))
    return out

def _lhs_arity(lhs: str) -> int:
    rest = lhs.split(maxsplit=1)
    if len(rest) == 1: return 0
    text = rest[1]; depth = braces = count = 0; token = False
    for ch in text + " ":
        if ch == "{": braces += 1
        elif ch == "}": braces = max(0, braces - 1)
        elif ch == "(":
            depth += 1
            if depth == 1 and braces == 0: count += 1
        elif ch == ")": depth = max(0, depth - 1)
        elif ch.isspace() and depth == 0:
            if token and braces == 0: count += 1
            token = False
        elif depth == 0 and braces == 0: token = True
    return count

def _record_blocks(source: str):
    lines = source.splitlines(); i = 0
    while i < len(lines):
        m = re.match(rf"^({_IDENT})\b[^=]*=\s*(.*)$", lines[i])
        if not m:
            i += 1; continue
        name = m.group(1); chunk = [m.group(2)]; k = i + 1
        while k < len(lines):
            if lines[k] and not lines[k][0].isspace(): break
            chunk.append(lines[k]); k += 1
        text = "\n".join(chunk); pos = text.find("record")
        brace = text.find("{", pos + 6) if pos >= 0 else -1
        if brace >= 0:
            depth = 0
            for off, ch in enumerate(text[brace:], brace):
                if ch == "{": depth += 1
                elif ch == "}":
                    depth -= 1
                    if depth == 0:
                        yield name, i + 1, text[brace + 1:off]; break
        i = max(i + 1, k)

def _assignments(body: str):
    out = []
    for chunk in re.split(r"(?m)^\s*;\s*", body):
        m = re.match(rf"\s*({_IDENT})\s*=\s*(.*)", chunk, re.S)
        if m: out.append((m.group(1), m.group(2).strip()))
    return out

def _resolve_record(checker, summary, type_text: str):
    terminal = _terminal(type_text)
    if terminal in summary.records: return summary.records[terminal]
    imported = checker.imported_summaries(summary)
    if terminal and "." in terminal:
        alias, name = terminal.rsplit(".", 1); mod = imported.get(alias)
        if mod and name in mod.records: return mod.records[name]
    for alias, mod in imported.items():
        for name, rec in mod.records.items():
            if re.search(rf"\b{re.escape(alias)}\.{re.escape(name)}\b", type_text): return rec
    return None

def _diag(D, code, msg, s, line, col=1, hint=None):
    return D(code, msg, s.path, line, col, hint)

def extended_diagnostics(checker, s, D):
    source = s.source; clean = _strip_comments(source); out = []
    data, ctors = _collect_data(source); clauses = _collect_clauses(source)
    imported = checker.imported_summaries(s)

    try:
        expected = ".".join(s.path.relative_to(checker.root).with_suffix("").parts)
        if s.module_name != expected:
            out.append(_diag(D, "TSAGDA004", f"module declares {s.module_name}, but path denotes {expected}", s, 1))
    except ValueError: pass

    for name, lines in _collect_top_decls(source).items():
        if len(set(lines)) > 1:
            out.append(_diag(D, "TSAGDA005", f"duplicate top-level declaration {name}", s, sorted(set(lines))[1]))

    for rname, rec in s.records.items():
        names = []
        for off, line in enumerate(source.splitlines()[rec.line:], rec.line + 1):
            if line and not line[0].isspace(): break
            m = re.match(rf"^\s+({_IDENT})\s*:", line)
            if m:
                if m.group(1) in names:
                    out.append(_diag(D, "TSAGDA006", f"duplicate field {m.group(1)} in record {rname}", s, off))
                names.append(m.group(1))

    for name, sig in s.signatures.items():
        if name not in clauses and not re.search(rf"(?m)^\s+{re.escape(name)}\s*:", source):
            out.append(_diag(D, "TSAGDA008", f"{name} has a signature but no evident defining clause", s, sig.line))
    for name, cs in clauses.items():
        if name not in s.signatures:
            out.append(_diag(D, "TSAGDA009", f"{name} has defining clause(s) but no evident top-level signature", s, cs[0][0]))
        seen = set()
        for line, lhs, rhs in cs:
            key = re.sub(r"\s+", " ", lhs + "=" + rhs)
            if key in seen: out.append(_diag(D, "TSAGDA010", f"duplicate identical clause for {name}", s, line))
            seen.add(key)

    for m in re.finditer(r"\{\!.*?\!\}|\?", clean, re.S):
        line, col = _line_col(source, m.start()); out.append(_diag(D, "TSAGDA012", "unresolved interaction hole", s, line, col))
    for name, sig in s.signatures.items():
        if re.search(r"(?<![A-Za-z0-9_'])_(?![A-Za-z0-9_'])", sig.type_text):
            out.append(_diag(D, "TSAGDA013", f"exported signature {name} contains explicit underscore metavariable", s, sig.line))

    import_lines = []
    for i, line in enumerate(source.splitlines(), 1):
        m = re.match(r"^\s*(open\s+)?import\s+([A-Za-z0-9_.']+)(?:\s+as\s+([A-Za-z0-9_.']+))?(.*)$", line)
        if m: import_lines.append((i, bool(m.group(1)), m.group(2), m.group(3) or m.group(2).split(".")[-1], m.group(4)))
    alias_owner = {}
    for line, is_open, module, alias, rest in import_lines:
        p = checker.module_path(module); top = module.split(".")[0]
        if not p.exists() and ((checker.root / top).exists() or (checker.root / (top + ".agda")).exists() or top == "DASHI"):
            out.append(_diag(D, "TSAGDA020", f"imported repository module {module} does not exist", s, line))
        if alias in alias_owner and alias_owner[alias] != module:
            out.append(_diag(D, "TSAGDA028", f"alias {alias} refers to both {alias_owner[alias]} and {module}", s, line))
        alias_owner[alias] = module
        target = imported.get(alias)
        if target:
            exports = set(target.signatures) | set(target.records) | {f for r in target.records.values() for f in r.fields}
            um = re.search(r"using\s*\((.*?)\)", rest); hm = re.search(r"hiding\s*\((.*?)\)", rest); rm = re.search(r"renaming\s*\((.*?)\)", rest)
            if um:
                for n in re.findall(_IDENT, um.group(1)):
                    if n not in exports: out.append(_diag(D, "TSAGDA023", f"{n} in using(...) is not exported by {module}", s, line))
            if hm:
                for n in re.findall(_IDENT, hm.group(1)):
                    if n not in exports: out.append(_diag(D, "TSAGDA024", f"{n} in hiding(...) is not exported by {module}", s, line))
            if rm:
                for old in re.findall(rf"({_IDENT})\s+to\s+{_IDENT}", rm.group(1)):
                    if old not in exports: out.append(_diag(D, "TSAGDA025", f"renaming source {old} is not exported by {module}", s, line))

    for m in re.finditer(rf"\b({_IDENT})\.({_IDENT})\b", clean):
        alias, name = m.groups(); target = imported.get(alias)
        if target and name not in target.signatures and name not in target.records and not any(name in r.fields for r in target.records.values()):
            line, col = _line_col(source, m.start()); out.append(_diag(D, "TSAGDA021", f"{alias}.{name} is not exported by {target.module_name}", s, line, col))

    for name, sig in s.signatures.items():
        want = _arity(sig.type_text)
        for line, lhs, rhs in clauses.get(name, []):
            got = _lhs_arity(lhs)
            if got != want: out.append(_diag(D, "TSAGDA045", f"{name} clause has {got} explicit LHS arguments; signature has {want}", s, line))
            for nm in re.findall(r"\{\s*([A-Za-z_][A-Za-z0-9_']*)", lhs):
                if not re.search(rf"\{{\s*{re.escape(nm)}\s*(?::|\}})", sig.type_text):
                    out.append(_diag(D, "TSAGDA042", f"named implicit argument {nm} is absent from {name}'s telescope", s, line))

    for alias, mod in imported.items():
        for rname, rec in mod.records.items():
            for fname in rec.fields:
                for m in re.finditer(rf"\b{re.escape(alias)}\.{re.escape(fname)}\s+({_IDENT})", clean):
                    receiver = m.group(1)
                    if receiver == "_": continue
                    line, col = _line_col(source, m.start())
                    sigs = [x for x in s.signatures.values() if x.line <= line]
                    if sigs:
                        sig = max(sigs, key=lambda x: x.line)
                        bm = re.search(rf"[({{]\s*{re.escape(receiver)}\s*:\s*([^(){{}}]+)", sig.type_text)
                        if bm and not re.search(rf"\b{re.escape(alias)}\.{re.escape(rname)}\b|\b{re.escape(rname)}\b", bm.group(1)):
                            out.append(_diag(D, "TSAGDA050", f"{alias}.{fname} expects {rname}; receiver {receiver} has visibly different declared head", s, line, col))

    opened = {}
    for rname, rec in s.records.items():
        if rname in s.opens:
            for f in rec.fields: opened.setdefault(f, []).append(rname)
    for f, owners in opened.items():
        if len(owners) > 1: out.append(_diag(D, "TSAGDA055", f"opened projection {f} is ambiguous across {', '.join(owners)}", s, 1))

    for def_name, line, body in _record_blocks(source):
        sig = s.signatures.get(def_name)
        if not sig: continue
        target = _resolve_record(checker, s, sig.type_text)
        if not target: continue
        ass = _assignments(body); names = [n for n, _ in ass]
        for n in names:
            if n not in target.fields: out.append(_diag(D, "TSAGDA060", f"{n} is not a field of record {target.name}", s, line))
        for n in set(names):
            if names.count(n) > 1: out.append(_diag(D, "TSAGDA061", f"field {n} is assigned more than once", s, line))
        missing = [n for n in target.fields if n not in names]
        if missing: out.append(_diag(D, "TSAGDA062", f"record {target.name} is missing fields: {', '.join(missing)}", s, line))
        for n, rhs in ass:
            field = target.fields.get(n)
            if not field: continue
            lm = re.match(r"λ\s+(.+?)\s*→", re.sub(r"\s+", " ", rhs))
            if lm:
                got = len(lm.group(1).split()); want = _arity(field.type_text)
                if want and got != want: out.append(_diag(D, "TSAGDA064", f"field {n} lambda has {got} binders; target field has {want} explicit arguments", s, line))

    for dname, decl in data.items():
        for ctor in decl.constructors.values():
            terminal = _terminal(ctor.type_text)
            if terminal and terminal.split(".")[-1] != dname:
                out.append(_diag(D, "TSAGDA122", f"constructor {ctor.name} of {dname} visibly returns {terminal}", s, ctor.line))
            for domain in _split_arrows(ctor.type_text)[:-1]:
                if re.search(rf"\b{re.escape(dname)}\b\s*(?:→|->)", domain):
                    out.append(_diag(D, "TSAGDA130", f"{dname} occurs negatively in constructor {ctor.name}", s, ctor.line))

    for name, cs in clauses.items():
        sig = s.signatures.get(name)
        if not sig: continue
        catch = None
        for line, lhs, rhs in cs:
            for ctor_name, ctor in ctors.items():
                pm = re.search(rf"\(\s*{re.escape(ctor_name)}\s+([^)]*)\)", lhs)
                if pm and len(pm.group(1).split()) != ctor.arity:
                    out.append(_diag(D, "TSAGDA082", f"constructor pattern {ctor_name} has {len(pm.group(1).split())} arguments; arity is {ctor.arity}", s, line))
            if catch is not None: out.append(_diag(D, "TSAGDA088", f"clause follows visible catch-all at line {catch}", s, line)); break
            if re.fullmatch(rf"{re.escape(name)}(?:\s+_)+", lhs): catch = line
            rec = re.search(rf"\b{re.escape(name)}\s+(.+)$", rhs)
            if rec:
                lhs_args = lhs.split()[1:]; rhs_args = rec.group(1).split()[:len(lhs_args)]
                if lhs_args and lhs_args == rhs_args: out.append(_diag(D, "TSAGDA140", f"{name} recursively calls itself with identical visible arguments", s, line))

    eq = {}
    for name, sig in s.signatures.items():
        parts = re.split(r"\s*≡\s*", sig.type_text)
        if len(parts) == 2: eq[name] = (parts[0].strip(), parts[1].strip())
    for name, cs in clauses.items():
        for line, lhs, rhs in cs:
            if rhs == "refl" and name in eq:
                ha, hb = _terminal(eq[name][0]), _terminal(eq[name][1])
                if ha and hb and ha != hb and ha in data and hb in data:
                    out.append(_diag(D, "TSAGDA100", f"refl endpoints have incompatible datatype heads {ha} and {hb}", s, line))
            tm = re.search(rf"\btrans\s+({_IDENT})\s+({_IDENT})", rhs)
            if tm and tm.group(1) in eq and tm.group(2) in eq:
                ha, hb = _terminal(eq[tm.group(1)][1]), _terminal(eq[tm.group(2)][0])
                if ha and hb and ha != hb and ha in data and hb in data:
                    out.append(_diag(D, "TSAGDA102", f"trans intermediate endpoints have incompatible heads {ha} and {hb}", s, line))

    known = set(s.signatures) | set(data) | set(ctors)
    fix = {}
    postulates = []; in_post = False
    critical = any(x in str(s.path) for x in ("/Closure/", "/Millennium/", "Exact.agda", "Receipt", "Theorem"))
    for i, line in enumerate(source.splitlines(), 1):
        fm = re.match(r"^\s*(infix|infixl|infixr)\s*(\d+)?\s+(.+)$", line)
        if fm:
            for sym in fm.group(3).split():
                shape = (fm.group(1), fm.group(2))
                if sym not in known: out.append(_diag(D, "TSAGDA150", f"fixity declaration references unknown symbol {sym}", s, i))
                if sym in fix and fix[sym] != shape: out.append(_diag(D, "TSAGDA151", f"conflicting fixity declarations for {sym}", s, i))
                fix[sym] = shape
        sm = re.match(rf"^\s*syntax\s+({_IDENT})\b", line)
        if sm and sm.group(1) not in known: out.append(_diag(D, "TSAGDA153", f"syntax declaration references unknown symbol {sm.group(1)}", s, i))
        if re.match(r"^\s*postulate\s*$", line): in_post = True; continue
        if in_post:
            if line and not line[0].isspace(): in_post = False
            else:
                pm = re.match(rf"^\s+({_IDENT})\s*:", line)
                if pm: postulates.append((pm.group(1), i))
        if "{-# TERMINATING #-}" in line: out.append(_diag(D, "TSAGDA161", "TERMINATING pragma bypasses termination checking", s, i))
        if "{-# NON_TERMINATING #-}" in line: out.append(_diag(D, "TSAGDA162", "NON_TERMINATING pragma weakens termination guarantees", s, i))
        if "NO_POSITIVITY_CHECK" in line: out.append(_diag(D, "TSAGDA163", "NO_POSITIVITY_CHECK disables positivity checking", s, i))
        if "allow-unsolved-metas" in line.lower(): out.append(_diag(D, "TSAGDA164", "allow-unsolved-metas weakens the trust boundary", s, i))
        if re.match(r"^\s*\{-#\s*OPTIONS", line) and any(x in line for x in ("--type-in-type", "--no-positivity-check", "--no-termination-check")):
            out.append(_diag(D, "TSAGDA165", "unsafe OPTIONS pragma in proof source", s, i))
        cm = re.match(rf"^\s*\{{-#\s*(?:COMPILE|FOREIGN)\s+({_IDENT})", line)
        if cm and cm.group(1) not in known: out.append(_diag(D, "TSAGDA166", f"foreign/compile pragma names unknown declaration {cm.group(1)}", s, i))

    if critical:
        for n, line in postulates: out.append(_diag(D, "TSAGDA160", f"postulate {n} occurs in proof-critical source", s, line))
        if s.module_name.endswith("Exact"):
            for m in re.finditer(r"\{\!.*?\!\}|(?<![A-Za-z0-9_'])_(?![A-Za-z0-9_'])", clean, re.S):
                line, col = _line_col(source, m.start()); out.append(_diag(D, "TSAGDA204", "Exact module contains unresolved proof placeholder", s, line, col))
            for n, line in postulates: out.append(_diag(D, "TSAGDA204", f"Exact module postulates {n}", s, line))
        for n, line in postulates:
            if re.search(r"(theorem|receipt|exact|closure|gate)", n, re.I):
                out.append(_diag(D, "TSAGDA202", f"proof endpoint {n} is only postulated", s, line))
        if "/Closure/" in str(s.path):
            for line, _, module, _, _ in import_lines:
                if re.search(r"(Obstruction|Assumption|Postulate|Placeholder)", module, re.I):
                    out.append(_diag(D, "TSAGDA205", f"closure imports assumption/obstruction module {module}", s, line))

    for name, sig in s.signatures.items():
        if re.search(r"(?<![A-Za-z0-9_'])_(?![A-Za-z0-9_'])", sig.type_text):
            code = "TSAGDA173" if "≡" in sig.type_text else "TSAGDA170"
            out.append(_diag(D, code, f"signature {name} contains explicit underscore", s, sig.line))
    for _, line, body in _record_blocks(source):
        for fname, rhs in _assignments(body):
            if rhs.strip() == "_": out.append(_diag(D, "TSAGDA172", f"record field {fname} is filled with raw underscore", s, line))

    return out

def api_snapshot(checker):
    modules = {}
    for path in checker.root.rglob("*.agda"):
        try: rel = path.relative_to(checker.root)
        except ValueError: continue
        if set(rel.parts) & {".cache", "build", "dist", "vendor", "third_party", "tmp"}: continue
        try: s = checker.parse_summary(path)
        except Exception: continue
        data, ctors = _collect_data(s.source)
        modules[s.module_name] = {
            "path": str(rel),
            "exports": sorted(set(s.signatures) | set(s.records) | set(ctors)),
            "signatures": {k: re.sub(r"\s+", " ", v.type_text).strip() for k, v in s.signatures.items()},
            "records": {k: {"fields": sorted(r.fields)} for k, r in s.records.items()},
            "constructors": {k: {"datatype": c.datatype, "arity": c.arity} for k, c in ctors.items()},
        }
    return {"version": 1, "modules": modules}

def api_drift(checker, baseline, D):
    out = []; now = api_snapshot(checker).get("modules", {})
    for mod, old in baseline.get("modules", {}).items():
        cur = now.get(mod); path = checker.module_path(mod)
        if not cur or not path.exists(): continue
        s = checker.parse_summary(path)
        for name in sorted(set(old.get("exports", ())) - set(cur.get("exports", ()))):
            out.append(_diag(D, "TSAGDA180", f"exported name {name} disappeared from {mod}", s, 1))
        for rn, rold in old.get("records", {}).items():
            rnew = cur.get("records", {}).get(rn)
            if rnew:
                for fn in sorted(set(rold.get("fields", ())) - set(rnew.get("fields", ()))):
                    out.append(_diag(D, "TSAGDA181", f"record field {rn}.{fn} disappeared", s, 1))
        for cn, cold in old.get("constructors", {}).items():
            cnew = cur.get("constructors", {}).get(cn)
            if cnew and cnew.get("arity") != cold.get("arity"):
                out.append(_diag(D, "TSAGDA182", f"constructor {cn} arity changed {cold.get('arity')} -> {cnew.get('arity')}", s, 1))
        for fn, fold in old.get("signatures", {}).items():
            fnew = cur.get("signatures", {}).get(fn)
            if fnew and _arity(fold) != _arity(fnew):
                out.append(_diag(D, "TSAGDA183", f"function {fn} arity changed {_arity(fold)} -> {_arity(fnew)}", s, 1))
    return out
