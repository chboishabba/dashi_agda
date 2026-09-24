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

def _diag(D, code, msg, s, line, col=1, hint=None, severity="error", confidence="high"):
    return D(code, msg, s.path, line, col, hint, severity, confidence)

def extended_diagnostics(checker, s, D):
    source = s.source; clean = _strip_comments(source); out = []
    data = {
        name: DataDecl(
            name=name,
            line=decl.line,
            constructors={
                cname: Constructor(
                    name=cname,
                    datatype=name,
                    type_text=ctor.type_text,
                    line=ctor.line,
                    arity=_arity(ctor.type_text),
                )
                for cname, ctor in decl.constructors.items()
            },
            indexed=False,
        )
        for name, decl in s.ast.data.items()
    }
    ctors = {
        cname: ctor
        for decl in data.values()
        for cname, ctor in decl.constructors.items()
    }
    clauses = {
        name: [
            (clause.line, clause.lhs_text, clause.rhs_text)
            for clause in items
        ]
        for name, items in s.ast.clauses.items()
    }
    imported = checker.imported_summaries(s)

    try:
        expected = ".".join(s.path.relative_to(checker.root).with_suffix("").parts)
        if s.module_name != expected:
            out.append(_diag(D, "TSAGDA004", f"module declares {s.module_name}, but path denotes {expected}", s, 1))
    except ValueError: pass

    for name, occurrences in s.ast.signature_occurrences.items():
        if len(occurrences) > 1:
            out.append(_diag(D, "TSAGDA005", f"duplicate top-level signature {name}", s, occurrences[1].line))

    for rname, rec in s.ast.records.items():
        seen_fields = set()
        for field in rec.field_occurrences:
            if field.name in seen_fields:
                out.append(_diag(D, "TSAGDA006", f"duplicate field {field.name} in record {rname}", s, field.line))
            seen_fields.add(field.name)

    constructor_owner = {}
    for dname, decl in s.ast.data.items():
        for ctor in decl.constructor_occurrences:
            previous = constructor_owner.get(ctor.name)
            if previous is not None:
                out.append(_diag(D, "TSAGDA007", f"duplicate constructor {ctor.name}", s, ctor.line))
            constructor_owner[ctor.name] = dname

    for name, sig in s.signatures.items():
        if name not in clauses and not re.search(rf"(?m)^\s+{re.escape(name)}\s*:", source):
            out.append(_diag(D, "TSAGDA008", f"{name} has a signature but no evident defining clause", s, sig.line, severity="warning", confidence="medium"))
    for name, cs in clauses.items():
        if name not in s.signatures:
            out.append(_diag(D, "TSAGDA009", f"{name} has defining clause(s) but no evident top-level signature", s, cs[0][0], severity="warning", confidence="medium"))
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

    import_lines = [
        (item.line, item.opened, item.module, item.alias, item.directives)
        for item in s.ast.imports
    ]
    alias_owner = {}
    for line, is_open, module, alias, directives in import_lines:
        p = checker.module_path(module); top = module.split(".")[0]
        if not p.exists() and ((checker.root / top).exists() or (checker.root / (top + ".agda")).exists() or top == "DASHI"):
            out.append(_diag(D, "TSAGDA020", f"imported repository module {module} does not exist", s, line))
        if alias in alias_owner and alias_owner[alias] != module:
            out.append(_diag(D, "TSAGDA028", f"alias {alias} refers to both {alias_owner[alias]} and {module}", s, line))
        alias_owner[alias] = module
        target = imported.get(alias)
        if target:
            exports = set(target.signatures) | set(target.records) | {f for r in target.records.values() for f in r.fields}
            for directive in directives:
                if directive.kind == "using":
                    for n in directive.names:
                        if n not in exports:
                            out.append(_diag(D, "TSAGDA023", f"{n} in using(...) is not exported by {module}", s, line))
                elif directive.kind == "hiding":
                    for n in directive.names:
                        if n not in exports:
                            out.append(_diag(D, "TSAGDA024", f"{n} in hiding(...) is not exported by {module}", s, line, severity="warning", confidence="medium"))
                elif directive.kind == "renaming":
                    for old, new in directive.renamings:
                        if old not in exports:
                            out.append(_diag(D, "TSAGDA025", f"renaming source {old} is not exported by {module}", s, line))

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
        if len(owners) > 1: out.append(_diag(D, "TSAGDA055", f"opened projection {f} is ambiguous across {', '.join(owners)}", s, 1, severity="warning", confidence="medium"))

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
                if lhs_args and lhs_args == rhs_args: out.append(_diag(D, "TSAGDA140", f"{name} recursively calls itself with identical visible arguments", s, line, severity="warning", confidence="medium"))

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
                if sym not in known: out.append(_diag(D, "TSAGDA150", f"fixity declaration references unknown symbol {sym}", s, i, severity="warning", confidence="medium"))
                if sym in fix and fix[sym] != shape: out.append(_diag(D, "TSAGDA151", f"conflicting fixity declarations for {sym}", s, i))
                fix[sym] = shape
        sm = re.match(rf"^\s*syntax\s+({_IDENT})\b", line)
        if sm and sm.group(1) not in known: out.append(_diag(D, "TSAGDA153", f"syntax declaration references unknown symbol {sm.group(1)}", s, i, severity="warning", confidence="medium"))
        if re.match(r"^\s*postulate\s*$", line): in_post = True; continue
        if in_post:
            if line and not line[0].isspace(): in_post = False
            else:
                pm = re.match(rf"^\s+({_IDENT})\s*:", line)
                if pm: postulates.append((pm.group(1), i))
        if "{-# TERMINATING #-}" in line: out.append(_diag(D, "TSAGDA161", "TERMINATING pragma bypasses termination checking", s, i, severity="warning", confidence="medium"))
        if "{-# NON_TERMINATING #-}" in line: out.append(_diag(D, "TSAGDA162", "NON_TERMINATING pragma weakens termination guarantees", s, i, severity="warning", confidence="medium"))
        if "NO_POSITIVITY_CHECK" in line: out.append(_diag(D, "TSAGDA163", "NO_POSITIVITY_CHECK disables positivity checking", s, i, severity="warning", confidence="medium"))
        if "allow-unsolved-metas" in line.lower(): out.append(_diag(D, "TSAGDA164", "allow-unsolved-metas weakens the trust boundary", s, i, severity="warning", confidence="medium"))
        if re.match(r"^\s*\{-#\s*OPTIONS", line) and any(x in line for x in ("--type-in-type", "--no-positivity-check", "--no-termination-check")):
            out.append(_diag(D, "TSAGDA165", "unsafe OPTIONS pragma in proof source", s, i, severity="warning", confidence="medium"))
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
                    out.append(_diag(D, "TSAGDA205", f"closure imports assumption/obstruction module {module}", s, line, severity="warning", confidence="medium"))

    for name, sig in s.signatures.items():
        if re.search(r"(?<![A-Za-z0-9_'])_(?![A-Za-z0-9_'])", sig.type_text):
            code = "TSAGDA173" if "≡" in sig.type_text else "TSAGDA170"
            out.append(_diag(D, code, f"signature {name} contains explicit underscore", s, sig.line))
    for _, line, body in _record_blocks(source):
        for fname, rhs in _assignments(body):
            if rhs.strip() == "_": out.append(_diag(D, "TSAGDA172", f"record field {fname} is filled with raw underscore", s, line, severity="warning", confidence="medium"))

    # Repository graph checks: TSAGDA029 import cycles and TSAGDA030 module collisions.
    graph = checker.dependency_graph()
    state, stack, cycle_for = {}, [], set()
    def visit(node):
        state[node] = 1; stack.append(node)
        for dep in graph.get(node, ()):
            if dep not in graph: continue
            if state.get(dep, 0) == 0: visit(dep)
            elif state.get(dep) == 1 and dep in stack:
                cycle_for.update(stack[stack.index(dep):])
        stack.pop(); state[node] = 2
    if s.module_name in graph:
        visit(s.module_name)
        if s.module_name in cycle_for:
            out.append(_diag(D, "TSAGDA029", f"module {s.module_name} participates in a repository import cycle", s, 1))

    identities = {}
    for p in checker.root.rglob("*.agda"):
        try:
            rel = p.relative_to(checker.root)
        except ValueError:
            continue
        if set(rel.parts) & {".cache", "build", "dist", "vendor", "third_party", "tmp"}: continue
        try:
            head = p.read_text(encoding="utf-8")[:4096]
        except (OSError, UnicodeDecodeError):
            continue
        mm = re.search(r"(?m)^\s*module\s+([A-Za-z0-9_.']+).*?\s+where\b", head)
        if mm: identities.setdefault(mm.group(1), []).append(p)
    peers = identities.get(s.module_name, [])
    if len(peers) > 1:
        out.append(_diag(D, "TSAGDA030", f"module identity {s.module_name} is declared by multiple files", s, 1))

    # TSAGDA026/027: collisions created by open imports and renamings.
    visible = {}
    for line, is_open, module, alias, directives in import_lines:
        if not is_open: continue
        target = imported.get(alias)
        if not target: continue
        names = set(target.signatures) | set(target.records) | {f for r in target.records.values() for f in r.fields}
        ren = {}
        for directive in directives:
            if directive.kind == "using":
                names &= set(directive.names)
            elif directive.kind == "hiding":
                names -= set(directive.names)
            elif directive.kind == "renaming":
                ren.update(dict(directive.renamings))
        for n in names:
            vn = ren.get(n, n); visible.setdefault(vn, []).append(module)
    for n, mods in visible.items():
        if len(set(mods)) > 1 and n not in s.signatures and n not in s.records:
            out.append(_diag(D, "TSAGDA027", f"open imports make {n} ambiguous between {', '.join(sorted(set(mods)))}", s, 1, severity="warning", confidence="medium"))

    # TSAGDA040/041/046/047/049: bounded arity checks for simple applications.
    known_arity = {name: _arity(sig.type_text) for name, sig in s.signatures.items()}
    known_arity.update({name: ctor.arity for name, ctor in ctors.items()})
    for name, want in known_arity.items():
        if want == 0: continue
        for m in re.finditer(rf"(?m)(?<![:.\w]){re.escape(name)}((?:\s+[^=\n;,)]+)+)", clean):
            if m.start() < len(source) and source[max(0, m.start()-16):m.start()].rstrip().endswith(":"):
                continue
            args = [a for a in m.group(1).strip().split() if not a.startswith("{")]
            if len(args) > want:
                line, col = _line_col(source, m.start())
                code = "TSAGDA046" if name in ctors else "TSAGDA040"
                out.append(_diag(D, code, f"{name} is visibly over-applied: {len(args)} explicit arguments for arity {want}", s, line, col))

    # Local record constructors: constructor arity is the number of fields.
    for rname, rec in s.records.items():
        lines = source.splitlines(); block = lines[rec.line:rec.line + 12]
        cm = next((re.match(rf"^\s+constructor\s+({_IDENT})", x) for x in block if re.match(rf"^\s+constructor\s+({_IDENT})", x)), None)
        if cm:
            cname = cm.group(1); want = len(rec.fields)
            for m in re.finditer(rf"\b{re.escape(cname)}\b([^\n=;]*)", clean):
                args = m.group(1).strip().split()
                if args and len(args) > want:
                    line, col = _line_col(source, m.start())
                    out.append(_diag(D, "TSAGDA047", f"record constructor {cname} is visibly over-applied ({len(args)}>{want})", s, line, col))

    # TSAGDA052/053: qualified projections with no/too many visible receiver arguments.
    for alias, mod in imported.items():
        for rname, rec in mod.records.items():
            for fname, fi in rec.fields.items():
                pat = rf"\b{re.escape(alias)}\.{re.escape(fname)}\b"
                for m in re.finditer(pat, clean):
                    tail = clean[m.end():].split("\n", 1)[0]
                    if re.match(r"\s*(?:$|[=;,)→])", tail):
                        line, col = _line_col(source, m.start())
                        out.append(_diag(D, "TSAGDA052", f"{alias}.{fname} is used without a visible {rname} receiver", s, line, col))
                    else:
                        args = re.match(r"\s+([^=;,)→]+)", tail)
                        if args:
                            got = len(args.group(1).split())
                            want = 1 + _arity(fi.type_text)
                            if got > want:
                                line, col = _line_col(source, m.start())
                                out.append(_diag(D, "TSAGDA053", f"{alias}.{fname} is visibly over-applied ({got}>{want})", s, line, col))

    # TSAGDA074/075/079: only rigid literals/constructors/non-functions.
    for cname, ctor in ctors.items():
        for m in re.finditer(rf"\b{re.escape(cname)}\b", clean):
            before = clean[max(0, m.start()-80):m.start()]
            if re.search(r"≡\s*$", before):
                other = re.search(r"([A-Za-z_][A-Za-z0-9_']*)\s*≡\s*$", before)
                if other and other.group(1) in ctors and ctors[other.group(1)].datatype != ctor.datatype:
                    line, col = _line_col(source, m.start())
                    out.append(_diag(D, "TSAGDA075", f"equality compares constructors from different datatypes: {other.group(1)} vs {cname}", s, line, col))

    # TSAGDA080/081/085/086/087/089: simple non-indexed pattern facts.
    for name, cs in clauses.items():
        sig = s.signatures.get(name)
        if not sig: continue
        first_domain = _split_arrows(sig.type_text)[0].strip() if _split_arrows(sig.type_text) else ""
        dtype = next((d for d in data.values() if re.search(rf"\b{re.escape(d.name)}\b", first_domain)), None)
        if dtype and not dtype.indexed:
            used = []
            absurd = []
            for line, lhs, rhs in cs:
                if "()" in lhs: absurd.append(line)
                heads = [cn for cn in dtype.constructors if re.search(rf"\b{re.escape(cn)}\b", lhs)]
                used.extend(heads)
                for tok in re.findall(rf"\b({_IDENT})\b", lhs):
                    if tok in ctors and ctors[tok].datatype != dtype.name:
                        out.append(_diag(D, "TSAGDA081", f"pattern constructor {tok} belongs to {ctors[tok].datatype}, expected {dtype.name}", s, line))
            if absurd and dtype.constructors:
                for line in absurd:
                    out.append(_diag(D, "TSAGDA085", f"absurd pattern used for visibly inhabited datatype {dtype.name}", s, line))
            if dtype.constructors and used and set(used) != set(dtype.constructors) and not any(re.fullmatch(rf"{re.escape(name)}\s+_", lhs) for _, lhs, _ in cs):
                missing = sorted(set(dtype.constructors) - set(used))
                if missing: out.append(_diag(D, "TSAGDA087", f"simple finite coverage for {name} misses constructors: {', '.join(missing)}", s, cs[0][0]))
            if len(used) != len(set(used)):
                out.append(_diag(D, "TSAGDA089", f"{name} has duplicate constructor branches in simple finite coverage", s, cs[0][0]))

    # TSAGDA101/103/104: equality combinator outer-shape checks.
    for name, cs in clauses.items():
        for line, lhs, rhs in cs:
            sm = re.search(rf"\bsym\s+({_IDENT})", rhs)
            if sm and sm.group(1) in eq and name in eq:
                pa, pb = eq[sm.group(1)]; ta, tb = eq[name]
                if _terminal(pa) and _terminal(tb) and _terminal(pa) != _terminal(tb):
                    out.append(_diag(D, "TSAGDA101", f"sym proof endpoint head does not match target equality for {name}", s, line))
            cm = re.search(rf"\bcong\s+({_IDENT})\s+({_IDENT})", rhs)
            if cm and cm.group(2) in eq and cm.group(1) in s.signatures:
                fun = s.signatures[cm.group(1)]
                if _arity(fun.type_text) == 0:
                    out.append(_diag(D, "TSAGDA103", f"cong function {cm.group(1)} has no visible function argument", s, line))

    # TSAGDA120/121/123: rigid declaration sanity.
    known_terms = set(clauses) | set(ctors)
    for rname, rec in s.records.items():
        for fname, fi in rec.fields.items():
            head = _terminal(fi.type_text)
            if head in known_terms and head not in data and head not in s.records:
                out.append(_diag(D, "TSAGDA120", f"field {rname}.{fname} has known term {head} in type-head position", s, fi.line))
    for dname, decl in data.items():
        for ctor in decl.constructors.values():
            head = _terminal(ctor.type_text)
            if head in known_terms and head not in data:
                out.append(_diag(D, "TSAGDA121", f"constructor {ctor.name} result resolves to known term {head}", s, ctor.line))

    # TSAGDA131: explicit negative occurrence is the same bounded contravariant test.
    for dname, decl in data.items():
        for ctor in decl.constructors.values():
            if any(re.search(rf"\b{re.escape(dname)}\b\s*(?:→|->)", dom) for dom in _split_arrows(ctor.type_text)[:-1]):
                out.append(_diag(D, "TSAGDA131", f"{dname} occurs in an obvious contravariant constructor position", s, ctor.line))

    # TSAGDA141/142 are advisory structural recursion warnings.
    for name, cs in clauses.items():
        recursive = [(line, lhs, rhs) for line, lhs, rhs in cs if re.search(rf"\b{re.escape(name)}\b", rhs)]
        for line, lhs, rhs in recursive:
            args = lhs.split()[1:]
            call = re.search(rf"\b{re.escape(name)}\s+(.+)$", rhs)
            if call and args:
                rhs_args = call.group(1).split()[:len(args)]
                if any(a.isdigit() and b.isdigit() and int(b) > int(a) for a, b in zip(args, rhs_args)):
                    out.append(_diag(D, "TSAGDA141", f"{name} has an obviously increasing numeric recursive argument", s, line, severity="warning", confidence="medium"))
                if rhs_args and not any((a.startswith("(") and b in a) or b in {"pred", "tail"} for a, b in zip(args, rhs_args)):
                    out.append(_diag(D, "TSAGDA142", f"{name} recursive call has no syntactically obvious smaller argument", s, line, severity="warning", confidence="medium"))

    # TSAGDA143: termination bypass in proof-critical code.
    if critical and ("{-# TERMINATING #-}" in source or "{-# NON_TERMINATING #-}" in source):
        line = next((i for i, x in enumerate(source.splitlines(), 1) if "TERMINATING" in x), 1)
        out.append(_diag(D, "TSAGDA143", "proof-critical code uses a termination-bypass pragma", s, line))

    # TSAGDA152: mixfix holes versus visible arity.
    for sym, shape in fix.items():
        if "_" in sym and sym in s.signatures:
            holes = sym.count("_"); want = _arity(s.signatures[sym].type_text)
            if holes != want:
                out.append(_diag(D, "TSAGDA152", f"mixfix {sym} has {holes} holes but signature has {want} explicit arguments", s, s.signatures[sym].line, severity="warning", confidence="medium"))

    # TSAGDA174: raw metas in module application/import-like syntax.
    for m in re.finditer(rf"\bmodule\s+{_IDENT}\s*=\s*{_IDENT}(?:\.{_IDENT})*\s+_", clean):
        line, col = _line_col(source, m.start())
        out.append(_diag(D, "TSAGDA174", "module application contains raw underscore metavariable", s, line, col, severity="warning", confidence="medium"))

    # TSAGDA200/201/203/206/208: DASHI-specific structural policy.
    if critical:
        for _, line, body in _record_blocks(source):
            for fname, rhs in _assignments(body):
                if rhs.strip() == "_":
                    out.append(_diag(D, "TSAGDA201", f"proof-critical record field {fname} contains raw metavariable", s, line))
        for rname, rec in s.records.items():
            for fname, fi in rec.fields.items():
                if re.search(r"(agreement|proof|witness|receipt)", fname, re.I) and _terminal(fi.type_text) == "Set":
                    out.append(_diag(D, "TSAGDA203", f"proof-like field {rname}.{fname} is unconstrained Set rather than an evident proposition/witness", s, fi.line, severity="warning", confidence="medium"))
        if re.search(r"(FactorThrough|Admissib|Bidi)", s.module_name, re.I):
            heads = [_terminal(sig.type_text) for sig in s.signatures.values()]
            rigid = sorted(set(h for h in heads if h and "." in h))
            if len(rigid) > 1:
                code = "TSAGDA208" if re.search(r"(FactorThrough|Admissib)", s.module_name, re.I) else "TSAGDA206"
                out.append(_diag(D, code, f"bridge module exposes multiple qualified carrier/result families: {', '.join(rigid[:6])}", s, 1))


    # Remaining bounded structural diagnostics and specific aliases.

    # TSAGDA011: empty where/mutual blocks.
    lines = source.splitlines()
    for i, line in enumerate(lines, 1):
        if re.match(r"^\s*(where|mutual)\s*$", line):
            indent = len(line) - len(line.lstrip())
            following = lines[i:i + 8]
            has_child = any(x.strip() and (len(x) - len(x.lstrip())) > indent for x in following)
            if not has_child:
                out.append(_diag(D, "TSAGDA011", f"{line.strip()} block has no evident indented declaration", s, i))

    # TSAGDA022/026: qualified alias mistakes and rename collisions.
    known_aliases = set(imported)
    local_prefixes = set(s.records) | set(data)
    for m in re.finditer(rf"\b({_IDENT})\.({_IDENT})\b", clean):
        alias, name = m.groups()
        if alias not in known_aliases and alias not in local_prefixes and alias[:1].isupper():
            line, col = _line_col(source, m.start())
            out.append(_diag(D, "TSAGDA022", f"qualified prefix {alias} is not a known import alias or local namespace", s, line, col, severity="warning", confidence="medium"))
    for line, is_open, module, alias, directives in import_lines:
        for directive in directives:
            if directive.kind != "renaming":
                continue
            for old, new in directive.renamings:
                if new in s.signatures or new in s.records:
                    out.append(_diag(D, "TSAGDA026", f"renaming {old} to {new} collides with a local declaration", s, line))

    # TSAGDA041/043/044/110/111: simple telescope and lambda visibility.
    for name, cs in clauses.items():
        sig = s.signatures.get(name)
        if not sig: continue
        parts = _split_arrows(sig.type_text); want = _arity(sig.type_text)
        implicit_names = set(re.findall(rf"\{{\s*({_IDENT})\s*:", sig.type_text))
        explicit_names = set(re.findall(rf"\(\s*({_IDENT})\s*:", sig.type_text))
        for line, lhs, rhs in cs:
            got = _lhs_arity(lhs)
            if got != want:
                out.append(_diag(D, "TSAGDA110", f"{name} clause binder count {got} does not match explicit telescope arity {want}", s, line))
            for nm in re.findall(r"\{\s*([A-Za-z_][A-Za-z0-9_']*)", lhs):
                if nm in explicit_names:
                    out.append(_diag(D, "TSAGDA043", f"explicit binder {nm} is matched with implicit visibility", s, line))
                    out.append(_diag(D, "TSAGDA111", f"clause visibility for {nm} disagrees with signature", s, line))
            lm = re.fullmatch(r"λ\s+(.+?)\s*→\s*.+", rhs)
            if lm and want:
                lam = len([x for x in lm.group(1).split() if not x.startswith("{")])
                if lam != max(0, want - got):
                    out.append(_diag(D, "TSAGDA044", f"RHS lambda exposes {lam} binders but {max(0, want-got)} explicit binders remain", s, line, severity="warning", confidence="medium"))
            if rhs in s.signatures and _arity(s.signatures[rhs].type_text) > 0 and _terminal(sig.type_text) not in {None, "Set", "Set₁", "Set₂"}:
                out.append(_diag(D, "TSAGDA041", f"RHS {rhs} is a known function left unapplied in a saturated result position", s, line, severity="warning", confidence="medium"))

    # TSAGDA048: parameterized module application arity.
    module_params = {}
    for alias, mod in imported.items():
        first = mod.source.splitlines()[0] if mod.source.splitlines() else ""
        mm = re.match(rf"^\s*module\s+[A-Za-z0-9_.']+\s*(.*?)\s+where\s*$", first)
        if mm:
            module_params[alias] = len(re.findall(r"[\({]\s*[A-Za-z_][A-Za-z0-9_']*\s*:", mm.group(1)))
    for i, line in enumerate(lines, 1):
        mm = re.match(rf"^\s*module\s+{_IDENT}\s*=\s*({_IDENT})(?:\.{_IDENT})*\s*(.*)$", line)
        if mm and mm.group(1) in module_params:
            got = len([x for x in mm.group(2).split() if x and x != "_"])
            want = module_params[mm.group(1)]
            if got != want:
                out.append(_diag(D, "TSAGDA048", f"module application supplies {got} visible arguments; imported module expects {want}", s, i))

    # TSAGDA049/051/054: projection receiver/arity refinements.
    for alias, mod in imported.items():
        field_owner = {f: rn for rn, rec in mod.records.items() for f in rec.fields}
        for fname, owner in field_owner.items():
            for m in re.finditer(rf"\b{re.escape(alias)}\.{re.escape(fname)}\s+({_IDENT})", clean):
                receiver = m.group(1); line, col = _line_col(source, m.start())
                if receiver in mod.records or receiver in mod.signatures:
                    out.append(_diag(D, "TSAGDA051", f"{alias}.{fname} receives known declaration/type name {receiver} where a {owner} value is expected", s, line, col, severity="warning", confidence="medium"))
                sigs = [x for x in s.signatures.values() if x.line <= line]
                if sigs:
                    sig = max(sigs, key=lambda x: x.line)
                    bm = re.search(rf"[({{]\s*{re.escape(receiver)}\s*:\s*(?:{re.escape(alias)}\.)?({_IDENT})", sig.type_text)
                    if bm and bm.group(1) in mod.records and bm.group(1) != owner:
                        out.append(_diag(D, "TSAGDA054", f"projection {fname} belongs to {owner}, but receiver {receiver} is declared as {bm.group(1)}", s, line, col))
            # Existing 052/053 evidence is also the generic projection arity diagnostic.
            for m in re.finditer(rf"\b{re.escape(alias)}\.{re.escape(fname)}\b", clean):
                tail = clean[m.end():].split("\n", 1)[0]
                if re.match(r"\s*(?:$|[=;,)→])", tail):
                    line, col = _line_col(source, m.start())
                    out.append(_diag(D, "TSAGDA049", f"projection {alias}.{fname} is under-applied", s, line, col))

    # TSAGDA056: dependent field projection used bare in a signature despite a matching record binder.
    for rname, rec in s.records.items():
        dependent = {f for f, fi in rec.fields.items() if any(re.search(rf"\b{re.escape(other)}\b", fi.type_text) for other in rec.fields if other != f)}
        if not dependent: continue
        for name, sig in s.signatures.items():
            if re.search(rf"\(\s*({_IDENT})\s*:\s*{re.escape(rname)}\b", sig.type_text):
                for f in dependent:
                    if re.search(rf"(?<!\.)\b{re.escape(f)}\b(?!\s+{_IDENT})", sig.type_text):
                        out.append(_diag(D, "TSAGDA056", f"dependent projection {f} is used without an evident {rname} receiver", s, sig.line, severity="warning", confidence="medium"))

    # TSAGDA063/065/066/067/068 and TSAGDA200: record target/value shape refinements.
    record_ctor_owner = {}
    for rname, rec in s.records.items():
        block = lines[rec.line:rec.line + 12]
        for x in block:
            cm = re.match(rf"^\s+constructor\s+({_IDENT})", x)
            if cm: record_ctor_owner[cm.group(1)] = rname
    for def_name, line, body in _record_blocks(source):
        sig = s.signatures.get(def_name)
        if not sig: continue
        target = _resolve_record(checker, s, sig.type_text)
        if not target and _terminal(sig.type_text) in data:
            out.append(_diag(D, "TSAGDA063", f"record expression is used where datatype {_terminal(sig.type_text)} is the declared result", s, line))
        if not target: continue
        for fname, rhs in _assignments(body):
            field = target.fields.get(fname)
            if not field: continue
            if rhs == "Set" and _terminal(field.type_text) not in {"Set", "Set₁", "Set₂", "Setω", "Prop", "Prop₁"}:
                out.append(_diag(D, "TSAGDA200", f"adapter field {fname} supplies Set where target expects witness/result {_terminal(field.type_text)}", s, line))
            rm = re.match(rf"({_IDENT})\b", rhs)
            if rm and rm.group(1) in record_ctor_owner and record_ctor_owner[rm.group(1)] != target.name:
                out.append(_diag(D, "TSAGDA068", f"constructor {rm.group(1)} constructs {record_ctor_owner[rm.group(1)]}, not target record {target.name}", s, line))
            pm = re.match(rf"({_IDENT})\s+({_IDENT})", rhs)
            if pm:
                proj, recv = pm.groups()
                sig_b = re.search(rf"[({{]\s*{re.escape(recv)}\s*:\s*({_IDENT})", sig.type_text)
                if sig_b and sig_b.group(1) in s.records and proj in s.records[sig_b.group(1)].fields:
                    actual = s.records[sig_b.group(1)].fields[proj]
                    et, at = _terminal(field.type_text), _terminal(actual.type_text)
                    if et and at and et != at:
                        code = "TSAGDA065" if et in {"Set","Set₁","Set₂","Setω","Prop","Prop₁"} or at in {"Set","Set₁","Set₂","Setω","Prop","Prop₁"} else "TSAGDA066"
                        out.append(_diag(D, code, f"field {fname} expects {et}, source projection {proj} returns {at}", s, line))
                        out.append(_diag(D, "TSAGDA067", f"source projection {proj} is structurally incompatible with target field {fname}", s, line))

    # TSAGDA070-079 shallow head checks on simple RHSs/applications.
    for name, cs in clauses.items():
        sig = s.signatures.get(name)
        if not sig: continue
        expected = _terminal(sig.type_text)
        for line, lhs, rhs in cs:
            if rhs in {"Set","Set₀","Set₁","Set₂","Setω","Prop","Prop₁"} and expected not in {"Set","Set₀","Set₁","Set₂","Setω","Prop","Prop₁"}:
                out.append(_diag(D, "TSAGDA078", f"sort {rhs} is used as the value of {name}, whose rigid result head is {expected}", s, line))
                out.append(_diag(D, "TSAGDA070", f"type/sort supplied where a term of head {expected} is expected", s, line))
            rm = re.fullmatch(rf"({_IDENT})(?:\s+.*)?", rhs)
            if rm and rm.group(1) in ctors and expected and ctors[rm.group(1)].datatype != expected:
                out.append(_diag(D, "TSAGDA072", f"{name} returns constructor {rm.group(1)} of {ctors[rm.group(1)].datatype}, not declared head {expected}", s, line))
                out.append(_diag(D, "TSAGDA075", f"constructor {rm.group(1)} belongs to wrong datatype for {name}", s, line))
            call = re.match(rf"({_IDENT})\s+({_IDENT})$", rhs)
            if call and call.group(1) in s.signatures and call.group(2) in ctors:
                fdom = _split_arrows(s.signatures[call.group(1)].type_text)[0]
                expected_dt = next((d for d in data if re.search(rf"\b{re.escape(d)}\b", fdom)), None)
                actual_dt = ctors[call.group(2)].datatype
                if expected_dt and expected_dt != actual_dt:
                    out.append(_diag(D, "TSAGDA073", f"argument {call.group(2)} has datatype {actual_dt}, but {call.group(1)} expects {expected_dt}", s, line))
            if re.match(r"^\d+$", rhs) and expected in {"Bool","String","Char"}:
                out.append(_diag(D, "TSAGDA074", f"numeric literal is incompatible with rigid result head {expected}", s, line))
            call0 = re.match(rf"({_IDENT})\s+.+", rhs)
            if call0 and call0.group(1) in s.signatures and _arity(s.signatures[call0.group(1)].type_text) == 0:
                out.append(_diag(D, "TSAGDA079", f"known non-function {call0.group(1)} is applied as a function", s, line))
    # Known functions occurring as bare type heads.
    for name, sig in s.signatures.items():
        for fn, fsig in s.signatures.items():
            if fn == name or _arity(fsig.type_text) == 0: continue
            if re.search(rf"(?:^|→|\()\s*{re.escape(fn)}\s*(?:→|\)|$)", sig.type_text):
                out.append(_diag(D, "TSAGDA076", f"known function {fn} is used as a type without enough application", s, sig.line, severity="warning", confidence="medium"))

    # TSAGDA080/083/084/086: bounded pattern hygiene.
    for name, cs in clauses.items():
        sig = s.signatures.get(name)
        for line, lhs, rhs in cs:
            for pm in re.finditer(r"\(\s*([A-Z][A-Za-z0-9_']*)", lhs):
                token = pm.group(1)
                if token not in ctors and token not in data and token not in s.records:
                    out.append(_diag(D, "TSAGDA080", f"pattern references unknown constructor-like name {token}", s, line, severity="warning", confidence="medium"))
            toks = re.findall(rf"\b({_IDENT})\b", lhs)
            simple = [x for x in toks if x != name and x not in ctors and x not in data and x not in s.records]
            for b in set(simple):
                if simple.count(b) > 1:
                    out.append(_diag(D, "TSAGDA083", f"linear pattern binder {b} appears more than once", s, line, severity="warning", confidence="medium"))
            for dm in re.finditer(rf"\.({_IDENT})", lhs):
                nm = dm.group(1)
                if nm not in toks:
                    out.append(_diag(D, "TSAGDA084", f"inaccessible pattern .{nm} has no evident local binder", s, line, severity="warning", confidence="medium"))
            if "λ ()" in rhs and sig:
                domains = _split_arrows(sig.type_text)
                inhabited = next((d for d in data.values() if d.constructors and any(re.search(rf"\b{re.escape(d.name)}\b", dom) for dom in domains[:-1])), None)
                if inhabited:
                    out.append(_diag(D, "TSAGDA086", f"absurd lambda used while a visible domain {inhabited.name} is inhabited", s, line, severity="warning", confidence="medium"))

    # TSAGDA071: known term supplied in a type/sort-valued record field.
    known_term_heads = set(clauses) | set(ctors)
    for def_name, line, body in _record_blocks(source):
        sig = s.signatures.get(def_name)
        if not sig: continue
        target = _resolve_record(checker, s, sig.type_text)
        if not target: continue
        for fname, rhs in _assignments(body):
            field = target.fields.get(fname)
            if not field or _terminal(field.type_text) not in {"Set","Set₀","Set₁","Set₂","Setω","Prop","Prop₁"}: continue
            rm = re.fullmatch(rf"({_IDENT})", rhs.strip())
            if rm and rm.group(1) in known_term_heads and rm.group(1) not in data and rm.group(1) not in s.records:
                out.append(_diag(D, "TSAGDA071", f"known term {rm.group(1)} is supplied where field {fname} expects a type/sort", s, line))

    # TSAGDA077: visible type-constructor parameter arity.
    type_params = {}
    for i, line in enumerate(lines, 1):
        dm = re.match(rf"^(?:data|record)\s+({_IDENT})\s*(.*?)\s*:\s*", line)
        if dm:
            type_params[dm.group(1)] = len(re.findall(r"[\({]\s*[A-Za-z_][A-Za-z0-9_']*\s*:", dm.group(2)))
    for tname, want in type_params.items():
        if want == 0: continue
        for name, sig in s.signatures.items():
            for m in re.finditer(rf"\b{re.escape(tname)}\b((?:\s+{_IDENT})*)", sig.type_text):
                got = len(m.group(1).split())
                if got != want:
                    out.append(_diag(D, "TSAGDA077", f"type constructor {tname} has {want} visible parameters but use supplies {got}", s, sig.line, severity="warning", confidence="medium"))

    # TSAGDA113: only the high-confidence single-identifier RHS case.
    global_names = set(s.signatures) | set(s.records) | set(data) | set(ctors) | set(imported)
    for name, cs in clauses.items():
        for line, lhs, rhs in cs:
            rm = re.fullmatch(rf"({_IDENT})", rhs)
            if not rm: continue
            ident = rm.group(1)
            lhs_names = set(re.findall(rf"\b({_IDENT})\b", lhs))
            if ident not in lhs_names and ident not in global_names and ident not in {"Set","Nat","Bool","String","refl","tt"}:
                out.append(_diag(D, "TSAGDA113", f"RHS identifier {ident} has no evident local or top-level binding", s, line, severity="warning", confidence="medium"))


    # TSAGDA104: equality proof used as whole RHS for a non-equality target.
    for name, cs in clauses.items():
        sig = s.signatures.get(name)
        if not sig or "≡" in sig.type_text: continue
        for line, lhs, rhs in cs:
            if rhs in eq:
                out.append(_diag(D, "TSAGDA104", f"equality proof {rhs} is used as the value of non-equality result {name}", s, line))

    # TSAGDA113/114/115: bounded clause/scope/signature checks.
    sig_occ = {}
    for i, line in enumerate(lines, 1):
        m = re.match(rf"^({_IDENT})\s*:\s*(.*)$", line)
        if m: sig_occ.setdefault(m.group(1), []).append((i, m.group(2).strip()))
    for name, occ in sig_occ.items():
        if len({t for _, t in occ}) > 1:
            out.append(_diag(D, "TSAGDA115", f"{name} has multiple incompatible top-level signatures", s, occ[-1][0]))
    for name, cs in clauses.items():
        sig = s.signatures.get(name)
        if not sig: continue
        expected = _terminal(sig.type_text)
        for line, lhs, rhs in cs:
            rm = re.match(rf"({_IDENT})\b", rhs)
            if rm and rm.group(1) in ctors and expected and ctors[rm.group(1)].datatype != expected:
                out.append(_diag(D, "TSAGDA114", f"clause result constructor head disagrees with declared result head {expected}", s, line))

    # TSAGDA123: a Set-valued field whose written codomain is a known term declaration.
    known_terms = set(clauses) | set(ctors)
    for rname, rec in s.records.items():
        for fname, fi in rec.fields.items():
            head = _terminal(fi.type_text)
            if head in known_terms and head not in data and head not in s.records:
                out.append(_diag(D, "TSAGDA123", f"projection {rname}.{fname} has known term {head} in type position", s, fi.line))

    # TSAGDA154: ambiguous opened mixfix/operator.
    for n, mods in visible.items():
        if "_" in n and len(set(mods)) > 1:
            out.append(_diag(D, "TSAGDA154", f"operator {n} is provided by multiple open imports", s, 1, severity="warning", confidence="medium"))

    # TSAGDA171/175 aliases for high-value metavariable classes.
    for d in list(out):
        if d.code == "TSAGDA002":
            out.append(_diag(D, "TSAGDA171", d.message, s, d.line, d.column, d.hint))
        if d.code == "TSAGDA012":
            out.append(_diag(D, "TSAGDA175", d.message, s, d.line, d.column, d.hint))

    # TSAGDA185: public re-export collision; TSAGDA186: stale import modifiers.
    public_exports = {}
    for line, is_open, module, alias, directives in import_lines:
        if not is_open or not any(d.kind == "public" for d in directives): continue
        target = imported.get(alias)
        if not target: continue
        names = set(target.signatures) | set(target.records) | {f for r in target.records.values() for f in r.fields}
        for n in names:
            public_exports.setdefault(n, []).append(module)
    for n, mods in public_exports.items():
        if len(set(mods)) > 1:
            out.append(_diag(D, "TSAGDA185", f"public re-export {n} collides across {', '.join(sorted(set(mods)))}", s, 1, severity="warning", confidence="medium"))

    for d in list(out):
        if d.code in {"TSAGDA023", "TSAGDA024", "TSAGDA025"}:
            out.append(_diag(D, "TSAGDA186", f"stale import modifier: {d.message}", s, d.line, d.column, d.hint, severity="warning", confidence="high"))

    # TSAGDA207: explicit forward/backward bidi endpoints should reverse.
    if "Bidi" in s.module_name:
        forward = next((sig for n, sig in s.signatures.items() if re.search(r"(forward|toTarget|encode)", n, re.I)), None)
        backward = next((sig for n, sig in s.signatures.items() if re.search(r"(backward|toSource|decode|inverse)", n, re.I)), None)
        if forward and backward:
            fp = _split_arrows(forward.type_text); bp = _split_arrows(backward.type_text)
            if len(fp) >= 2 and len(bp) >= 2:
                fa, fb, ba, bb = _terminal(fp[0]), _terminal(fp[-1]), _terminal(bp[0]), _terminal(bp[-1])
                if all((fa, fb, ba, bb)) and (fa != bb or fb != ba):
                    out.append(_diag(D, "TSAGDA207", f"bidi forward/backward outer heads are not reversed: {fa}->{fb} versus {ba}->{bb}", s, min(forward.line, backward.line), severity="warning", confidence="medium"))


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
            "projections": {f: rname for rname, r in s.records.items() for f in r.fields},
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
        for proj, old_owner in old.get("projections", {}).items():
            new_owner = cur.get("projections", {}).get(proj)
            if new_owner and new_owner != old_owner:
                out.append(_diag(D, "TSAGDA184", f"projection {proj} moved receiver record {old_owner} -> {new_owner}", s, 1))
    return out
