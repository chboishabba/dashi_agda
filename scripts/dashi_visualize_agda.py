#!/usr/bin/env python3
"""Generic source-backed Agda term-flow visualiser.

The only semantic configuration is a set of fully-qualified root declarations.
All declaration, call, variable-use, local-binding, constructor-field and return
fibres are derived from Agda source.  SVG coordinates are a presentation-only
embedding of the derived term-flow graph.

This source parser is deliberately fail-closed and is not an Agda elaborator.
Every node retains its source text and source location.  Ambiguous references
remain external/unresolved rather than being promoted to resolved proof edges.
The JSON schema is designed so an elaborated Agda reflection exporter can later
replace the parser without changing the renderer.
"""
from __future__ import annotations

import argparse
import html
import json
import re
import textwrap
from collections import defaultdict, deque
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any, Iterable

SCHEMA = "dashi-agda-termflow-v1"
IDENT = r"[^\W\d][\w′″₀-₉-]*"
IDENT_RE = re.compile(IDENT)
QUALIFIED_RE = re.compile(rf"\b(?:{IDENT}\.)+{IDENT}\b")
SIG_RE = re.compile(rf"^({IDENT})\s*:\s*(.*)$")
DEFINITION_HEAD_RE = re.compile(rf"^({IDENT})(?:\s|\(|\{{|$)")
KEYWORDS = {
    "module", "where", "open", "import", "using", "renaming", "hiding",
    "record", "data", "field", "constructor", "let", "in", "with", "rewrite",
    "Set", "Set₁", "Set₂", "forall", "postulate", "primitive", "private", "public",
}
BUILTINS = {
    "refl", "record", "true", "false", "zero", "suc", "λ", "∀", "_", "[]",
}


class VisualisationError(RuntimeError):
    pass


@dataclass(frozen=True)
class SourceRef:
    path: str
    line: int
    end_line: int


@dataclass
class Declaration:
    module: str
    name: str
    path: Path
    line: int
    end_line: int
    signature: str
    body: str
    imports: list[str]
    aliases: dict[str, str]
    postulated: bool = False

    @property
    def fqname(self) -> str:
        return f"{self.module}.{self.name}"


@dataclass(frozen=True)
class Binder:
    id: str
    declaration: str
    name: str
    type_text: str
    implicit: bool
    source: SourceRef


@dataclass
class TermNode:
    id: str
    declaration: str
    kind: str
    label: str
    expression: str
    output: str | None
    source: SourceRef
    called_declarations: list[str] = field(default_factory=list)
    variables_used: list[str] = field(default_factory=list)
    state: str = "derived"


@dataclass(frozen=True)
class Fibre:
    id: str
    source: str
    target: str
    kind: str
    label: str
    evidence: str


def strip_comment(line: str) -> str:
    return line.split("--", 1)[0].rstrip()


def normalise_space(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def parse_imports(lines: list[str]) -> tuple[list[str], dict[str, str]]:
    imports: list[str] = []
    aliases: dict[str, str] = {}
    for raw in lines:
        line = strip_comment(raw).strip()
        m = re.match(r"^(?:open\s+)?import\s+([\w.]+)(?:\s+as\s+(\w+))?", line)
        if not m:
            m = re.match(r"^import\s+([\w.]+)(?:\s+as\s+(\w+))?", line)
        if m:
            module, alias = m.group(1), m.group(2)
            imports.append(module)
            if alias:
                aliases[alias] = module
    return imports, aliases


def parse_agda(path: Path) -> list[Declaration]:
    lines = path.read_text(encoding="utf-8").splitlines()
    module_match = next(
        (m for raw in lines if (m := re.match(r"^\s*module\s+([\w.]+)\s+where", raw))),
        None,
    )
    if module_match is None:
        return []
    module = module_match.group(1)
    imports, aliases = parse_imports(lines)
    declarations: list[Declaration] = []
    postulate_indent: int | None = None
    i = 0
    while i < len(lines):
        raw = lines[i]
        clean = strip_comment(raw)
        text = clean.strip()
        indent = len(raw) - len(raw.lstrip())
        if text in {"postulate", "primitive"}:
            postulate_indent = indent
            i += 1
            continue
        if postulate_indent is not None and text and indent <= postulate_indent:
            postulate_indent = None
        match = SIG_RE.match(text) if indent == 0 or postulate_indent is not None else None
        if not match or match.group(1) in KEYWORDS:
            i += 1
            continue
        name = match.group(1)
        start = i
        sig_parts = [match.group(2)]
        decl_indent = indent
        is_postulated = postulate_indent is not None
        i += 1
        while i < len(lines):
            nxt_raw = lines[i]
            nxt = strip_comment(nxt_raw).strip()
            nxt_indent = len(nxt_raw) - len(nxt_raw.lstrip())
            if not nxt:
                i += 1
                continue
            if is_postulated:
                if nxt_indent == decl_indent and SIG_RE.match(nxt):
                    break
                if nxt_indent <= (postulate_indent or 0):
                    break
                sig_parts.append(nxt)
                i += 1
                continue
            if nxt_indent == 0 and (SIG_RE.match(nxt) or re.match(rf"^{re.escape(name)}(?:\s|\(|\{{|$)", nxt)):
                break
            sig_parts.append(nxt)
            i += 1
        body_parts: list[str] = []
        body_end = i
        if not is_postulated:
            definition = re.compile(rf"^{re.escape(name)}(?:\s|\(|\{{|$)")
            while i < len(lines) and definition.match(strip_comment(lines[i]).strip()):
                while i < len(lines):
                    braw = lines[i]
                    btext = strip_comment(braw).rstrip()
                    bindent = len(braw) - len(braw.lstrip())
                    if btext.strip() and bindent == 0 and SIG_RE.match(btext.strip()):
                        break
                    if btext.strip():
                        body_parts.append(btext)
                    body_end = i + 1
                    i += 1
                if i >= len(lines) or not definition.match(strip_comment(lines[i]).strip()):
                    break
        declarations.append(
            Declaration(
                module=module,
                name=name,
                path=path,
                line=start + 1,
                end_line=max(start + 1, body_end),
                signature=normalise_space(" ".join(sig_parts)),
                body="\n".join(body_parts),
                imports=imports,
                aliases=dict(aliases),
                postulated=is_postulated,
            )
        )
    return declarations


def scan_repo(root: Path) -> dict[str, Declaration]:
    declarations: dict[str, Declaration] = {}
    for path in sorted(root.rglob("*.agda")):
        for declaration in parse_agda(path):
            declarations[declaration.fqname] = declaration
    return declarations


def declaration_indexes(declarations: dict[str, Declaration]) -> tuple[dict[str, list[str]], dict[str, dict[str, str]]]:
    by_short: dict[str, list[str]] = defaultdict(list)
    by_module: dict[str, dict[str, str]] = defaultdict(dict)
    for fqname, declaration in declarations.items():
        by_short[declaration.name].append(fqname)
        by_module[declaration.module][declaration.name] = fqname
    return dict(by_short), dict(by_module)


def resolve_token(
    token: str,
    declaration: Declaration,
    declarations: dict[str, Declaration],
    by_short: dict[str, list[str]],
    by_module: dict[str, dict[str, str]],
) -> str | None:
    if token in declarations:
        return token
    if "." in token:
        head, rest = token.split(".", 1)
        if head in declaration.aliases:
            candidate = f"{declaration.aliases[head]}.{rest}"
            return candidate if candidate in declarations else None
        suffix_matches = [fq for fq in declarations if fq.endswith("." + token)]
        return suffix_matches[0] if len(suffix_matches) == 1 else None
    local = by_module.get(declaration.module, {}).get(token)
    if local:
        return local
    imported = [f"{module}.{token}" for module in declaration.imports if f"{module}.{token}" in declarations]
    if len(imported) == 1:
        return imported[0]
    global_matches = by_short.get(token, [])
    return global_matches[0] if len(global_matches) == 1 else None


def reference_tokens(text: str) -> list[str]:
    qualified = QUALIFIED_RE.findall(text)
    masked = text
    for token in qualified:
        masked = masked.replace(token, " ")
    plain = [t for t in IDENT_RE.findall(masked) if t not in KEYWORDS and t not in BUILTINS]
    return qualified + plain


def resolved_references(
    declaration: Declaration,
    declarations: dict[str, Declaration],
    by_short: dict[str, list[str]],
    by_module: dict[str, dict[str, str]],
) -> list[str]:
    refs: set[str] = set()
    for token in reference_tokens(declaration.signature + "\n" + declaration.body):
        target = resolve_token(token, declaration, declarations, by_short, by_module)
        if target and target != declaration.fqname:
            refs.add(target)
    return sorted(refs)


def split_top_level_arrows(signature: str) -> list[str]:
    parts: list[str] = []
    depth = 0
    start = 0
    i = 0
    while i < len(signature):
        ch = signature[i]
        if ch in "({[":
            depth += 1
        elif ch in ")}]"):
            depth = max(0, depth - 1)
        elif ch == "→" and depth == 0:
            parts.append(signature[start:i].strip())
            start = i + 1
        i += 1
    parts.append(signature[start:].strip())
    return [part for part in parts if part]


def parse_binders(declaration: Declaration, repo_root: Path) -> list[Binder]:
    pieces = split_top_level_arrows(declaration.signature)
    binders: list[Binder] = []
    source = SourceRef(declaration.path.relative_to(repo_root).as_posix(), declaration.line, declaration.end_line)
    counter = 0
    for piece in pieces[:-1]:
        implicit = piece.startswith("{")
        inner = piece.strip("(){} ")
        if ":" in inner:
            left, type_text = inner.split(":", 1)
            names = [n for n in IDENT_RE.findall(left) if n not in KEYWORDS]
        else:
            names = []
            type_text = inner
        for name in names:
            counter += 1
            binders.append(Binder(
                id=f"{slug(declaration.fqname)}--binder-{counter}-{slug(name)}",
                declaration=declaration.fqname,
                name=name,
                type_text=normalise_space(type_text),
                implicit=implicit,
                source=source,
            ))
    return binders


def logical_lines(body: str) -> list[tuple[int, str]]:
    raw_lines = body.splitlines()
    out: list[tuple[int, str]] = []
    buffer: list[str] = []
    start = 0
    depth = 0
    for idx, raw in enumerate(raw_lines):
        stripped = raw.strip()
        if not stripped:
            continue
        if not buffer:
            start = idx
        buffer.append(stripped)
        depth += sum(stripped.count(c) for c in "({[") - sum(stripped.count(c) for c in ")}]")
        continuation = stripped.endswith(("=", "→", "in", "let", "record")) or depth > 0
        if not continuation:
            out.append((start, normalise_space(" ".join(buffer))))
            buffer = []
            depth = 0
    if buffer:
        out.append((start, normalise_space(" ".join(buffer))))
    return out


def classify_expression(text: str) -> tuple[str, str | None, str]:
    clean = text.strip()
    field_match = re.match(r"^;?\s*([\w′″₀-₉-]+)\s*=\s*(.+)$", clean)
    if field_match:
        return "record-field", field_match.group(1), field_match.group(2)
    let_match = re.match(rf"^({IDENT})\s*=\s*(.+)$", clean)
    if let_match:
        return "local-binding", let_match.group(1), let_match.group(2)
    if "record" in clean and "{" in clean:
        return "record-construction", None, clean
    if re.search(r"\btrans\b|\bcong\b|≡", clean):
        return "equality-composition", None, clean
    if "λ" in clean:
        return "lambda", None, clean
    if "with" in clean or "rewrite" in clean:
        return "case-or-rewrite", None, clean
    if clean.endswith("()") or " ()" in clean:
        return "impossible-branch", None, clean
    if "=" in clean:
        left, right = clean.split("=", 1)
        return "definition-clause", normalise_space(left), normalise_space(right)
    return "application", None, clean


def build_term_nodes(
    declaration: Declaration,
    binders: list[Binder],
    declarations: dict[str, Declaration],
    by_short: dict[str, list[str]],
    by_module: dict[str, dict[str, str]],
    repo_root: Path,
    max_nodes: int,
) -> list[TermNode]:
    binder_names = {b.name for b in binders}
    nodes: list[TermNode] = []
    seen: set[tuple[str, str | None, str]] = set()
    for ordinal, (offset, line) in enumerate(logical_lines(declaration.body), 1):
        kind, output, expression = classify_expression(line)
        expression = normalise_space(expression)
        key = (kind, output, expression)
        if key in seen:
            continue
        seen.add(key)
        calls: set[str] = set()
        variables: set[str] = set()
        for token in reference_tokens(expression):
            if token in binder_names:
                variables.add(token)
                continue
            target = resolve_token(token, declaration, declarations, by_short, by_module)
            if target and target != declaration.fqname:
                calls.add(target)
            elif token in binder_names:
                variables.add(token)
        if output:
            variables.discard(output)
        source = SourceRef(
            declaration.path.relative_to(repo_root).as_posix(),
            min(declaration.end_line, declaration.line + offset),
            min(declaration.end_line, declaration.line + offset),
        )
        nodes.append(TermNode(
            id=f"{slug(declaration.fqname)}--term-{ordinal}",
            declaration=declaration.fqname,
            kind=kind,
            label=output or kind,
            expression=expression,
            output=output,
            source=source,
            called_declarations=sorted(calls),
            variables_used=sorted(variables),
            state="open" if declaration.postulated else "derived",
        ))
        if len(nodes) >= max_nodes:
            break
    if not nodes and declaration.postulated:
        source = SourceRef(declaration.path.relative_to(repo_root).as_posix(), declaration.line, declaration.end_line)
        nodes.append(TermNode(
            id=f"{slug(declaration.fqname)}--term-postulate",
            declaration=declaration.fqname,
            kind="postulate",
            label="postulated input",
            expression=declaration.signature,
            output=None,
            source=source,
            state="open",
        ))
    return nodes


def slug(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9]+", "-", value).strip("-").lower()


def declaration_state(declaration: Declaration) -> str:
    if declaration.postulated or not declaration.body:
        return "open"
    if re.search(r"\bfalse\b|\b⊥\b", declaration.body) and re.search(r"Promoted|Available|Condition|Target", declaration.name, re.I):
        return "fail-closed"
    return "defined"


def discover_reachable(
    roots: list[str],
    declarations: dict[str, Declaration],
    by_short: dict[str, list[str]],
    by_module: dict[str, dict[str, str]],
    max_declarations: int,
) -> list[str]:
    missing = [root for root in roots if root not in declarations]
    if missing:
        raise VisualisationError(f"root declarations not found: {missing}")
    queue = deque(roots)
    visited: list[str] = []
    seen: set[str] = set()
    while queue and len(visited) < max_declarations:
        fqname = queue.popleft()
        if fqname in seen:
            continue
        seen.add(fqname)
        visited.append(fqname)
        declaration = declarations[fqname]
        for ref in resolved_references(declaration, declarations, by_short, by_module):
            if ref not in seen:
                queue.append(ref)
    return visited


def build_ir(repo_root: Path, config_path: Path) -> dict[str, Any]:
    config = json.loads(config_path.read_text(encoding="utf-8"))
    if config.get("schema") != SCHEMA:
        raise VisualisationError(f"wrong schema in {config_path}")
    scan_root = repo_root / config.get("scan_root", "DASHI")
    declarations = scan_repo(scan_root)
    by_short, by_module = declaration_indexes(declarations)
    roots = config["roots"]
    selected = discover_reachable(
        roots,
        declarations,
        by_short,
        by_module,
        int(config.get("max_declarations", 32)),
    )
    selected_set = set(selected)
    declaration_rows: list[dict[str, Any]] = []
    binder_rows: list[Binder] = []
    term_rows: list[TermNode] = []
    fibres: list[Fibre] = []
    node_ids: set[str] = set()

    binders_by_decl: dict[str, list[Binder]] = {}
    terms_by_decl: dict[str, list[TermNode]] = {}
    for fqname in selected:
        declaration = declarations[fqname]
        binders = parse_binders(declaration, repo_root)
        terms = build_term_nodes(
            declaration,
            binders,
            declarations,
            by_short,
            by_module,
            repo_root,
            int(config.get("max_term_nodes_per_declaration", 42)),
        )
        binders_by_decl[fqname] = binders
        terms_by_decl[fqname] = terms
        binder_rows.extend(binders)
        term_rows.extend(terms)
        source = SourceRef(declaration.path.relative_to(repo_root).as_posix(), declaration.line, declaration.end_line)
        result_type = split_top_level_arrows(declaration.signature)[-1]
        declaration_rows.append({
            "id": f"decl-{slug(fqname)}",
            "fqname": fqname,
            "name": declaration.name,
            "module": declaration.module,
            "signature": declaration.signature,
            "result_type": result_type,
            "state": declaration_state(declaration),
            "source": asdict(source),
            "is_root": fqname in roots,
            "postulated": declaration.postulated,
        })

    for binder in binder_rows:
        node_ids.add(binder.id)
    for term in term_rows:
        node_ids.add(term.id)
    declaration_node = {row["fqname"]: row["id"] for row in declaration_rows}
    node_ids.update(declaration_node.values())

    for fqname in selected:
        declaration_id = declaration_node[fqname]
        binders = binders_by_decl[fqname]
        terms = terms_by_decl[fqname]
        binder_id = {binder.name: binder.id for binder in binders}
        output_id: dict[str, str] = {}
        for term in terms:
            for variable in term.variables_used:
                source = output_id.get(variable) or binder_id.get(variable)
                if source:
                    fibres.append(Fibre(
                        id=f"fibre-{len(fibres)+1}", source=source, target=term.id,
                        kind="variable-use", label=variable, evidence="binder-or-local-output",
                    ))
            for called in term.called_declarations:
                if called in selected_set:
                    fibres.append(Fibre(
                        id=f"fibre-{len(fibres)+1}", source=declaration_node[called], target=term.id,
                        kind="application", label=declarations[called].name, evidence="resolved-source-reference",
                    ))
            if term.output:
                output_id[term.output] = term.id
        if terms:
            fibres.append(Fibre(
                id=f"fibre-{len(fibres)+1}", source=terms[-1].id, target=declaration_id,
                kind="return", label="result", evidence="final-source-expression",
            ))
        for binder in binders:
            if not any(f.source == binder.id for f in fibres):
                fibres.append(Fibre(
                    id=f"fibre-{len(fibres)+1}", source=binder.id, target=declaration_id,
                    kind="unused-or-type-level", label=binder.name, evidence="signature-binder",
                ))

    return {
        "schema": SCHEMA,
        "title": config["title"],
        "slug": config["slug"],
        "roots": roots,
        "claim_boundary": (
            "Source-derived term flow; source parsing does not replace Agda elaboration. "
            "Open/postulated inputs remain visibly open and no displayed edge upgrades theorem authority."
        ),
        "declarations": declaration_rows,
        "binders": [asdict(row) for row in binder_rows],
        "terms": [asdict(row) for row in term_rows],
        "fibres": [asdict(row) for row in fibres],
        "invariants": {
            "configuration_contains_roots_not_edges": True,
            "all_declarations_resolve_to_agda_source": True,
            "application_edges_are_resolved_source_references": True,
            "variable_fibres_follow_binder_or_local_output_identity": True,
            "node_expressions_are_actual_source_expressions": True,
            "svg_positions_are_not_semantic_inputs": True,
        },
    }


def esc(value: object) -> str:
    return html.escape(str(value), quote=True)


def wrap(text: str, width: int) -> list[str]:
    return textwrap.wrap(normalise_space(text), width=width, break_long_words=False, break_on_hyphens=False) or [""]


def state_colour(state: str) -> str:
    return {
        "defined": "#46D39A",
        "derived": "#62C8FF",
        "open": "#FF6B78",
        "fail-closed": "#F2C14E",
    }.get(state, "#9AB7D5")


def kind_colour(kind: str) -> str:
    return {
        "application": "#62C8FF",
        "local-binding": "#A978F2",
        "record-field": "#55D6BE",
        "record-construction": "#55D6BE",
        "equality-composition": "#F2C14E",
        "definition-clause": "#7DCFFF",
        "lambda": "#C99CFF",
        "case-or-rewrite": "#FF9F68",
        "impossible-branch": "#FF6B78",
        "postulate": "#FF6B78",
    }.get(kind, "#8FB9DB")


def declaration_layers(ir: dict[str, Any]) -> list[list[str]]:
    ids = {row["fqname"] for row in ir["declarations"]}
    incoming = {fq: set() for fq in ids}
    for term in ir["terms"]:
        for called in term["called_declarations"]:
            if called in ids:
                incoming[term["declaration"]].add(called)
    layers: list[list[str]] = []
    remaining = set(ids)
    done: set[str] = set()
    while remaining:
        layer = sorted(fq for fq in remaining if incoming[fq] <= done)
        if not layer:
            layer = sorted(remaining)
        layers.append(layer)
        done.update(layer)
        remaining.difference_update(layer)
    return layers


def render_svg(ir: dict[str, Any]) -> str:
    declarations = {row["fqname"]: row for row in ir["declarations"]}
    binders_by_decl: dict[str, list[dict[str, Any]]] = defaultdict(list)
    terms_by_decl: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for binder in ir["binders"]:
        binders_by_decl[binder["declaration"]].append(binder)
    for term in ir["terms"]:
        terms_by_decl[term["declaration"]].append(term)

    layers = declaration_layers(ir)
    panel_w = 720
    gap_x = 100
    margin = 90
    positions: dict[str, tuple[float, float]] = {}
    panel_heights: dict[str, int] = {}
    max_rows = max(len(layer) for layer in layers)
    for fqname in declarations:
        sig_lines = wrap(declarations[fqname]["signature"], 76)
        term_count = len(terms_by_decl[fqname])
        binder_count = len(binders_by_decl[fqname])
        panel_heights[fqname] = 165 + 17 * len(sig_lines) + 34 * binder_count + 78 * max(1, term_count)
    column_heights: list[int] = []
    for x_idx, layer in enumerate(layers):
        y = 150
        for fqname in layer:
            positions[fqname] = (margin + x_idx * (panel_w + gap_x), y)
            y += panel_heights[fqname] + 100
        column_heights.append(y)
    width = max(1900, margin * 2 + len(layers) * panel_w + max(0, len(layers)-1) * gap_x)
    height = max(1000, max(column_heights, default=900) + 80)

    node_position: dict[str, tuple[float, float]] = {}
    parts: list[str] = [f'''<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="{width}" height="{height}" viewBox="0 0 {width} {height}">
<defs>
 <linearGradient id="bg" x1="0" y1="0" x2="1" y2="1"><stop stop-color="#061321"/><stop offset="1" stop-color="#0A1730"/></linearGradient>
 <pattern id="grid" width="26" height="26" patternUnits="userSpaceOnUse"><path d="M26 0H0V26" fill="none" stroke="#18314E" stroke-width="1" opacity=".35"/></pattern>
 <filter id="glow" x="-80%" y="-80%" width="260%" height="260%"><feGaussianBlur stdDeviation="4" result="b"/><feMerge><feMergeNode in="b"/><feMergeNode in="SourceGraphic"/></feMerge></filter>
 <marker id="arrow" markerWidth="9" markerHeight="9" refX="8" refY="4.5" orient="auto"><path d="M0 0L9 4.5L0 9Z" fill="#D8EDFF"/></marker>
 <style>
 .title{{font:700 36px Inter,Arial,sans-serif;fill:#F2F7FF}} .sub{{font:500 15px Inter,Arial,sans-serif;fill:#9CBBD5}}
 .decl-name{{font:700 20px ui-monospace,SFMono-Regular,monospace;fill:#F2F7FF}} .module{{font:500 12px ui-monospace,monospace;fill:#85A8C8}}
 .sig{{font:500 12px ui-monospace,monospace;fill:#D7E9FA}} .label{{font:700 12px Inter,Arial,sans-serif;fill:#EAF5FF}}
 .formula{{font:500 12px ui-monospace,monospace;fill:#D7E9FA}} .meta{{font:500 10px ui-monospace,monospace;fill:#87A7C4}}
 .panel{{fill:#0B1E35;stroke:#2E5C84;stroke-width:1.6}} .binder{{fill:#112945;stroke:#5D86AB;stroke-width:1.1}}
 .term{{fill:#0D243E;stroke-width:1.5}} .fibre{{fill:none;stroke-linecap:round;opacity:.82;stroke-dasharray:9 7;animation:flow 10s linear infinite}}
 .math-note{{font:600 11px Inter,Arial,sans-serif;fill:#8FBCD9}} @keyframes flow{{to{{stroke-dashoffset:-64}}}}
 </style>
</defs>
<rect width="100%" height="100%" fill="url(#bg)"/><rect width="100%" height="100%" fill="url(#grid)"/>
<text x="70" y="55" class="title">{esc(ir['title'])}</text>
<text x="70" y="84" class="sub">Root-driven Agda term flow: variables are fibres; applications, constructors and equality chains are operator junctions.</text>
<text x="70" y="108" class="sub">Every formula shown inside a node is normalised directly from its Agda source expression.</text>''']

    for fqname, declaration in declarations.items():
        x, y = positions[fqname]
        h = panel_heights[fqname]
        colour = state_colour(declaration["state"])
        parts.append(f'<g id="{esc(declaration["id"])}"><rect class="panel" x="{x}" y="{y}" width="{panel_w}" height="{h}" rx="18"/>')
        parts.append(f'<rect x="{x}" y="{y}" width="8" height="{h}" rx="4" fill="{colour}"/>')
        parts.append(f'<text x="{x+24}" y="{y+30}" class="decl-name">{esc(declaration["name"])}</text>')
        parts.append(f'<text x="{x+24}" y="{y+51}" class="module">{esc(declaration["module"])}</text>')
        parts.append(f'<text x="{x+24}" y="{y+70}" class="meta">{esc(declaration["source"]["path"])}:{declaration["source"]["line"]} · {esc(declaration["state"])}</text>')
        cursor = y + 94
        parts.append(f'<text x="{x+24}" y="{cursor}" class="math-note">TYPE / MATHEMATICAL MAP</text>')
        cursor += 18
        for line in wrap(declaration["signature"], 76):
            parts.append(f'<text x="{x+24}" y="{cursor}" class="sig">{esc(line)}</text>')
            cursor += 17
        cursor += 8
        for binder in binders_by_decl[fqname]:
            bx = x + 24
            by = cursor
            bw = 230
            bh = 27
            node_position[binder["id"]] = (bx + bw, by + bh/2)
            parts.append(f'<rect class="binder" x="{bx}" y="{by}" width="{bw}" height="{bh}" rx="8"/>')
            parts.append(f'<text x="{bx+10}" y="{by+18}" class="formula">{esc(binder["name"])} : {esc(binder["type_text"])}</text>')
            cursor += 34
        for term in terms_by_decl[fqname] or [{
            "id": declaration["id"]+"-empty", "kind":"application", "label":"definition", "expression":"(no parsed body expression)",
            "source":declaration["source"], "state":declaration["state"]
        }]:
            tx = x + 285
            ty = cursor
            tw = panel_w - 310
            expr_lines = wrap(term["expression"], 54)[:4]
            th = 43 + len(expr_lines) * 16
            node_position[term["id"]] = (tx, ty + th/2)
            tcolour = kind_colour(term["kind"])
            parts.append(f'<rect class="term" x="{tx}" y="{ty}" width="{tw}" height="{th}" rx="11" stroke="{tcolour}"/>')
            parts.append(f'<text x="{tx+12}" y="{ty+18}" class="label">{esc(term["kind"])} · {esc(term["label"])}</text>')
            ly = ty + 38
            for line in expr_lines:
                parts.append(f'<text x="{tx+12}" y="{ly}" class="formula">{esc(line)}</text>')
                ly += 16
            parts.append(f'<text x="{tx+12}" y="{ty+th-8}" class="meta">source line {term["source"]["line"]}</text>')
            cursor += th + 12
        node_position[declaration["id"]] = (x + panel_w, y + 32)
        parts.append('</g>')

    # Draw fibres after panels so paths remain visible; endpoint circles animate transport.
    fibre_parts: list[str] = ['<g id="fibres">']
    for index, fibre in enumerate(ir["fibres"]):
        if fibre["source"] not in node_position or fibre["target"] not in node_position:
            continue
        sx, sy = node_position[fibre["source"]]
        tx, ty = node_position[fibre["target"]]
        if tx >= sx:
            c1x, c2x = sx + max(45, (tx-sx)*.35), tx - max(45, (tx-sx)*.35)
        else:
            c1x, c2x = sx + 80, tx - 80
        d = f"M{sx:.1f},{sy:.1f} C{c1x:.1f},{sy:.1f} {c2x:.1f},{ty:.1f} {tx:.1f},{ty:.1f}"
        colour = {"variable-use":"#A978F2", "application":"#62C8FF", "return":"#46D39A", "unused-or-type-level":"#7F93A8"}.get(fibre["kind"], "#8FB9DB")
        path_id = f"path-{index}"
        fibre_parts.append(f'<path id="{path_id}" class="fibre" d="{d}" stroke="{colour}" stroke-width="{2.2 if fibre["kind"] == "variable-use" else 2.8}" marker-end="url(#arrow)"/>')
        fibre_parts.append(f'<text class="meta"><textPath href="#{path_id}" startOffset="48%">{esc(fibre["label"])}</textPath></text>')
        fibre_parts.append(f'<circle r="3.4" fill="{colour}" filter="url(#glow)"><animateMotion dur="{6.5 + (index % 5)}s" begin="{(index % 7)*.35}s" repeatCount="indefinite"><mpath href="#{path_id}"/></animateMotion></circle>')
    fibre_parts.append('</g>')
    parts.extend(fibre_parts)
    parts.append(f'<text x="70" y="{height-35}" class="sub">{esc(ir["claim_boundary"])}</text>')
    parts.append('</svg>')
    return "\n".join(parts)


def write_outputs(ir: dict[str, Any], config: dict[str, Any], repo_root: Path) -> tuple[Path, Path]:
    json_path = repo_root / config["output_json"]
    svg_path = repo_root / config["output_svg"]
    json_path.parent.mkdir(parents=True, exist_ok=True)
    svg_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(ir, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    svg_path.write_text(render_svg(ir), encoding="utf-8")
    return json_path, svg_path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    repo_root = args.repo_root.resolve()
    config_path = args.config if args.config.is_absolute() else repo_root / args.config
    config = json.loads(config_path.read_text(encoding="utf-8"))
    ir = build_ir(repo_root, config_path)
    if args.check:
        if not ir["declarations"]:
            raise VisualisationError("no declarations discovered")
        if not ir["terms"]:
            raise VisualisationError("no term-flow nodes discovered")
        if any(root not in {row["fqname"] for row in ir["declarations"]} for root in ir["roots"]):
            raise VisualisationError("not all roots present in IR")
        print(f"validated {len(ir['declarations'])} declarations, {len(ir['terms'])} terms, {len(ir['fibres'])} fibres")
        return 0
    json_path, svg_path = write_outputs(ir, config, repo_root)
    print(json_path.relative_to(repo_root))
    print(svg_path.relative_to(repo_root))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
