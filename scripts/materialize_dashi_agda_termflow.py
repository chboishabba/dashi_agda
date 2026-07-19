#!/usr/bin/env python3
"""Generate animated SVGs from roots in arbitrary Agda source.

Configuration names root declarations and rendering limits only. Reachable
functions, bound variables, local equations, record fields, theorem calls and
returns are derived from source. Each operator node prints the source expression
it represents. This parser is conservative and does not replace Agda elaboration.
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
from typing import Any

from materialize_dashi_lane_hyperfabric import Declaration, scan_repo

SCHEMA = "dashi-agda-termflow-v1"
IDENT = r"[^\W\d][\w′″₀-₉-]*"
IDENT_RE = re.compile(IDENT)
QUALIFIED_RE = re.compile(rf"\b(?:{IDENT}\.)+{IDENT}\b")
KEYWORDS = {
    "module", "where", "open", "import", "using", "renaming", "hiding",
    "record", "data", "field", "constructor", "let", "in", "with", "rewrite",
    "Set", "Set₁", "Set₂", "postulate", "primitive", "private", "public",
    "true", "false", "zero", "suc", "refl",
}


class TermFlowError(RuntimeError):
    pass


@dataclass(frozen=True)
class SourceRef:
    path: str
    line: int
    end_line: int


@dataclass(frozen=True)
class Binder:
    id: str
    declaration: str
    name: str
    type_text: str
    implicit: bool
    source: SourceRef


@dataclass
class Term:
    id: str
    declaration: str
    kind: str
    label: str
    expression: str
    output: str | None
    source: SourceRef
    calls: list[str] = field(default_factory=list)
    variables: list[str] = field(default_factory=list)


@dataclass(frozen=True)
class Fibre:
    id: str
    source: str
    target: str
    kind: str
    label: str
    evidence: str


def slug(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9]+", "-", value).strip("-").lower()


def norm(value: str) -> str:
    return re.sub(r"\s+", " ", value).strip()


def esc(value: object) -> str:
    return html.escape(str(value), quote=True)


def wrap(value: str, width: int) -> list[str]:
    return textwrap.wrap(norm(value), width=width, break_long_words=False, break_on_hyphens=False) or [""]


def make_indexes(declarations: dict[str, Declaration]) -> tuple[dict[str, list[str]], dict[str, dict[str, str]]]:
    by_short: dict[str, list[str]] = defaultdict(list)
    by_module: dict[str, dict[str, str]] = defaultdict(dict)
    for fqname, declaration in declarations.items():
        by_short[declaration.name].append(fqname)
        by_module[declaration.module][declaration.name] = fqname
    return dict(by_short), dict(by_module)


def aliases_for(declaration: Declaration) -> dict[str, str]:
    aliases: dict[str, str] = {}
    source = declaration.path.read_text(encoding="utf-8")
    for match in re.finditer(r"^\s*import\s+([\w.]+)\s+as\s+(\w+)", source, re.MULTILINE):
        aliases[match.group(2)] = match.group(1)
    return aliases


def source_tokens(text: str) -> list[str]:
    qualified = QUALIFIED_RE.findall(text)
    masked = text
    for token in qualified:
        masked = masked.replace(token, " ")
    plain = [token for token in IDENT_RE.findall(masked) if token not in KEYWORDS]
    return qualified + plain


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
        head, tail = token.split(".", 1)
        aliases = aliases_for(declaration)
        if head in aliases:
            candidate = f"{aliases[head]}.{tail}"
            return candidate if candidate in declarations else None
        matches = [fqname for fqname in declarations if fqname.endswith("." + token)]
        return matches[0] if len(matches) == 1 else None
    local = by_module.get(declaration.module, {}).get(token)
    if local:
        return local
    imported = [f"{module}.{token}" for module in declaration.imports if f"{module}.{token}" in declarations]
    if len(imported) == 1:
        return imported[0]
    matches = by_short.get(token, [])
    return matches[0] if len(matches) == 1 else None


def resolved_references(
    declaration: Declaration,
    declarations: dict[str, Declaration],
    by_short: dict[str, list[str]],
    by_module: dict[str, dict[str, str]],
) -> list[str]:
    refs: set[str] = set()
    for token in source_tokens(declaration.signature + "\n" + declaration.body):
        target = resolve_token(token, declaration, declarations, by_short, by_module)
        if target and target != declaration.fqname:
            refs.add(target)
    return sorted(refs)


def split_arrows(signature: str) -> list[str]:
    parts: list[str] = []
    depth = 0
    start = 0
    closing = set(")}]")
    for index, char in enumerate(signature):
        if char in "({[":
            depth += 1
        elif char in closing:
            depth = max(0, depth - 1)
        elif char == "→" and depth == 0:
            parts.append(signature[start:index].strip())
            start = index + 1
    parts.append(signature[start:].strip())
    return [part for part in parts if part]


def binders_for(declaration: Declaration, repo_root: Path) -> list[Binder]:
    source = SourceRef(declaration.path.relative_to(repo_root).as_posix(), declaration.line, declaration.line)
    rows: list[Binder] = []
    ordinal = 0
    for piece in split_arrows(declaration.signature)[:-1]:
        implicit = piece.startswith("{")
        inner = piece.strip("(){} ")
        if ":" not in inner:
            continue
        names_text, type_text = inner.split(":", 1)
        for name in IDENT_RE.findall(names_text):
            if name in KEYWORDS:
                continue
            ordinal += 1
            rows.append(Binder(
                id=f"{slug(declaration.fqname)}-binder-{ordinal}-{slug(name)}",
                declaration=declaration.fqname,
                name=name,
                type_text=norm(type_text),
                implicit=implicit,
                source=source,
            ))
    return rows


def logical_lines(body: str) -> list[tuple[int, str]]:
    rows: list[tuple[int, str]] = []
    buffer: list[str] = []
    start = 0
    depth = 0
    for offset, raw in enumerate(body.splitlines()):
        line = raw.strip()
        if not line:
            continue
        if not buffer:
            start = offset
        buffer.append(line)
        depth += sum(line.count(char) for char in "({[")
        depth -= sum(line.count(char) for char in ")}]")
        if depth <= 0 and not line.endswith(("=", "→", "let", "in", "record")):
            rows.append((start, norm(" ".join(buffer))))
            buffer = []
            depth = 0
    if buffer:
        rows.append((start, norm(" ".join(buffer))))
    return rows


def classify(line: str) -> tuple[str, str | None, str]:
    match = re.match(rf"^;?\s*({IDENT})\s*=\s*(.+)$", line)
    if match:
        kind = "record-field" if line.lstrip().startswith(";") else "local-binding"
        return kind, match.group(1), match.group(2)
    if "record" in line and "{" in line:
        return "record-construction", None, line
    if re.search(r"\btrans\b|\bcong\b|≡", line):
        return "equality-composition", None, line
    if "λ" in line:
        return "lambda", None, line
    if "with" in line or "rewrite" in line:
        return "case-or-rewrite", None, line
    if " ()" in line or line.endswith("()"):
        return "impossible-branch", None, line
    if "=" in line:
        left, right = line.split("=", 1)
        return "definition-clause", norm(left), norm(right)
    return "application", None, line


def terms_for(
    declaration: Declaration,
    binders: list[Binder],
    declarations: dict[str, Declaration],
    by_short: dict[str, list[str]],
    by_module: dict[str, dict[str, str]],
    repo_root: Path,
    limit: int,
) -> list[Term]:
    binder_names = {binder.name for binder in binders}
    rows: list[Term] = []
    seen: set[tuple[str, str | None, str]] = set()
    for ordinal, (offset, line) in enumerate(logical_lines(declaration.body), 1):
        kind, output, expression = classify(line)
        expression = norm(expression)
        key = (kind, output, expression)
        if key in seen:
            continue
        seen.add(key)
        calls: set[str] = set()
        variables: set[str] = set()
        for token in source_tokens(expression):
            if token in binder_names:
                variables.add(token)
                continue
            target = resolve_token(token, declaration, declarations, by_short, by_module)
            if target and target != declaration.fqname:
                calls.add(target)
        source_line = min(declaration.end_line, declaration.line + offset)
        rows.append(Term(
            id=f"{slug(declaration.fqname)}-term-{ordinal}",
            declaration=declaration.fqname,
            kind=kind,
            label=output or kind,
            expression=expression,
            output=output,
            source=SourceRef(declaration.path.relative_to(repo_root).as_posix(), source_line, source_line),
            calls=sorted(calls),
            variables=sorted(variables),
        ))
        if len(rows) >= limit:
            break
    if not rows and (declaration.postulated or not declaration.body):
        rows.append(Term(
            id=f"{slug(declaration.fqname)}-open",
            declaration=declaration.fqname,
            kind="postulate-or-open",
            label="open input",
            expression=declaration.signature,
            output=None,
            source=SourceRef(declaration.path.relative_to(repo_root).as_posix(), declaration.line, declaration.end_line),
        ))
    return rows


def discover(
    roots: list[str],
    declarations: dict[str, Declaration],
    by_short: dict[str, list[str]],
    by_module: dict[str, dict[str, str]],
    limit: int,
) -> list[str]:
    missing = [root for root in roots if root not in declarations]
    if missing:
        raise TermFlowError(f"root declarations not found: {missing}")
    queue = deque(roots)
    seen: set[str] = set()
    ordered: list[str] = []
    while queue and len(ordered) < limit:
        fqname = queue.popleft()
        if fqname in seen:
            continue
        seen.add(fqname)
        ordered.append(fqname)
        for target in resolved_references(declarations[fqname], declarations, by_short, by_module):
            if target not in seen:
                queue.append(target)
    return ordered


def declaration_state(declaration: Declaration) -> str:
    if declaration.postulated or not declaration.body:
        return "open"
    if "false" in declaration.body and re.search(r"Promoted|Available|Condition|Target", declaration.name, re.I):
        return "fail-closed"
    return "defined"


def build_ir(repo_root: Path, config_path: Path) -> dict[str, Any]:
    config = json.loads(config_path.read_text(encoding="utf-8"))
    if config.get("schema") != SCHEMA:
        raise TermFlowError(f"wrong schema in {config_path}")
    declarations = scan_repo(repo_root / config.get("scan_root", "DASHI"))
    by_short, by_module = make_indexes(declarations)
    selected = discover(
        config["roots"], declarations, by_short, by_module,
        int(config.get("max_declarations", 36)),
    )
    selected_set = set(selected)
    declaration_rows: list[dict[str, Any]] = []
    all_binders: list[Binder] = []
    all_terms: list[Term] = []
    binders_by_decl: dict[str, list[Binder]] = {}
    terms_by_decl: dict[str, list[Term]] = {}

    for fqname in selected:
        declaration = declarations[fqname]
        binders = binders_for(declaration, repo_root)
        terms = terms_for(
            declaration, binders, declarations, by_short, by_module, repo_root,
            int(config.get("max_term_nodes_per_declaration", 48)),
        )
        binders_by_decl[fqname] = binders
        terms_by_decl[fqname] = terms
        all_binders.extend(binders)
        all_terms.extend(terms)
        declaration_rows.append({
            "id": f"decl-{slug(fqname)}",
            "fqname": fqname,
            "name": declaration.name,
            "module": declaration.module,
            "signature": declaration.signature,
            "result_type": split_arrows(declaration.signature)[-1],
            "state": declaration_state(declaration),
            "source": asdict(SourceRef(
                declaration.path.relative_to(repo_root).as_posix(), declaration.line, declaration.end_line
            )),
            "is_root": fqname in config["roots"],
        })

    declaration_ids = {row["fqname"]: row["id"] for row in declaration_rows}
    fibres: list[Fibre] = []
    for fqname in selected:
        binder_ids = {binder.name: binder.id for binder in binders_by_decl[fqname]}
        local_outputs: dict[str, str] = {}
        terms = terms_by_decl[fqname]
        for term in terms:
            for variable in term.variables:
                source = local_outputs.get(variable) or binder_ids.get(variable)
                if source:
                    fibres.append(Fibre(
                        id=f"fibre-{len(fibres)+1}", source=source, target=term.id,
                        kind="variable-use", label=variable, evidence="binder-or-local-output",
                    ))
            for call in term.calls:
                if call in selected_set:
                    fibres.append(Fibre(
                        id=f"fibre-{len(fibres)+1}", source=declaration_ids[call], target=term.id,
                        kind="function-application", label=declarations[call].name,
                        evidence="resolved-Agda-source-reference",
                    ))
            if term.output:
                local_outputs[term.output] = term.id
        if terms:
            fibres.append(Fibre(
                id=f"fibre-{len(fibres)+1}", source=terms[-1].id, target=declaration_ids[fqname],
                kind="return", label="result", evidence="final-source-expression",
            ))

    return {
        "schema": SCHEMA,
        "title": config["title"],
        "slug": config["slug"],
        "roots": config["roots"],
        "declarations": declaration_rows,
        "binders": [asdict(row) for row in all_binders],
        "terms": [asdict(row) for row in all_terms],
        "fibres": [asdict(row) for row in fibres],
        "claim_boundary": (
            "Source-derived term flow; source parsing does not replace Agda elaboration. "
            "Open inputs remain open and no visual edge upgrades theorem authority."
        ),
        "invariants": {
            "configuration_contains_roots_not_edges": True,
            "all_declarations_resolve_to_Agda_source": True,
            "operator_nodes_display_actual_source_expressions": True,
            "variable_fibres_preserve_binder_identity": True,
            "call_fibres_are_resolved_source_references": True,
            "layout_coordinates_are_not_semantic_inputs": True,
        },
    }


def state_colour(state: str) -> str:
    return {"defined": "#46D39A", "open": "#FF6B78", "fail-closed": "#F2C14E"}.get(state, "#91B4D4")


def kind_colour(kind: str) -> str:
    return {
        "application": "#62C8FF", "local-binding": "#A978F2",
        "record-field": "#55D6BE", "record-construction": "#55D6BE",
        "equality-composition": "#F2C14E", "definition-clause": "#7DCFFF",
        "lambda": "#C99CFF", "case-or-rewrite": "#FF9F68",
        "impossible-branch": "#FF6B78", "postulate-or-open": "#FF6B78",
    }.get(kind, "#8FB9DB")


def declaration_layers(ir: dict[str, Any]) -> list[list[str]]:
    ids = {row["fqname"] for row in ir["declarations"]}
    incoming = {fqname: set() for fqname in ids}
    for term in ir["terms"]:
        for call in term["calls"]:
            if call in ids:
                incoming[term["declaration"]].add(call)
    remaining = set(ids)
    done: set[str] = set()
    result: list[list[str]] = []
    while remaining:
        layer = sorted(fqname for fqname in remaining if incoming[fqname] <= done)
        if not layer:
            layer = sorted(remaining)
        result.append(layer)
        done.update(layer)
        remaining.difference_update(layer)
    return result


def render_svg(ir: dict[str, Any]) -> str:
    declarations = {row["fqname"]: row for row in ir["declarations"]}
    binders: dict[str, list[dict[str, Any]]] = defaultdict(list)
    terms: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for binder in ir["binders"]:
        binders[binder["declaration"]].append(binder)
    for term in ir["terms"]:
        terms[term["declaration"]].append(term)

    panel_width = 700
    gap = 100
    margin = 80
    layers = declaration_layers(ir)
    heights: dict[str, int] = {}
    for fqname, declaration in declarations.items():
        heights[fqname] = (
            150 + 17 * len(wrap(declaration["signature"], 74))
            + 34 * len(binders[fqname])
            + sum(60 + 16 * min(4, len(wrap(term["expression"], 52))) for term in terms[fqname])
        )
    positions: dict[str, tuple[float, float]] = {}
    column_bottoms: list[int] = []
    for column, layer in enumerate(layers):
        y = 145
        for fqname in layer:
            positions[fqname] = (margin + column * (panel_width + gap), y)
            y += heights[fqname] + 85
        column_bottoms.append(y)
    width = max(1800, margin * 2 + len(layers) * panel_width + max(0, len(layers)-1) * gap)
    height = max(950, max(column_bottoms, default=850) + 60)
    node_positions: dict[str, tuple[float, float]] = {}

    parts = [f'''<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="{width}" height="{height}" viewBox="0 0 {width} {height}">
<defs>
 <linearGradient id="bg" x1="0" y1="0" x2="1" y2="1"><stop stop-color="#061321"/><stop offset="1" stop-color="#0A1730"/></linearGradient>
 <pattern id="grid" width="26" height="26" patternUnits="userSpaceOnUse"><path d="M26 0H0V26" fill="none" stroke="#18314E" stroke-width="1" opacity=".35"/></pattern>
 <filter id="glow" x="-80%" y="-80%" width="260%" height="260%"><feGaussianBlur stdDeviation="4" result="b"/><feMerge><feMergeNode in="b"/><feMergeNode in="SourceGraphic"/></feMerge></filter>
 <marker id="arrow" markerWidth="9" markerHeight="9" refX="8" refY="4.5" orient="auto"><path d="M0 0L9 4.5L0 9Z" fill="#D8EDFF"/></marker>
 <style>
 .title{{font:700 35px Inter,Arial,sans-serif;fill:#F2F7FF}} .sub{{font:500 14px Inter,Arial,sans-serif;fill:#9CBBD5}}
 .decl{{font:700 19px ui-monospace,monospace;fill:#F2F7FF}} .module{{font:500 11px ui-monospace,monospace;fill:#85A8C8}}
 .signature{{font:500 11px ui-monospace,monospace;fill:#D7E9FA}} .label{{font:700 11px Inter,Arial,sans-serif;fill:#EAF5FF}}
 .formula{{font:500 11px ui-monospace,monospace;fill:#D7E9FA}} .meta{{font:500 9px ui-monospace,monospace;fill:#87A7C4}}
 .panel{{fill:#0B1E35;stroke:#2E5C84;stroke-width:1.5}} .binder{{fill:#112945;stroke:#5D86AB;stroke-width:1}}
 .term{{fill:#0D243E;stroke-width:1.4}} .fibre{{fill:none;stroke-linecap:round;opacity:.8;stroke-dasharray:9 7;animation:flow 10s linear infinite}}
 @keyframes flow{{to{{stroke-dashoffset:-64}}}}
 </style>
</defs>
<rect width="100%" height="100%" fill="url(#bg)"/><rect width="100%" height="100%" fill="url(#grid)"/>
<text x="65" y="50" class="title">{esc(ir['title'])}</text>
<text x="65" y="77" class="sub">Variables are fibres. Function applications, record fields, constructors and equality chains are operator junctions.</text>
<text x="65" y="99" class="sub">Each mathematical expression printed inside a node is taken directly from its Agda source.</text>''']

    for fqname, declaration in declarations.items():
        x, y = positions[fqname]
        panel_height = heights[fqname]
        colour = state_colour(declaration["state"])
        parts.append(f'<rect class="panel" x="{x}" y="{y}" width="{panel_width}" height="{panel_height}" rx="17"/>')
        parts.append(f'<rect x="{x}" y="{y}" width="7" height="{panel_height}" rx="4" fill="{colour}"/>')
        parts.append(f'<text x="{x+22}" y="{y+28}" class="decl">{esc(declaration["name"])}</text>')
        parts.append(f'<text x="{x+22}" y="{y+48}" class="module">{esc(declaration["module"])}</text>')
        parts.append(f'<text x="{x+22}" y="{y+65}" class="meta">{esc(declaration["source"]["path"])}:{declaration["source"]["line"]} · {esc(declaration["state"])}</text>')
        cursor = y + 88
        parts.append(f'<text x="{x+22}" y="{cursor}" class="label">TYPE / MATHEMATICAL MAP</text>')
        cursor += 17
        for line in wrap(declaration["signature"], 74):
            parts.append(f'<text x="{x+22}" y="{cursor}" class="signature">{esc(line)}</text>')
            cursor += 17
        cursor += 8
        for binder in binders[fqname]:
            bx, by, bw, bh = x + 22, cursor, 235, 26
            node_positions[binder["id"]] = (bx + bw, by + bh/2)
            parts.append(f'<rect class="binder" x="{bx}" y="{by}" width="{bw}" height="{bh}" rx="7"/>')
            parts.append(f'<text x="{bx+9}" y="{by+17}" class="formula">{esc(binder["name"])} : {esc(binder["type_text"])}</text>')
            cursor += 34
        for term in terms[fqname]:
            tx, ty, tw = x + 280, cursor, panel_width - 305
            expression_lines = wrap(term["expression"], 52)[:4]
            th = 43 + 16 * len(expression_lines)
            node_positions[term["id"]] = (tx, ty + th/2)
            tcolour = kind_colour(term["kind"])
            parts.append(f'<rect class="term" x="{tx}" y="{ty}" width="{tw}" height="{th}" rx="10" stroke="{tcolour}"/>')
            parts.append(f'<text x="{tx+11}" y="{ty+17}" class="label">{esc(term["kind"])} · {esc(term["label"])}</text>')
            line_y = ty + 36
            for line in expression_lines:
                parts.append(f'<text x="{tx+11}" y="{line_y}" class="formula">{esc(line)}</text>')
                line_y += 16
            parts.append(f'<text x="{tx+11}" y="{ty+th-7}" class="meta">source line {term["source"]["line"]}</text>')
            cursor += th + 12
        node_positions[declaration["id"]] = (x + panel_width, y + 30)

    parts.append('<g id="fibres">')
    for index, fibre in enumerate(ir["fibres"]):
        if fibre["source"] not in node_positions or fibre["target"] not in node_positions:
            continue
        sx, sy = node_positions[fibre["source"]]
        tx, ty = node_positions[fibre["target"]]
        c1x = sx + max(45, abs(tx-sx) * .32)
        c2x = tx - max(45, abs(tx-sx) * .32)
        path = f"M{sx:.1f},{sy:.1f} C{c1x:.1f},{sy:.1f} {c2x:.1f},{ty:.1f} {tx:.1f},{ty:.1f}"
        colour = {"variable-use":"#A978F2", "function-application":"#62C8FF", "return":"#46D39A"}.get(fibre["kind"], "#8FB9DB")
        path_id = f"flow-{index}"
        parts.append(f'<path id="{path_id}" class="fibre" d="{path}" stroke="{colour}" stroke-width="2.4" marker-end="url(#arrow)"/>')
        parts.append(f'<text class="meta"><textPath href="#{path_id}" startOffset="45%">{esc(fibre["label"])}</textPath></text>')
        parts.append(f'<circle r="3.2" fill="{colour}" filter="url(#glow)"><animateMotion dur="{6.5 + index % 5}s" begin="{(index % 7)*.3}s" repeatCount="indefinite"><mpath href="#{path_id}"/></animateMotion></circle>')
    parts.append('</g>')
    parts.append(f'<text x="65" y="{height-28}" class="sub">{esc(ir["claim_boundary"])}</text>')
    parts.append('</svg>')
    return "\n".join(parts)


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
        if not ir["declarations"] or not ir["terms"]:
            raise TermFlowError("term-flow extraction produced no declarations or terms")
        roots = {row["fqname"] for row in ir["declarations"]}
        if not all(root in roots for root in ir["roots"]):
            raise TermFlowError("not all requested roots reached the IR")
        print(f"validated {len(ir['declarations'])} declarations, {len(ir['terms'])} operator nodes, {len(ir['fibres'])} fibres")
        return 0
    json_path = repo_root / config["output_json"]
    svg_path = repo_root / config["output_svg"]
    json_path.parent.mkdir(parents=True, exist_ok=True)
    svg_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(ir, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    svg_path.write_text(render_svg(ir), encoding="utf-8")
    print(json_path.relative_to(repo_root))
    print(svg_path.relative_to(repo_root))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
