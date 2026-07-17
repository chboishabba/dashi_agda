#!/usr/bin/env python3
"""Generate animated proof-lane hyperfabrics from source-backed DASHI declarations.

The configuration selects declarations and may name an intended critical-path edge.
Every rendered carrier must resolve to an Agda declaration. Dependency topology is
computed from declaration references plus the explicit critical-path edges already
used by the theory-atlas configuration. SVG coordinates are only an embedding of
that graph; split/merge topology comes from graph out-degree/in-degree.
"""
from __future__ import annotations

import argparse
import html
import json
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

SCHEMA = "dashi-lane-hyperfabric-v1"


class LaneError(RuntimeError):
    pass


@dataclass(frozen=True)
class SourceRef:
    path: str
    declaration: str
    line: int


@dataclass
class Carrier:
    id: str
    declaration: str
    name: str
    title: str
    lane: str
    state: str
    signature: str
    source: SourceRef
    external_refs: list[str]


@dataclass(frozen=True)
class Transport:
    id: str
    source: str
    target: str
    kind: str
    evidence: str


@dataclass
class Declaration:
    module: str
    name: str
    path: Path
    line: int
    signature: str
    body: str
    imports: list[str]
    postulated: bool = False

    @property
    def fqname(self) -> str:
        return f"{self.module}.{self.name}"

    @property
    def tokens(self) -> set[str]:
        return set(re.findall(r"[^\W\d][\w′″₀-₉-]*", self.signature + "\n" + self.body))


def parse_agda(path: Path) -> list[Declaration]:
    lines = path.read_text(encoding="utf-8").splitlines()
    module_match = next((re.match(r"^\s*module\s+([\w.]+)\s+where", line) for line in lines if re.match(r"^\s*module\s+([\w.]+)\s+where", line)), None)
    if not module_match:
        return []
    module = module_match.group(1)
    imports = [m.group(1) for line in lines if (m := re.match(r"^\s*(?:open\s+)?import\s+([\w.]+)", line))]
    sig_re = re.compile(r"^([^\W\d][\w′″₀-₉-]*)\s*:\s*(.*)$")
    out: list[Declaration] = []
    post_indent: int | None = None
    i = 0
    while i < len(lines):
        raw = lines[i]
        clean = raw.split("--", 1)[0].rstrip()
        text = clean.strip()
        indent = len(raw) - len(raw.lstrip())
        if text in {"postulate", "primitive"}:
            post_indent = indent
            i += 1
            continue
        if post_indent is not None and text and indent <= post_indent:
            post_indent = None
        match = sig_re.match(text) if indent == 0 or post_indent is not None else None
        if not match or match.group(1) in {"module", "open", "import", "record", "data", "field"}:
            i += 1
            continue
        name = match.group(1)
        line_no = i + 1
        signature = [match.group(2)]
        decl_indent = indent
        is_postulated = post_indent is not None
        i += 1
        while i < len(lines):
            nxt_raw = lines[i]
            nxt = nxt_raw.split("--", 1)[0].rstrip().strip()
            nxt_indent = len(nxt_raw) - len(nxt_raw.lstrip())
            if not nxt:
                i += 1
                continue
            if is_postulated:
                if nxt_indent == decl_indent and sig_re.match(nxt):
                    break
                if nxt_indent <= (post_indent or 0):
                    break
                signature.append(nxt)
                i += 1
                continue
            if nxt_indent == 0 and (sig_re.match(nxt) or re.match(rf"^{re.escape(name)}(?:\s|\(|\{{|$)", nxt)):
                break
            signature.append(nxt)
            i += 1
        body: list[str] = []
        if not is_postulated:
            definition = re.compile(rf"^{re.escape(name)}(?:\s|\(|\{{|$)")
            while i < len(lines) and definition.match(lines[i].split("--", 1)[0].rstrip().strip()):
                while i < len(lines):
                    braw = lines[i]
                    btext = braw.split("--", 1)[0].rstrip().strip()
                    bindent = len(braw) - len(braw.lstrip())
                    if btext and bindent == 0 and sig_re.match(btext):
                        break
                    if btext:
                        body.append(btext)
                    i += 1
                if i >= len(lines) or not definition.match(lines[i].split("--", 1)[0].rstrip().strip()):
                    break
        out.append(Declaration(module, name, path, line_no, " ".join(signature), "\n".join(body), imports, is_postulated))
    return out


def scan_repo(root: Path) -> dict[str, Declaration]:
    return {d.fqname: d for path in sorted(root.rglob("*.agda")) for d in parse_agda(path)}


def qualified_refs(body: str) -> list[str]:
    return sorted(set(re.findall(r"\b[A-Z][A-Za-z0-9_]*\.[A-Za-z_][\w′-]*", body)))


def build_ir(repo_root: Path, config_path: Path) -> dict[str, Any]:
    config = json.loads(config_path.read_text(encoding="utf-8"))
    if config.get("schema") != SCHEMA:
        raise LaneError(f"wrong schema in {config_path}")

    declarations = scan_repo(repo_root / config.get("scan_root", "DASHI"))
    rules = config.get("authority_rules", {})
    rows = config["carriers"]
    selected: dict[str, tuple[dict[str, Any], Declaration]] = {}
    by_name: dict[str, str] = {}
    for row in rows:
        d = declarations.get(row["declaration"])
        if d is None:
            raise LaneError(f"selected declaration not found: {row['declaration']}")
        selected[row["id"]] = (row, d)
        by_name[d.name] = row["id"]

    states: dict[str, str] = {}
    dependencies: dict[str, list[str]] = {}
    explicit: dict[str, set[str]] = {}
    for cid, (row, d) in selected.items():
        ex = set(row.get("dependencies", []))
        inferred = {by_name[t] for t in d.tokens if t in by_name and by_name[t] != cid}
        deps = sorted(ex | inferred)
        missing = set(deps) - set(selected)
        if missing:
            raise LaneError(f"{cid}: unknown dependencies {sorted(missing)}")
        dependencies[cid] = deps
        explicit[cid] = ex
        if d.postulated or not d.body or any(re.search(p, d.name) for p in rules.get("open_declaration_patterns", [])):
            state = "open_analytic"
        elif any(re.search(p, d.module) for p in rules.get("source_imported_module_patterns", [])):
            state = "source_imported"
        elif any(re.search(p, d.signature) for p in rules.get("conditional_input_type_patterns", [])):
            state = "proved_conditional"
        else:
            state = "proved"
        states[cid] = state

    carrier_rows: list[Carrier] = []
    for cid, (row, d) in selected.items():
        carrier_rows.append(Carrier(cid, d.fqname, d.name, row.get("title", d.name), row.get("lane", "proof lane"), states[cid], d.signature, SourceRef(d.path.relative_to(repo_root).as_posix(), d.name, d.line), qualified_refs(d.body)))

    by_id = {c.id: c for c in carrier_rows}
    transports: list[Transport] = []
    seen: set[tuple[str, str]] = set()
    for cid in selected:
        for dep in dependencies[cid]:
            edge = (dep, cid)
            if edge in seen:
                continue
            seen.add(edge)
            evidence = "explicit-critical-path" if dep in explicit[cid] else "declaration-reference"
            transports.append(Transport(f"{dep}--{cid}", dep, cid, "dependency", evidence))

    external_map: dict[str, str] = config.get("external_reference_labels", {})
    for carrier in list(carrier_rows):
        for ref in carrier.external_refs:
            if ref not in external_map:
                continue
            ext_id = "external-" + re.sub(r"[^A-Za-z0-9]+", "-", ref).strip("-").lower()
            if ext_id not in by_id:
                ext = Carrier(
                    id=ext_id,
                    declaration=ref,
                    name=ref,
                    title=external_map[ref],
                    lane="imported anchor",
                    state="source_imported",
                    signature="qualified source reference",
                    source=carrier.source,
                    external_refs=[],
                )
                carrier_rows.append(ext)
                by_id[ext_id] = ext
            edge = (ext_id, carrier.id)
            if edge not in seen:
                seen.add(edge)
                transports.append(Transport(f"{ext_id}--{carrier.id}", ext_id, carrier.id, "import", "qualified-reference"))

    indegree = {c.id: 0 for c in carrier_rows}
    outdegree = {c.id: 0 for c in carrier_rows}
    for t in transports:
        indegree[t.target] += 1
        outdegree[t.source] += 1

    for t in transports:
        if outdegree[t.source] > 1:
            object.__setattr__(t, "kind", "split")
        if indegree[t.target] > 1:
            object.__setattr__(t, "kind", "merge")

    return {
        "schema": SCHEMA,
        "title": config["title"],
        "slug": config["slug"],
        "claim_boundary": config.get("claim_boundary", "Topology records source dependencies; it does not discharge open analytic inputs."),
        "carriers": [asdict(c) for c in carrier_rows],
        "transports": [asdict(t) for t in transports],
        "invariants": {
            "all_internal_carriers_resolve_to_agda_declarations": True,
            "edges_are_declaration_references_or_declared_critical_path": True,
            "split_merge_derived_from_graph_degree": True,
            "svg_positions_not_semantic_inputs": True,
        },
    }


def topological_layers(ir: dict[str, Any]) -> list[list[str]]:
    ids = [c["id"] for c in ir["carriers"]]
    incoming = {i: set() for i in ids}
    outgoing = {i: set() for i in ids}
    for t in ir["transports"]:
        incoming[t["target"]].add(t["source"])
        outgoing[t["source"]].add(t["target"])
    remaining = set(ids)
    done: set[str] = set()
    layers: list[list[str]] = []
    while remaining:
        layer = sorted(i for i in remaining if incoming[i] <= done)
        if not layer:
            layer = sorted(remaining)
        layers.append(layer)
        done.update(layer)
        remaining.difference_update(layer)
    return layers


def esc(value: object) -> str:
    return html.escape(str(value), quote=True)


def state_colour(state: str) -> str:
    return {
        "proved": "#48D597",
        "proved_conditional": "#43C6E8",
        "source_imported": "#F2C14E",
        "open_analytic": "#FF6B78",
        "legacy": "#8993A4",
    }.get(state, "#A6C8FF")


def render_svg(ir: dict[str, Any]) -> str:
    carriers = {c["id"]: c for c in ir["carriers"]}
    layers = topological_layers(ir)
    x_step = 250
    margin_x = 120
    width = max(1700, margin_x + (len(layers) - 1) * x_step + 220)
    max_rows = max(len(layer) for layer in layers)
    height = max(880, 250 + max_rows * 145)

    positions: dict[str, tuple[float, float]] = {}
    for x_index, layer in enumerate(layers):
        x = margin_x + x_index * x_step
        total = len(layer)
        for row, carrier_id in enumerate(layer):
            y = 180 + (row - (total - 1) / 2) * 145 + (max_rows - 1) * 58
            positions[carrier_id] = (x, y)

    indegree = {i: 0 for i in carriers}
    outdegree = {i: 0 for i in carriers}
    for t in ir["transports"]:
        indegree[t["target"]] += 1
        outdegree[t["source"]] += 1

    parts = [f'''<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="{width}" height="{height}" viewBox="0 0 {width} {height}">
<defs>
 <linearGradient id="bg" x1="0" y1="0" x2="1" y2="1"><stop stop-color="#061321"/><stop offset="1" stop-color="#14102B"/></linearGradient>
 <filter id="glow"><feGaussianBlur stdDeviation="5" result="b"/><feMerge><feMergeNode in="b"/><feMergeNode in="SourceGraphic"/></feMerge></filter>
 <style>text{{font-family:Inter,Arial,sans-serif}}.title{{fill:#F4FAFF;font-weight:700}}.sub{{fill:#9DBAD3}}.mono{{fill:#7298B7;font-family:monospace}}.strand{{fill:none;stroke-linecap:round;stroke-width:10;opacity:.86}}.under{{fill:none;stroke:#061321;stroke-width:20;stroke-linecap:round}}.cell{{fill:#0B2139;stroke-width:2}}.open{{stroke-dasharray:9 7}}@keyframes move{{to{{stroke-dashoffset:-42}}}}.moving{{stroke-dasharray:13 9;animation:move 7s linear infinite}}</style>
</defs><rect width="100%" height="100%" fill="url(#bg)"/>
<text x="70" y="58" class="title" font-size="38">{esc(ir['title'])}</text>
<text x="70" y="88" class="sub" font-size="16">Transport is proof/dependency flow; graph degree generates strand splits and merges. Open analytic endpoints remain loose.</text>''']

    path_rows: list[tuple[str, str, str, str]] = []
    for index, t in enumerate(ir["transports"]):
        sx, sy = positions[t["source"]]
        tx, ty = positions[t["target"]]
        sx += 88
        tx -= 88
        bend = 55 + (index % 3) * 18
        d = f"M {sx},{sy} C {sx+bend},{sy} {tx-bend},{ty} {tx},{ty}"
        pid = f"path-{index}"
        source_state = carriers[t["source"]]["state"]
        colour = state_colour(source_state)
        path_rows.append((pid, d, colour, t["kind"]))
        parts.append(f'<path id="{pid}" d="{d}" fill="none" stroke="none"/>')
        parts.append(f'<path d="{d}" class="under"/>')
        extra = ' stroke-dasharray="6 8"' if t["kind"] == "import" else ""
        parts.append(f'<path d="{d}" class="strand moving" stroke="{colour}"{extra}/>')

    for index, (pid, _d, colour, _kind) in enumerate(path_rows):
        parts.append(f'<circle r="6" fill="{colour}" filter="url(#glow)"><animateMotion dur="{5.0 + index % 4}s" begin="{index * .35:.2f}s" repeatCount="indefinite"><mpath href="#{pid}" xlink:href="#{pid}"/></animateMotion></circle>')

    for carrier_id, c in carriers.items():
        x, y = positions[carrier_id]
        colour = state_colour(c["state"])
        css = "cell open" if c["state"] == "open_analytic" else "cell"
        parts.append(f'<rect class="{css}" x="{x-88}" y="{y-48}" width="176" height="96" rx="20" stroke="{colour}"/>')
        title = c["title"]
        if len(title) > 24:
            title = title[:22] + "…"
        parts.append(f'<text x="{x}" y="{y-12}" text-anchor="middle" class="title" font-size="15">{esc(title)}</text>')
        parts.append(f'<text x="{x}" y="{y+10}" text-anchor="middle" class="sub" font-size="11">{esc(c["lane"])}</text>')
        parts.append(f'<text x="{x}" y="{y+30}" text-anchor="middle" font-size="11" fill="{colour}">{esc(c["state"])}</text>')
        if outdegree[carrier_id] > 1:
            parts.append(f'<text x="{x}" y="{y+67}" text-anchor="middle" class="sub" font-size="11">split × {outdegree[carrier_id]}</text>')
        if indegree[carrier_id] > 1:
            parts.append(f'<text x="{x}" y="{y+80}" text-anchor="middle" class="sub" font-size="11">merge × {indegree[carrier_id]}</text>')

    footer_y = height - 72
    paths = sorted(set(c["source"]["path"] for c in ir["carriers"] if not c["id"].startswith("external-")))
    parts.append(f'<text x="70" y="{footer_y}" class="mono" font-size="11">Sources: {esc(" · ".join(paths))}</text>')
    parts.append(f'<text x="70" y="{footer_y+25}" class="sub" font-size="12">{esc(ir["claim_boundary"])}</text>')
    parts.append(f'<text x="70" y="{footer_y+48}" class="sub" font-size="12">No visual node exists without an Agda declaration or an actual qualified source reference in a selected declaration body.</text>')
    parts.append('</svg>')
    return "\n".join(parts) + "\n"


def materialize(repo_root: Path, config: Path, json_out: Path, svg_out: Path, check: bool) -> dict[str, Any]:
    ir = build_ir(repo_root, config)
    if check:
        return ir
    json_out.parent.mkdir(parents=True, exist_ok=True)
    svg_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(ir, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    svg_out.write_text(render_svg(ir), encoding="utf-8")
    return ir


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--json-output", type=Path)
    parser.add_argument("--svg-output", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = args.repo_root.resolve()
    config = args.config if args.config.is_absolute() else root / args.config
    raw = json.loads(config.read_text())
    slug = raw["slug"]
    json_out = args.json_output or root / f"artifacts/{slug}.json"
    svg_out = args.svg_output or root / f"artifacts/{slug}.svg"
    ir = materialize(root, config, json_out, svg_out, args.check)
    print(json.dumps({"ok": True, "carriers": len(ir["carriers"]), "transports": len(ir["transports"]), "slug": slug}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
