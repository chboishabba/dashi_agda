#!/usr/bin/env python3
"""Generate a source-aware DASHI theory atlas downstream of Agda proofs."""
from __future__ import annotations

import argparse
import datetime as dt
import html
import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

SCHEMA = "dashi-theory-atlas-v1"
IDENT = r"[^\W\d][\w′″₀-₉-]*"
SIG = re.compile(rf"^(?P<name>{IDENT})\s*:\s*(?P<type>.*)$")
MODULE = re.compile(r"^\s*module\s+([\w.]+)\s+where")
IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([\w.]+)")
TOKEN = re.compile(IDENT)
LABEL = {
    "proved": "proved",
    "proved_conditional": "proved conditional on named inputs",
    "source_imported": "source-imported",
    "open_analytic": "OPEN ANALYTIC INPUT",
    "legacy": "legacy/non-critical",
}
COLOUR = {
    "proved": ("#153c2f", "#4ade80"),
    "proved_conditional": ("#123b4a", "#22d3ee"),
    "source_imported": ("#4a3510", "#fbbf24"),
    "open_analytic": ("#3f1717", "#f87171"),
    "legacy": ("#27272a", "#a1a1aa"),
}


class AtlasError(RuntimeError):
    pass


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
        return set(TOKEN.findall(f"{self.signature}\n{self.body}"))


@dataclass
class Card:
    id: str
    declaration: Declaration
    title: str
    formula: str
    lane: str
    critical: bool
    anchors: list[str]
    relation: str
    explicit_dependencies: list[str]
    state: str = "proved"
    dependencies: list[str] = field(default_factory=list)
    open_inputs: list[str] = field(default_factory=list)


def uncomment(line: str) -> str:
    return line.split("--", 1)[0].rstrip()


def parse_agda_file(path: Path) -> list[Declaration]:
    lines = path.read_text(encoding="utf-8").splitlines()
    module = next((m.group(1) for line in lines if (m := MODULE.match(line))), None)
    if module is None:
        return []
    imports = [m.group(1) for line in lines if (m := IMPORT.match(line))]
    declarations: list[Declaration] = []
    postulate_indent: int | None = None
    i = 0
    while i < len(lines):
        raw = lines[i]
        text = uncomment(raw).strip()
        indent = len(raw) - len(raw.lstrip())
        if text in {"postulate", "primitive"}:
            postulate_indent = indent
            i += 1
            continue
        if postulate_indent is not None and text and indent <= postulate_indent:
            postulate_indent = None
        match = SIG.match(text) if indent == 0 or postulate_indent is not None else None
        if match is None or match.group("name") in {"module", "open", "import", "record", "data", "field"}:
            i += 1
            continue

        name = match.group("name")
        line_number = i + 1
        declaration_indent = indent
        signature = [match.group("type")]
        i += 1
        while i < len(lines):
            next_raw = lines[i]
            next_text = uncomment(next_raw).strip()
            next_indent = len(next_raw) - len(next_raw.lstrip())
            if not next_text:
                i += 1
                continue
            if postulate_indent is not None:
                if next_indent == declaration_indent and SIG.match(next_text):
                    break
                if next_indent <= postulate_indent:
                    break
                signature.append(next_text)
                i += 1
                continue
            if next_indent == 0 and (
                SIG.match(next_text)
                or re.match(rf"^{re.escape(name)}(?:\s|\(|\{{|$)", next_text)
            ):
                break
            signature.append(next_text)
            i += 1

        body: list[str] = []
        if postulate_indent is None:
            definition = re.compile(rf"^{re.escape(name)}(?:\s|\(|\{{|$)")
            while i < len(lines) and definition.match(uncomment(lines[i]).strip()):
                while i < len(lines):
                    body_raw = lines[i]
                    body_text = uncomment(body_raw).strip()
                    body_indent = len(body_raw) - len(body_raw.lstrip())
                    if body_text and body_indent == 0 and SIG.match(body_text):
                        break
                    if body_text:
                        body.append(body_text)
                    i += 1
                if i >= len(lines) or not definition.match(uncomment(lines[i]).strip()):
                    break

        declarations.append(
            Declaration(
                module=module,
                name=name,
                path=path,
                line=line_number,
                signature=" ".join(signature),
                body="\n".join(body),
                imports=imports,
                postulated=postulate_indent is not None,
            )
        )
    return declarations


def scan_repo(root: Path) -> dict[str, Declaration]:
    return {
        declaration.fqname: declaration
        for path in sorted(root.rglob("*.agda"))
        for declaration in parse_agda_file(path)
    }


def matches(value: str, patterns: list[str]) -> bool:
    return any(re.search(pattern, value) for pattern in patterns)


def build_cards(spec: dict[str, Any], declarations: dict[str, Declaration], strict: bool = True) -> list[Card]:
    cards: list[Card] = []
    for row in spec["cards"]:
        declaration = declarations.get(row["declaration"])
        if declaration is None:
            if strict:
                raise AtlasError(f"selected declaration not found: {row['declaration']}")
            continue
        cards.append(
            Card(
                id=row.get("id", declaration.fqname),
                declaration=declaration,
                title=row.get("title", declaration.name),
                formula=row.get("formula", declaration.signature),
                lane=row.get("lane", "critical path"),
                critical=row.get("critical", True),
                anchors=row.get("source_anchors", []),
                relation=row.get("source_relation", "DASHI introduces new theorem"),
                explicit_dependencies=row.get("dependencies", []),
            )
        )
    if len({card.id for card in cards}) != len(cards):
        raise AtlasError("duplicate card id")
    return cards


def derive_graph(cards: list[Card], spec: dict[str, Any]) -> None:
    by_id = {card.id: card for card in cards}
    by_name = {card.declaration.name: card.id for card in cards}
    rules = spec.get("authority_rules", {})
    for card in cards:
        inferred = {by_name[token] for token in card.declaration.tokens if token in by_name and by_name[token] != card.id}
        card.dependencies = sorted(set(card.explicit_dependencies) | inferred)
        missing = set(card.dependencies) - set(by_id)
        if missing:
            raise AtlasError(f"{card.id}: unknown dependencies {sorted(missing)}")
        if not card.critical:
            card.state = "legacy"
        elif card.declaration.postulated or not card.declaration.body or matches(card.declaration.name, rules.get("open_declaration_patterns", [])):
            card.state = "open_analytic"
        elif matches(card.declaration.module, rules.get("source_imported_module_patterns", [])):
            card.state = "source_imported"
        else:
            conditional = [pattern for pattern in rules.get("conditional_input_type_patterns", []) if re.search(pattern, card.declaration.signature)]
            if conditional:
                card.state = "proved_conditional"
                card.open_inputs = conditional

    def open_dependencies(card_id: str, trail: frozenset[str] = frozenset()) -> set[str]:
        if card_id in trail:
            return set()
        card = by_id[card_id]
        found = {card_id} if card.state == "open_analytic" else set()
        for dependency in card.dependencies:
            found |= open_dependencies(dependency, trail | {card_id})
        return found

    for card in cards:
        inherited = sorted(open_dependencies(card.id) - {card.id})
        if card.state == "proved" and inherited:
            card.state = "proved_conditional"
        card.open_inputs = sorted(set(card.open_inputs) | set(inherited))

    visiting: set[str] = set()
    complete: set[str] = set()

    def visit(card_id: str) -> None:
        if card_id in visiting:
            raise AtlasError(f"dependency cycle at {card_id}")
        if card_id in complete:
            return
        visiting.add(card_id)
        for dependency in by_id[card_id].dependencies:
            visit(dependency)
        visiting.remove(card_id)
        complete.add(card_id)

    for card_id in by_id:
        visit(card_id)


def make_payload(spec: dict[str, Any], cards: list[Card], root: Path, generated_at: str) -> dict[str, Any]:
    counts = {state: 0 for state in LABEL}
    rows = []
    for number, card in enumerate(cards, 1):
        counts[card.state] += 1
        declaration = card.declaration
        rows.append(
            {
                "number": number,
                "id": card.id,
                "title": card.title,
                "formula": card.formula,
                "lane": card.lane,
                "declaration": declaration.fqname,
                "module": declaration.module,
                "name": declaration.name,
                "state": card.state,
                "state_label": LABEL[card.state],
                "critical": card.critical,
                "dependencies": card.dependencies,
                "open_inputs": card.open_inputs,
                "imports": declaration.imports,
                "source_locator": {"path": declaration.path.relative_to(root).as_posix(), "line": declaration.line},
                "source_anchors": card.anchors,
                "source_relation": card.relation,
                "signature": declaration.signature,
                "has_definition": bool(declaration.body),
                "postulated": declaration.postulated,
            }
        )
    return {
        "schema": SCHEMA,
        "schema_version": "1.0.0",
        "title": spec.get("title", "DASHI Theory Atlas"),
        "generated_at": generated_at,
        "counts": counts,
        "cards": rows,
        "footer": "Compilation certifies type-correct assembly only. It does not discharge displayed open analytic inputs.",
    }


def render_svg(data: dict[str, Any]) -> str:
    rows = data["cards"]
    width, card_width, card_height, gap = 1280, 1120, 180, 34
    height = 330 + len(rows) * (card_height + gap)
    positions = {row["id"]: 150 + index * (card_height + gap) for index, row in enumerate(rows)}
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}">',
        '<rect width="100%" height="100%" fill="#09090b"/>',
        '<style>text{font-family:system-ui,sans-serif}.mono{font-family:monospace}</style>',
        f'<text x="80" y="62" fill="#fafafa" font-size="34" font-weight="700">{html.escape(data["title"])}</text>',
    ]
    for row in rows:
        for dependency in row["dependencies"]:
            if dependency in positions:
                dash = ' stroke-dasharray="10 8"' if row["state"] == "proved_conditional" else ""
                parts.append(f'<path d="M 640 {positions[dependency] + card_height} L 640 {positions[row["id"]]}" stroke="#52525b" stroke-width="3" fill="none"{dash}/>')
    for row in rows:
        y = positions[row["id"]]
        fill, stroke = COLOUR[row["state"]]
        dash = ' stroke-dasharray="10 7"' if row["state"] == "open_analytic" else ""
        parts.extend(
            [
                f'<rect x="80" y="{y}" rx="18" width="{card_width}" height="{card_height}" fill="{fill}" stroke="{stroke}" stroke-width="3"{dash}/>',
                f'<text x="108" y="{y + 38}" fill="{stroke}" font-size="18" font-weight="700">{row["number"]:02d} · {html.escape(row["lane"])}</text>',
                f'<text x="108" y="{y + 72}" fill="#fafafa" font-size="25" font-weight="700">{html.escape(row["title"])}</text>',
                f'<text class="mono" x="108" y="{y + 108}" fill="#e4e4e7" font-size="16">{html.escape(row["formula"][:112])}</text>',
                f'<text class="mono" x="108" y="{y + 151}" fill="#a1a1aa" font-size="14">{html.escape(row["name"])}</text>',
                f'<text x="1172" y="{y + 38}" fill="{stroke}" text-anchor="end" font-size="15" font-weight="700">{html.escape(row["state_label"])}</text>',
            ]
        )
    parts.extend(
        [
            f'<text x="80" y="{height - 64}" fill="#f4f4f5" font-size="17" font-weight="700">{html.escape(data["footer"])}</text>',
            "</svg>",
        ]
    )
    return "\n".join(parts) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--spec", type=Path, default=Path("config/dashi-yang-mills-critical-path-atlas.json"))
    parser.add_argument("--json-output", type=Path, default=Path("artifacts/dashi-yang-mills-critical-path.json"))
    parser.add_argument("--svg-output", type=Path, default=Path("artifacts/dashi-yang-mills-critical-path.svg"))
    parser.add_argument("--generated-at")
    parser.add_argument("--no-strict", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = args.repo_root.resolve()
    spec_path = args.spec if args.spec.is_absolute() else root / args.spec
    spec = json.loads(spec_path.read_text(encoding="utf-8"))
    if spec.get("schema") != SCHEMA:
        raise AtlasError("wrong atlas schema")
    cards = build_cards(spec, scan_repo(root / spec.get("scan_root", "DASHI")), strict=not args.no_strict)
    derive_graph(cards, spec)
    data = make_payload(spec, cards, root, args.generated_at or dt.datetime.now(dt.UTC).replace(microsecond=0).isoformat())
    if args.check:
        print(json.dumps({"ok": True, "cards": len(cards), "counts": data["counts"]}, sort_keys=True))
        return 0
    json_path = args.json_output if args.json_output.is_absolute() else root / args.json_output
    svg_path = args.svg_output if args.svg_output.is_absolute() else root / args.svg_output
    json_path.parent.mkdir(parents=True, exist_ok=True)
    svg_path.parent.mkdir(parents=True, exist_ok=True)
    json_path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    svg_path.write_text(render_svg(data), encoding="utf-8")
    print(f"wrote {json_path}\nwrote {svg_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
