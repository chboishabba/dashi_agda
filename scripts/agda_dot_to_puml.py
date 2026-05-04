#!/usr/bin/env python3
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path


LABEL_RE = re.compile(r'^\s*(?P<id>[A-Za-z_][A-Za-z0-9_]*)\[label="(?P<label>[^"]+)"\];\s*$')
EDGE_RE = re.compile(r"^\s*(?P<src>[A-Za-z_][A-Za-z0-9_]*)\s*->\s*(?P<dst>[A-Za-z_][A-Za-z0-9_]*)\s*;\s*$")


@dataclass(frozen=True)
class DotGraph:
    labels: dict[str, str]
    edges: list[tuple[str, str]]


def parse_agda_dot(text: str) -> DotGraph:
    labels: dict[str, str] = {}
    edges: list[tuple[str, str]] = []

    for line_no, line in enumerate(text.splitlines(), start=1):
        stripped = line.strip()
        if not stripped or stripped in {"digraph dependencies {", "}"}:
            continue

        label_match = LABEL_RE.match(line)
        if label_match:
            labels[label_match.group("id")] = label_match.group("label")
            continue

        edge_match = EDGE_RE.match(line)
        if edge_match:
            edges.append((edge_match.group("src"), edge_match.group("dst")))
            continue

        raise ValueError(f"unsupported DOT line {line_no}: {line}")

    missing = sorted({node for edge in edges for node in edge if node not in labels})
    if missing:
        raise ValueError(f"edges refer to missing node labels: {', '.join(missing)}")

    return DotGraph(labels=labels, edges=edges)


def puml_alias(node_id: str) -> str:
    return f"agda_{node_id}"


def render_puml(
    graph: DotGraph,
    *,
    title: str,
    element: str,
    direction: str,
) -> str:
    lines = [
        "@startuml",
        f"title {title}",
        "skinparam linetype ortho",
        "skinparam packageStyle rectangle",
    ]

    if direction:
        lines.append(f"{direction} direction")

    lines.append("")

    for node_id, label in sorted(graph.labels.items(), key=lambda item: item[1]):
        lines.append(f'{element} "{label}" as {puml_alias(node_id)}')

    lines.append("")

    for src, dst in graph.edges:
        lines.append(f"{puml_alias(src)} --> {puml_alias(dst)}")

    lines.append("@enduml")
    return "\n".join(lines) + "\n"


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Convert the DOT emitted by `agda --dependency-graph=FILE` into a "
            "PlantUML dependency diagram."
        )
    )
    parser.add_argument("dot", type=Path, help="Input DOT file from Agda.")
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        help="Output PUML path. Defaults to stdout.",
    )
    parser.add_argument(
        "--title",
        default="Agda module dependency graph",
        help="PlantUML diagram title.",
    )
    parser.add_argument(
        "--element",
        choices=("component", "class", "rectangle"),
        default="component",
        help="PlantUML node element type. Default: component.",
    )
    parser.add_argument(
        "--direction",
        choices=("left to right", "top to bottom", ""),
        default="left to right",
        help="PlantUML graph direction. Default: left to right.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        graph = parse_agda_dot(args.dot.read_text(encoding="utf-8"))
        puml = render_puml(
            graph,
            title=args.title,
            element=args.element,
            direction=args.direction,
        )
    except (OSError, ValueError) as exc:
        print(f"agda-dot-to-puml: {exc}", file=sys.stderr)
        return 1

    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(puml, encoding="utf-8")
    else:
        sys.stdout.write(puml)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
