#!/usr/bin/env python3
"""Materialise a source-backed battery of Euler phase visualisations.

The Agda module owns scene identity, dimensionality, view selection, and claim
authority.  This renderer owns floating-point sampling, screen projection, layout,
and SVG animation.  Generated pixels are never theorem-authority inputs.
"""
from __future__ import annotations

import argparse
import html
import json
import math
import re
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence


SCHEMA = "dashi-agda-phase-visualisation-v1"
AUTHORITY = {"exact", "derived", "illustrative", "observed", "candidate"}
VIEW_KINDS = {
    "phase-plane",
    "residual-shadow",
    "helix",
    "axis-fan",
    "waveform",
    "mosaic",
    "spiral",
    "search-tree",
}
SCENE_RE = re.compile(
    r"^(?P<name>[A-Za-z][\w′″-]*)\s*:\s*SceneDescriptor\s*\n"
    r"(?P=name)\s*=\s*sceneDescriptor\s+"
    r'"(?P<title>[^"\n]+)"\s+'
    r"(?P<dimension>\d+)\s+"
    r"(?P<samples>\d+)\s+"
    r"\((?P<views>[^\n)]*)\)\s+"
    r"(?P<semantic>[A-Za-z-]+)\s+"
    r"(?P<rendering>[A-Za-z-]+)\s*$",
    re.MULTILINE,
)


class PhaseVisualisationError(RuntimeError):
    pass


@dataclass(frozen=True)
class SourceRef:
    path: str
    line: int
    end_line: int
    declaration: str


@dataclass(frozen=True)
class Scene:
    name: str
    title: str
    dimension: int
    samples: int
    views: tuple[str, ...]
    semantic_authority: str
    rendering_authority: str
    source: SourceRef


def esc(value: object) -> str:
    return html.escape(str(value), quote=True)


def slug(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9]+", "-", value).strip("-").lower()


def fmt(value: float) -> str:
    if abs(value) < 5e-10:
        value = 0.0
    return f"{value:.3f}"


def parse_views(text: str) -> tuple[str, ...]:
    views = tuple(token for token in re.findall(r"[A-Za-z][A-Za-z-]*", text) if token in VIEW_KINDS)
    if not views:
        raise PhaseVisualisationError(f"scene has no recognised views: {text!r}")
    return views


def parse_scenes(source_path: Path, repo_root: Path) -> dict[str, Scene]:
    source = source_path.read_text(encoding="utf-8")
    relative = source_path.relative_to(repo_root).as_posix()
    scenes: dict[str, Scene] = {}
    for match in SCENE_RE.finditer(source):
        semantic = match.group("semantic")
        rendering = match.group("rendering")
        if semantic not in AUTHORITY or rendering not in AUTHORITY:
            raise PhaseVisualisationError(
                f"unknown authority on {match.group('name')}: {semantic}/{rendering}"
            )
        line = source.count("\n", 0, match.start()) + 1
        end_line = source.count("\n", 0, match.end()) + 1
        scene = Scene(
            name=match.group("name"),
            title=match.group("title"),
            dimension=int(match.group("dimension")),
            samples=int(match.group("samples")),
            views=parse_views(match.group("views")),
            semantic_authority=semantic,
            rendering_authority=rendering,
            source=SourceRef(relative, line, end_line, match.group("name")),
        )
        scenes[scene.name] = scene
    if not scenes:
        raise PhaseVisualisationError(f"no SceneDescriptor declarations found in {relative}")
    return scenes


def phase_vector(dimension: int, theta: float) -> list[float]:
    """Embed the ordinary complex phase plane in the first two real coordinates."""
    if dimension < 2:
        raise PhaseVisualisationError("phase scenes require dimension >= 2")
    vector = [0.0] * dimension
    vector[0] = math.cos(theta)
    vector[1] = math.sin(theta)
    return vector


def subtract(left: Sequence[float], right: Sequence[float]) -> list[float]:
    if len(left) != len(right):
        raise PhaseVisualisationError("vector dimensions differ")
    return [a - b for a, b in zip(left, right)]


def norm(vector: Sequence[float]) -> float:
    return math.sqrt(sum(value * value for value in vector))


def projection_axes(dimension: int) -> list[tuple[float, float]]:
    """Deterministic oblique screen basis; layout data, not semantic input."""
    axes: list[tuple[float, float]] = []
    denominator = max(1, dimension - 1)
    for index in range(dimension):
        angle = -math.pi / 14 + 2 * math.pi * index / dimension
        length = 1.0 - 0.24 * index / denominator
        axes.append((length * math.cos(angle), length * math.sin(angle)))
    return axes


def project(vector: Sequence[float], axes: Sequence[tuple[float, float]]) -> tuple[float, float]:
    if len(vector) != len(axes):
        raise PhaseVisualisationError("projection dimension differs from vector dimension")
    return (
        sum(value * axis[0] for value, axis in zip(vector, axes)),
        sum(value * axis[1] for value, axis in zip(vector, axes)),
    )


def scene_ir(scene: Scene) -> dict[str, Any]:
    axes = projection_axes(scene.dimension)
    anchor = phase_vector(scene.dimension, 0.0)
    rows: list[dict[str, Any]] = []
    for index in range(scene.samples):
        theta = 2 * math.pi * index / (scene.samples - 1)
        phase = phase_vector(scene.dimension, theta)
        residual = subtract(anchor, phase)
        rows.append(
            {
                "index": index,
                "theta": theta,
                "phase": phase,
                "residual": residual,
                "residual_norm": norm(residual),
                "projected_phase": list(project(phase, axes)),
                "projected_residual": list(project(residual, axes)),
            }
        )
    closing_residual = rows[-1]["residual"]
    projected_zero = project([0.0] * scene.dimension, axes)
    return {
        "name": scene.name,
        "title": scene.title,
        "dimension": scene.dimension,
        "sample_count": scene.samples,
        "views": list(scene.views),
        "semantic_authority": scene.semantic_authority,
        "rendering_authority": scene.rendering_authority,
        "source": asdict(scene.source),
        "phase_embedding": {
            "description": "theta maps to (cos theta, sin theta, 0, ..., 0)",
            "active_coordinates": [0, 1],
            "ambient_dimension": scene.dimension,
        },
        "screen_projection": {
            "kind": "deterministic-oblique-axis-fan",
            "axes": [list(axis) for axis in axes],
            "semantic_input": False,
        },
        "samples": rows,
        "invariants": {
            "full_turn_phase_closes": max(abs(value) for value in closing_residual) < 1e-9,
            "full_turn_residual_norm": norm(closing_residual),
            "screen_projection_preserves_zero": max(abs(value) for value in projected_zero) < 1e-12,
            "ambient_coordinates_above_one_are_zero": all(
                all(abs(value) < 1e-12 for value in row["phase"][2:]) for row in rows
            ),
            "screen_coordinates_are_not_semantic_inputs": True,
        },
    }


def build_ir(repo_root: Path, config_path: Path) -> dict[str, Any]:
    config = json.loads(config_path.read_text(encoding="utf-8"))
    if config.get("schema") != SCHEMA:
        raise PhaseVisualisationError(f"wrong schema in {config_path}")
    source_path = repo_root / config["source"]
    scenes = parse_scenes(source_path, repo_root)
    missing = [name for name in config["scenes"] if name not in scenes]
    if missing:
        raise PhaseVisualisationError(f"scene declarations not found: {missing}")
    selected = [scene_ir(scenes[name]) for name in config["scenes"]]
    return {
        "schema": SCHEMA,
        "title": config["title"],
        "source": config["source"],
        "scenes": selected,
        "claim_boundary": {
            "exact": "phase closure implies zero residual; zero-preserving projection maps that zero to screen zero",
            "derived": "higher-dimensional scenes embed the ordinary two-coordinate phase plane in an ambient real coordinate space",
            "illustrative": "axis placement, camera, sampling density, spiral, helix, waveform, mosaic, colour, and animation",
            "observed": "pixel-derived features remain observations and candidate models until returned to Agda and proved",
        },
        "method": [
            "model the theory faithfully in Agda",
            "derive a source-addressed visual IR",
            "render a selected battery of known views",
            "analyse generated pixels or paths as observations",
            "reconstruct candidate invariants",
            "discharge candidates back in Agda before authority promotion",
        ],
        "invariants": {
            "configuration_names_scenes_not_coordinates": True,
            "all_scenes_resolve_to_Agda_source": True,
            "renderer_owns_only_sampling_projection_and_layout": True,
            "no_visual_edge_upgrades_theorem_authority": True,
        },
    }


def svg_path(points: Iterable[tuple[float, float]]) -> str:
    rows = list(points)
    if not rows:
        return ""
    return "M" + " L".join(f"{fmt(x)},{fmt(y)}" for x, y in rows)


def panel_shell(x: float, y: float, width: float, height: float, title: str) -> list[str]:
    return [
        f'<rect class="view" x="{fmt(x)}" y="{fmt(y)}" width="{fmt(width)}" height="{fmt(height)}" rx="16"/>',
        f'<text class="view-title" x="{fmt(x + 16)}" y="{fmt(y + 25)}">{esc(title)}</text>',
    ]


def render_phase_plane(scene: dict[str, Any], x: float, y: float, w: float, h: float) -> list[str]:
    parts = panel_shell(x, y, w, h, "phase plane + residual route")
    cx, cy = x + w * 0.43, y + h * 0.57
    radius = min(w, h) * 0.27
    phase_points = []
    residual_points = []
    for row in scene["samples"]:
        px, py = row["phase"][0], row["phase"][1]
        rx, ry = row["residual"][0], row["residual"][1]
        phase_points.append((cx + radius * px, cy - radius * py))
        residual_points.append((cx + radius * 0.58 * rx, cy - radius * 0.58 * ry))
    path_id = f"phase-residual-{slug(scene['name'])}"
    parts.extend(
        [
            f'<line class="axis" x1="{fmt(x + 18)}" y1="{fmt(cy)}" x2="{fmt(x + w - 18)}" y2="{fmt(cy)}"/>',
            f'<line class="axis" x1="{fmt(cx)}" y1="{fmt(y + 42)}" x2="{fmt(cx)}" y2="{fmt(y + h - 17)}"/>',
            f'<circle cx="{fmt(cx)}" cy="{fmt(cy)}" r="{fmt(radius)}" class="guide"/>',
            f'<path d="{svg_path(phase_points)}" class="phase-route"/>',
            f'<path id="{path_id}" d="{svg_path(residual_points)}" class="residual-route"/>',
            f'<circle r="4.5" class="moving"><animateMotion dur="11s" repeatCount="indefinite"><mpath href="#{path_id}"/></animateMotion></circle>',
            f'<text class="tiny" x="{fmt(x + 18)}" y="{fmt(y + h - 14)}">R(θ) = anchor − phase(θ); closure at θ = 2π</text>',
        ]
    )
    return parts


def render_residual_shadow(scene: dict[str, Any], x: float, y: float, w: float, h: float) -> list[str]:
    parts = panel_shell(x, y, w, h, "translated vectors + residual shadow")
    theta = 0.63 * 2 * math.pi
    phase = phase_vector(scene["dimension"], theta)
    anchor = phase_vector(scene["dimension"], 0.0)
    residual = subtract(anchor, phase)
    cx, cy = x + w * 0.40, y + h * 0.58
    scale = min(w, h) * 0.24
    phase_end = (cx + scale * phase[0], cy - scale * phase[1])
    neg_end = (cx - scale * phase[0], cy + scale * phase[1])
    final_end = (neg_end[0] + scale * anchor[0], neg_end[1] - scale * anchor[1])
    residual_end = (cx + scale * residual[0], cy - scale * residual[1])
    parts.extend(
        [
            f'<circle cx="{fmt(cx)}" cy="{fmt(cy)}" r="{fmt(scale)}" class="guide"/>',
            f'<line class="gold-arrow" x1="{fmt(cx)}" y1="{fmt(cy)}" x2="{fmt(phase_end[0])}" y2="{fmt(phase_end[1])}"/>',
            f'<line class="pink-arrow" x1="{fmt(cx)}" y1="{fmt(cy)}" x2="{fmt(neg_end[0])}" y2="{fmt(neg_end[1])}"/>',
            f'<line class="cyan-arrow" x1="{fmt(neg_end[0])}" y1="{fmt(neg_end[1])}" x2="{fmt(final_end[0])}" y2="{fmt(final_end[1])}"/>',
            f'<line class="green-arrow" x1="{fmt(cx)}" y1="{fmt(cy)}" x2="{fmt(residual_end[0])}" y2="{fmt(residual_end[1])}"/>',
            f'<text class="tiny gold" x="{fmt(phase_end[0] + 6)}" y="{fmt(phase_end[1] - 4)}">phase</text>',
            f'<text class="tiny pink" x="{fmt(neg_end[0] - 42)}" y="{fmt(neg_end[1] + 16)}">−phase</text>',
            f'<text class="tiny cyan" x="{fmt((neg_end[0] + final_end[0]) / 2 - 5)}" y="{fmt(neg_end[1] - 8)}">+anchor</text>',
            f'<text class="tiny green" x="{fmt(residual_end[0] + 6)}" y="{fmt(residual_end[1] + 14)}">residual</text>',
        ]
    )
    return parts


def render_helix(scene: dict[str, Any], x: float, y: float, w: float, h: float) -> list[str]:
    parts = panel_shell(x, y, w, h, "time lift / helix")
    points: list[tuple[float, float]] = []
    count = max(120, scene["sample_count"])
    for index in range(count):
        theta = 6 * math.pi * index / (count - 1)
        time = index / (count - 1)
        px = x + w * 0.52 + w * 0.24 * math.cos(theta) + w * 0.12 * (time - 0.5)
        py = y + h * 0.83 - h * 0.58 * time - h * 0.11 * math.sin(theta)
        points.append((px, py))
    path_id = f"helix-{slug(scene['name'])}"
    parts.extend(
        [
            f'<path id="{path_id}" d="{svg_path(points)}" class="helix-route"/>',
            f'<circle r="4.5" class="moving"><animateMotion dur="12s" repeatCount="indefinite"><mpath href="#{path_id}"/></animateMotion></circle>',
            f'<line class="axis" x1="{fmt(x + w * .20)}" y1="{fmt(y + h * .84)}" x2="{fmt(x + w * .83)}" y2="{fmt(y + h * .84)}"/>',
            f'<line class="axis" x1="{fmt(x + w * .20)}" y1="{fmt(y + h * .84)}" x2="{fmt(x + w * .30)}" y2="{fmt(y + h * .24)}"/>',
            f'<text class="tiny" x="{fmt(x + 18)}" y="{fmt(y + h - 14)}">circle shadow + monotone phase/time coordinate</text>',
        ]
    )
    return parts


def render_axis_fan(scene: dict[str, Any], x: float, y: float, w: float, h: float) -> list[str]:
    parts = panel_shell(x, y, w, h, f"ambient axis fan · R^{scene['dimension']}")
    cx, cy = x + w * 0.50, y + h * 0.56
    radius = min(w, h) * 0.32
    axes = scene["screen_projection"]["axes"]
    for index, (ax, ay) in enumerate(axes):
        length = math.sqrt(ax * ax + ay * ay) or 1.0
        ex = cx + radius * ax / length
        ey = cy - radius * ay / length
        active = index < 2
        css = "fan-active-a" if index == 0 else "fan-active-b" if index == 1 else "fan-axis"
        parts.append(f'<line class="{css}" x1="{fmt(cx)}" y1="{fmt(cy)}" x2="{fmt(ex)}" y2="{fmt(ey)}"/>')
        if index < 8:
            label = "Re" if index == 0 else "Im" if index == 1 else f"e{index}"
            parts.append(f'<text class="tiny" x="{fmt(ex + 4)}" y="{fmt(ey - 3)}">{label}</text>')
        if active:
            parts.append(f'<circle cx="{fmt(ex)}" cy="{fmt(ey)}" r="3.5" class="active-dot"/>')
    parts.append(
        f'<text class="tiny" x="{fmt(x + 18)}" y="{fmt(y + h - 14)}">only Re/Im carry phase; remaining axes show ambient capacity</text>'
    )
    return parts


def render_waveform(scene: dict[str, Any], x: float, y: float, w: float, h: float) -> list[str]:
    parts = panel_shell(x, y, w, h, "residual magnitude waveform")
    left, right = x + 24, x + w - 18
    top, bottom = y + 46, y + h - 30
    points = []
    for row in scene["samples"]:
        px = left + (right - left) * row["index"] / (scene["sample_count"] - 1)
        py = bottom - (bottom - top) * row["residual_norm"] / 2.0
        points.append((px, py))
    parts.extend(
        [
            f'<line class="axis" x1="{fmt(left)}" y1="{fmt(bottom)}" x2="{fmt(right)}" y2="{fmt(bottom)}"/>',
            f'<line class="axis" x1="{fmt(left)}" y1="{fmt(top)}" x2="{fmt(left)}" y2="{fmt(bottom)}"/>',
            f'<path d="{svg_path(points)}" class="wave-route"/>',
            f'<text class="tiny" x="{fmt(left)}" y="{fmt(bottom + 17)}">0</text>',
            f'<text class="tiny" x="{fmt(right - 20)}" y="{fmt(bottom + 17)}">2π</text>',
            f'<text class="tiny" x="{fmt(left + 7)}" y="{fmt(top + 4)}">2</text>',
            f'<text class="tiny" x="{fmt(x + 18)}" y="{fmt(y + h - 10)}">|R(θ)| = 2 |sin(θ/2)|</text>',
        ]
    )
    return parts


def render_mosaic(scene: dict[str, Any], x: float, y: float, w: float, h: float) -> list[str]:
    parts = panel_shell(x, y, w, h, "projection matrix mosaic")
    axes = scene["screen_projection"]["axes"]
    left, top = x + 34, y + 54
    grid_w, grid_h = w - 54, h - 92
    cell_w = grid_w / len(axes)
    cell_h = grid_h / 2
    for row in range(2):
        for column, axis in enumerate(axes):
            value = axis[row]
            opacity = 0.12 + 0.78 * min(1.0, abs(value))
            css = "mosaic-positive" if value >= 0 else "mosaic-negative"
            parts.append(
                f'<rect class="{css}" opacity="{fmt(opacity)}" x="{fmt(left + column * cell_w)}" '
                f'y="{fmt(top + row * cell_h)}" width="{fmt(max(1.0, cell_w - .7))}" height="{fmt(cell_h - 1)}"/>'
            )
    parts.extend(
        [
            f'<text class="tiny" x="{fmt(x + 12)}" y="{fmt(top + cell_h * .55)}">x</text>',
            f'<text class="tiny" x="{fmt(x + 12)}" y="{fmt(top + cell_h * 1.55)}">y</text>',
            f'<text class="tiny" x="{fmt(x + 18)}" y="{fmt(y + h - 14)}">columns = ambient axes; rows = screen coefficients</text>',
        ]
    )
    return parts


def render_spiral(scene: dict[str, Any], x: float, y: float, w: float, h: float) -> list[str]:
    parts = panel_shell(x, y, w, h, "phase/time spiral")
    cx, cy = x + w * 0.50, y + h * 0.56
    points: list[tuple[float, float]] = []
    count = max(120, scene["sample_count"])
    for index in range(count):
        t = index / (count - 1)
        theta = 6 * math.pi * t
        radius = min(w, h) * (0.06 + 0.29 * t)
        points.append((cx + radius * math.cos(theta), cy - radius * math.sin(theta)))
    path_id = f"spiral-{slug(scene['name'])}"
    parts.extend(
        [
            f'<path id="{path_id}" d="{svg_path(points)}" class="spiral-route"/>',
            f'<circle r="4.2" class="moving"><animateMotion dur="13s" repeatCount="indefinite"><mpath href="#{path_id}"/></animateMotion></circle>',
            f'<text class="tiny" x="{fmt(x + 18)}" y="{fmt(y + h - 14)}">radius is display time; angle is phase</text>',
        ]
    )
    return parts


def render_search_tree(scene: dict[str, Any], x: float, y: float, w: float, h: float) -> list[str]:
    parts = panel_shell(x, y, w, h, "candidate search tree")
    levels = 4
    nodes: list[list[tuple[float, float]]] = []
    for level in range(levels):
        count = 2**level
        row = []
        for index in range(count):
            px = x + w * (index + 1) / (count + 1)
            py = y + 55 + (h - 90) * level / (levels - 1)
            row.append((px, py))
        nodes.append(row)
    for level in range(levels - 1):
        for index, (sx, sy) in enumerate(nodes[level]):
            for child in (2 * index, 2 * index + 1):
                tx, ty = nodes[level + 1][child]
                parts.append(f'<line class="tree-edge" x1="{fmt(sx)}" y1="{fmt(sy)}" x2="{fmt(tx)}" y2="{fmt(ty)}"/>')
    for level in nodes:
        for px, py in level:
            parts.append(f'<circle class="tree-node" cx="{fmt(px)}" cy="{fmt(py)}" r="5"/>')
    return parts


VIEW_RENDERERS = {
    "phase-plane": render_phase_plane,
    "residual-shadow": render_residual_shadow,
    "helix": render_helix,
    "axis-fan": render_axis_fan,
    "waveform": render_waveform,
    "mosaic": render_mosaic,
    "spiral": render_spiral,
    "search-tree": render_search_tree,
}


def render_svg(ir: dict[str, Any]) -> str:
    width = 1600
    scene_height = 405
    header_height = 150
    footer_height = 70
    height = header_height + scene_height * len(ir["scenes"]) + footer_height
    margin = 55
    gap = 16
    panel_width = (width - 2 * margin - 3 * gap) / 4
    panel_height = 292
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img" aria-labelledby="title desc">',
        f'<title id="title">{esc(ir["title"])}</title>',
        '<desc id="desc">Source-backed Euler phase scenes rendered through a battery of phase plane, residual, helix, axis fan, waveform, mosaic, and spiral views.</desc>',
        '<defs>',
        '<linearGradient id="bg" x2="1" y2="1"><stop stop-color="#040918"/><stop offset=".58" stop-color="#11213e"/><stop offset="1" stop-color="#27123d"/></linearGradient>',
        '<pattern id="grid" width="32" height="32" patternUnits="userSpaceOnUse"><path d="M32 0H0V32" fill="none" stroke="#9eb4d1" stroke-opacity=".055"/></pattern>',
        '<filter id="glow"><feGaussianBlur stdDeviation="5"/></filter>',
        '<marker id="goldArrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto"><path d="M0 0L8 4L0 8Z" fill="#ffd166"/></marker>',
        '<marker id="pinkArrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto"><path d="M0 0L8 4L0 8Z" fill="#ff70ae"/></marker>',
        '<marker id="cyanArrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto"><path d="M0 0L8 4L0 8Z" fill="#5ce1e6"/></marker>',
        '<marker id="greenArrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto"><path d="M0 0L8 4L0 8Z" fill="#61f4c2"/></marker>',
        '''<style>
        text{font-family:Inter,system-ui,sans-serif}.title{fill:#f6f8ff;font-size:36px;font-weight:760}.subtitle{fill:#9eb2cd;font-size:15px}.scene-title{fill:#f6f8ff;font-size:20px;font-weight:720}.meta{fill:#9eb2cd;font-size:11px;font-family:ui-monospace,monospace}.view{fill:#071329;fill-opacity:.76;stroke:#b9cdec;stroke-opacity:.16}.view-title{fill:#dcecff;font-size:13px;font-weight:700}.tiny{fill:#9eb2cd;font-size:10px}.axis{stroke:#abc0dc;stroke-opacity:.28;stroke-width:1.2}.guide{fill:none;stroke:#a8bdd8;stroke-opacity:.25;stroke-dasharray:5 7}.phase-route{fill:none;stroke:#ffd166;stroke-width:2.2}.residual-route{fill:none;stroke:#61f4c2;stroke-width:3}.moving{fill:#ff70ae;filter:url(#glow)}.gold-arrow{stroke:#ffd166;stroke-width:3;marker-end:url(#goldArrow)}.pink-arrow{stroke:#ff70ae;stroke-width:3;marker-end:url(#pinkArrow)}.cyan-arrow{stroke:#5ce1e6;stroke-width:3;marker-end:url(#cyanArrow)}.green-arrow{stroke:#61f4c2;stroke-width:3;marker-end:url(#greenArrow)}.gold{fill:#ffd166}.pink{fill:#ff70ae}.cyan{fill:#5ce1e6}.green{fill:#61f4c2}.helix-route{fill:none;stroke:#ffd166;stroke-width:3}.fan-axis{stroke:#7895b8;stroke-opacity:.38;stroke-width:1.4}.fan-active-a{stroke:#5ce1e6;stroke-width:3}.fan-active-b{stroke:#ffd166;stroke-width:3}.active-dot{fill:#f6f8ff}.wave-route{fill:none;stroke:#61f4c2;stroke-width:3}.mosaic-positive{fill:#5ce1e6}.mosaic-negative{fill:#ff70ae}.spiral-route{fill:none;stroke:#b69cff;stroke-width:3}.tree-edge{stroke:#7895b8;stroke-opacity:.5}.tree-node{fill:#b69cff}.scene-rule{stroke:#42617f;stroke-opacity:.45}
        </style>''',
        '</defs>',
        '<rect width="100%" height="100%" fill="url(#bg)"/><rect width="100%" height="100%" fill="url(#grid)"/>',
        f'<text id="title" class="title" x="{margin}" y="54">{esc(ir["title"])}</text>',
        f'<text class="subtitle" x="{margin}" y="82">Agda selects scenes and claim authority; the renderer selects samples, camera, layout, and animation.</text>',
        f'<text class="subtitle" x="{margin}" y="106">Exact closure is carried as an invariant. Spirals, helices, mosaics, and axis fans are explicit visual projections—not new algebra.</text>',
    ]
    for scene_index, scene in enumerate(ir["scenes"]):
        top = header_height + scene_index * scene_height
        source = scene["source"]
        parts.extend(
            [
                f'<line class="scene-rule" x1="{margin}" y1="{fmt(top - 13)}" x2="{width - margin}" y2="{fmt(top - 13)}"/>',
                f'<text class="scene-title" x="{margin}" y="{fmt(top + 17)}">{esc(scene["title"])}</text>',
                f'<text class="meta" x="{margin}" y="{fmt(top + 37)}">{esc(scene["name"])} · dim {scene["dimension"]} · {scene["sample_count"]} samples · semantic {esc(scene["semantic_authority"])} · render {esc(scene["rendering_authority"])}</text>',
                f'<text class="meta" x="{width - margin}" y="{fmt(top + 37)}" text-anchor="end">{esc(source["path"])}:{source["line"]}</text>',
            ]
        )
        panel_y = top + 52
        for view_index, view in enumerate(scene["views"][:4]):
            panel_x = margin + view_index * (panel_width + gap)
            parts.extend(VIEW_RENDERERS[view](scene, panel_x, panel_y, panel_width, panel_height))
        if len(scene["views"]) < 4:
            for view_index in range(len(scene["views"]), 4):
                panel_x = margin + view_index * (panel_width + gap)
                parts.extend(panel_shell(panel_x, panel_y, panel_width, panel_height, "available battery slot"))
                parts.append(
                    f'<text class="tiny" x="{fmt(panel_x + 18)}" y="{fmt(panel_y + 58)}">Add a typed EvidenceFeature or explicit SceneDescriptor view.</text>'
                )
    footer_y = height - 30
    parts.append(
        f'<text class="subtitle" x="{margin}" y="{footer_y}">Pixels may suggest an invariant; only the reconstructed Agda proof can promote it. Screen projection preserves zero by contract.</text>'
    )
    parts.append('</svg>')
    return "\n".join(parts)


def validate_ir(ir: dict[str, Any]) -> None:
    if not ir["scenes"]:
        raise PhaseVisualisationError("no scenes selected")
    for scene in ir["scenes"]:
        if scene["dimension"] < 2 or scene["sample_count"] < 3:
            raise PhaseVisualisationError(f"invalid scene size: {scene['name']}")
        if not scene["views"]:
            raise PhaseVisualisationError(f"scene has no views: {scene['name']}")
        if not scene["invariants"]["full_turn_phase_closes"]:
            raise PhaseVisualisationError(f"full-turn closure failed: {scene['name']}")
        if not scene["invariants"]["screen_projection_preserves_zero"]:
            raise PhaseVisualisationError(f"zero projection failed: {scene['name']}")
        if not scene["invariants"]["ambient_coordinates_above_one_are_zero"]:
            raise PhaseVisualisationError(f"phase escaped active plane: {scene['name']}")


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
    validate_ir(ir)
    if args.check:
        print(
            f"validated {len(ir['scenes'])} source-backed phase scenes and "
            f"{sum(len(scene['views']) for scene in ir['scenes'])} selected views"
        )
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
