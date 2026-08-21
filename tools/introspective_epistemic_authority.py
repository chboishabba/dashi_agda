#!/usr/bin/env python3
"""Generate and machine-read the epistemic-authority introspection diagram.

This is deliberately a round trip:

  formal semantic specimen
      -> deterministic OpenCV raster
      -> connected-component measurement
      -> JSON receipt
      -> Agda finite receipt/model

The current raster intentionally exposes one useful failure: the two semantic
edges leaving ``received`` touch at their common branch point, so five semantic
edges appear as only four connected edge components.  That information-losing
visual quotient is formalised in
``DASHI.Reasoning.EpistemicAuthorityIntrospectiveVisualReceiptExact``.

The pixel analysis is an empirical receipt about this generated image.  It does
not itself grant semantic or legal authority.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import cv2
import numpy as np

WIDTH = 1200
HEIGHT = 700

NODE_GRAY = 32
EDGE_GRAY = 96
TEXT_GRAY = 235
TERMINAL_GRAY = 48

NODES = {
    "received": (60, 300, 240, 380, "received"),
    "apparent": (350, 100, 570, 180, "reasonably apparent"),
    "persisted": (700, 100, 880, 180, "persisted"),
    "objective": (980, 100, 1160, 180, "objective gateway"),
    "comprehended": (350, 480, 570, 560, "comprehended"),
    "withdraw": (790, 480, 970, 560, "withdraw"),
}

# Five semantic edges.  The first and fourth share/touch at the branch origin
# in the raster, hence OpenCV observes four edge connected components.
EDGES = [
    ((250, 340), (330, 140)),       # received -> apparent
    ((580, 140), (680, 140)),       # apparent -> persisted
    ((890, 140), (960, 140)),       # persisted -> objective
    ((250, 340), (330, 520)),       # received -> comprehended
    ((580, 520), (770, 520)),       # comprehended -> withdraw
]

TERMINALS = ("objective", "withdraw")


def gray3(value: int) -> tuple[int, int, int]:
    return value, value, value


def generate() -> np.ndarray:
    image = np.full((HEIGHT, WIDTH, 3), 255, np.uint8)

    for start, end in EDGES:
        cv2.line(
            image,
            start,
            end,
            gray3(EDGE_GRAY),
            thickness=8,
            lineType=cv2.LINE_8,
        )

    for x1, y1, x2, y2, label in NODES.values():
        cv2.rectangle(
            image,
            (x1, y1),
            (x2, y2),
            gray3(NODE_GRAY),
            thickness=-1,
            lineType=cv2.LINE_8,
        )
        cv2.putText(
            image,
            label,
            (x1 + 10, (y1 + y2) // 2 + 8),
            cv2.FONT_HERSHEY_SIMPLEX,
            0.48,
            gray3(TEXT_GRAY),
            1,
            cv2.LINE_8,
        )

    for name in TERMINALS:
        x1, y1, x2, y2, _ = NODES[name]
        cv2.circle(
            image,
            (x2 - 18, y1 + 18),
            8,
            gray3(TERMINAL_GRAY),
            thickness=-1,
            lineType=cv2.LINE_8,
        )

    return image


def components(mask: np.ndarray, min_area: int) -> list[dict[str, int]]:
    count, _labels, stats, _centroids = cv2.connectedComponentsWithStats(
        mask.astype(np.uint8), connectivity=8
    )
    result: list[dict[str, int]] = []
    for index in range(1, count):
        area = int(stats[index, cv2.CC_STAT_AREA])
        if area < min_area:
            continue
        result.append(
            {
                "area": area,
                "x": int(stats[index, cv2.CC_STAT_LEFT]),
                "y": int(stats[index, cv2.CC_STAT_TOP]),
                "w": int(stats[index, cv2.CC_STAT_WIDTH]),
                "h": int(stats[index, cv2.CC_STAT_HEIGHT]),
            }
        )
    return result


def analyse(image: np.ndarray) -> dict[str, object]:
    gray = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
    node_components = components(gray == NODE_GRAY, min_area=1000)
    edge_components = components(gray == EDGE_GRAY, min_area=100)
    terminal_components = components(gray == TERMINAL_GRAY, min_area=50)

    receipt: dict[str, object] = {
        "generator": "OpenCV deterministic raster",
        "width": WIDTH,
        "height": HEIGHT,
        "semantic_node_count": len(NODES),
        "node_components": len(node_components),
        "semantic_edge_count": len(EDGES),
        "edge_components": len(edge_components),
        "terminal_markers": len(terminal_components),
        "branch_origin_count": 1,
        "semantic_expected": {
            "shared_origin": "received",
            "upper_terminal": "objectiveGateway",
            "lower_terminal": "withdraw",
        },
        "node_components_detail": node_components,
        "edge_components_detail": edge_components,
        "terminal_components_detail": terminal_components,
    }

    # Fail closed if a visual or OpenCV change invalidates the finite receipt
    # hard-coded into the Agda module.
    expected = {
        "semantic_node_count": 6,
        "node_components": 6,
        "semantic_edge_count": 5,
        "edge_components": 4,
        "terminal_markers": 2,
        "branch_origin_count": 1,
    }
    for key, value in expected.items():
        if receipt[key] != value:
            raise RuntimeError(
                f"introspection receipt drift: {key}={receipt[key]!r}, "
                f"expected {value!r}"
            )

    return receipt


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--out-dir",
        default="artifacts/introspective/epistemic-authority",
        help="directory for PNG and JSON receipt",
    )
    args = parser.parse_args()

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    image = generate()
    png_path = out_dir / "epistemic_authority_capture.png"
    receipt_path = out_dir / "epistemic_authority_capture.receipt.json"

    if not cv2.imwrite(str(png_path), image):
        raise RuntimeError(f"failed to write {png_path}")

    receipt = analyse(image)
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")

    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
