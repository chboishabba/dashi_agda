#!/usr/bin/env python3
"""Deterministic introspective visual proof for the zeta Hermitian route.

This renderer is deliberately explanatory rather than decorative.  It sends the
same reflected zero-pair geometry through two observers:

* the Alpöge--Furman inertia observer, which retains one uniform pair-count cost;
* the proposed Hermitian-energy observer, which retains a graded transverse
  defect (shown with an illustrative normalized hyperbolic plateau floor).

The lower panel visualizes the theorem-level consequence recovered by inspection:
a distance-sensitive defect yields a nested family of distance-stratified pair
ceilings.  The raster is an observer only; formal consequences live in
RiemannDistanceStratifiedObserverIntrospectiveExact.agda.
"""
from pathlib import Path
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, Circle, Rectangle, FancyArrowPatch

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "artifacts" / "introspection" / "riemann"
OUT.mkdir(parents=True, exist_ok=True)
SVG = OUT / "riemann_observer_comparison_visual_proof.svg"
PNG = OUT / "riemann_observer_comparison_visual_proof.png"

alphas = np.array([0.00, 0.05, 0.14, 0.28, 0.42])
names = ["on line", "near", "mid", "far", "farther"]
L = 4.0
a = 3 * L / 8

def defect(alpha: float) -> float:
    if alpha == 0:
        return 0.0
    return np.sinh(2 * a * abs(alpha)) / abs(alpha) - 2 * a

raw = np.array([defect(x) for x in alphas])
d = raw / raw[-1]

fig = plt.figure(figsize=(16, 10))
ax = fig.add_axes([0, 0, 1, 1])
ax.set_xlim(0, 16)
ax.set_ylim(0, 10)
ax.axis("off")

ax.text(8, 9.65, "Same zero pairs, two different questions",
        ha="center", fontsize=21, fontweight="bold")
ax.text(8, 9.30,
        "The published inertia argument keeps a uniform pair-count signal.  "
        "The Hermitian route aims to retain distance from the critical line.",
        ha="center", fontsize=11.5)

# 1. Same reflected input geometry.
ax.add_patch(FancyBboxPatch((0.45, 5.75), 4.0, 3.0,
                            boxstyle="round,pad=0.03", fill=False, linewidth=1.5))
ax.text(0.72, 8.44, "1  Same reflected pairs", fontsize=14, fontweight="bold")
xc = 2.45
ax.plot([xc, xc], [6.15, 8.00], linewidth=2)
ax.text(xc, 8.07, "critical line", ha="center", fontsize=10)
ys = np.linspace(7.68, 6.28, len(alphas))
for alpha, name, y in zip(alphas, names, ys):
    if alpha == 0:
        ax.add_patch(Circle((xc, y), 0.08, fill=False, linewidth=1.4))
        ax.text(0.80, y, "on line", va="center", fontsize=9.5)
    else:
        dist = 0.32 + alpha * 2.7
        ax.add_patch(Circle((xc - dist, y), 0.07, fill=False, linewidth=1.2))
        ax.add_patch(Circle((xc + dist, y), 0.07, fill=False, linewidth=1.2))
        ax.plot([xc - dist, xc + dist], [y, y], linestyle=":", linewidth=0.8)
        ax.text(0.80, y, f"{name}  ±α", va="center", fontsize=9.5)
ax.text(0.80, 5.97, "Only horizontal displacement changes.", fontsize=9.3)

# 2A. Coarse published observer.
ax.add_patch(FancyBboxPatch((4.85, 5.75), 4.35, 3.0,
                            boxstyle="round,pad=0.03", fill=False, linewidth=1.5))
ax.text(5.12, 8.44, "2A  Inertia observer", fontsize=14, fontweight="bold")
ax.text(5.12, 8.10, "“How many off-line pairs must the spectrum pay for?”", fontsize=9.6)
for y in [7.62, 7.30, 6.98, 6.66]:
    ax.add_patch(Circle((5.48, y), 0.05, fill=False, linewidth=1))
    ax.add_patch(FancyArrowPatch((5.58, y), (6.25, y), arrowstyle="->",
                                 mutation_scale=9, linewidth=0.8))
    ax.add_patch(FancyBboxPatch((6.30, y - 0.105), 1.60, 0.21,
                                boxstyle="round,pad=0.02", fill=False, linewidth=1))
    ax.text(7.10, y, "same pair-cost", ha="center", va="center", fontsize=8.5)
ax.text(8.16, 7.63, "near", fontsize=8.4)
ax.text(8.16, 6.67, "farther", fontsize=8.4)
ax.text(5.12, 6.08,
        "Result: distance is discarded; every off-line pair contributes the same coarse type.",
        fontsize=9.2)

# 2B. Distance-sensitive candidate observer.
ax.add_patch(FancyBboxPatch((9.60, 5.75), 5.95, 3.0,
                            boxstyle="round,pad=0.03", fill=False, linewidth=1.5))
ax.text(9.87, 8.44, "2B  Hermitian-energy observer", fontsize=14, fontweight="bold")
ax.text(9.87, 8.10, "“How much extra energy does this displacement force?”", fontsize=9.6)
barx, maxw = 11.30, 2.75
for name, val, y in zip(names, d, ys):
    ax.text(9.88, y, name, va="center", fontsize=8.8)
    ax.add_patch(Rectangle((barx, y - 0.095), maxw, 0.19, fill=False, linewidth=0.8))
    if val > 0:
        ax.add_patch(Rectangle((barx, y - 0.095), maxw * val, 0.19, alpha=0.22))
    ax.text(barx + maxw + 0.10, y, f"{val:.2f}", va="center", fontsize=8.5)
ax.text(9.87, 5.97,
        "Result: zero remains zero; larger displacement produces a larger candidate defect.",
        fontsize=9.2)

ax.add_patch(FancyArrowPatch((4.47, 7.35), (4.82, 7.35),
                             arrowstyle="->", mutation_scale=12))
ax.add_patch(FancyArrowPatch((4.47, 6.55), (9.56, 6.55),
                             arrowstyle="->", mutation_scale=12))

# 3. The theorem-level difference: one ceiling versus a nested family.
ax.add_patch(FancyBboxPatch((0.45, 0.55), 15.10, 4.70,
                            boxstyle="round,pad=0.03", fill=False, linewidth=1.5))
ax.text(0.72, 4.92, "3  Why that can prove something stronger",
        fontsize=14, fontweight="bold")
ax.text(0.72, 4.57,
        "A graded defect gives a different ceiling at every distance threshold: "
        "the farther a pair is, the more of the same error budget it must consume.",
        fontsize=10.4)

ax.text(0.90, 4.05, "Published: one distance-blind population ceiling",
        fontsize=10.8, fontweight="bold")
ax.add_patch(FancyBboxPatch((0.90, 2.72), 4.05, 0.95,
                            boxstyle="round,pad=0.04", fill=False, linewidth=1.15))
for i in range(5):
    ax.add_patch(Circle((1.38 + 0.68 * i, 3.18), 0.13, fill=False, linewidth=1.05))
    ax.text(1.38 + 0.68 * i, 3.18, "1", ha="center", va="center", fontsize=9)
ax.text(2.92, 2.88, "near and far spend the same unit", ha="center", fontsize=9)
ax.text(0.93, 2.28, "Good for total pair counts; no distance stratification.", fontsize=9.4)

ax.text(5.55, 4.05, "Hermitian: a nested family of distance ceilings",
        fontsize=10.8, fontweight="bold")
alpha_curve = np.linspace(0, 0.45, 300)
curve = np.array([defect(v) for v in alpha_curve])
curve = curve / curve[-1]
X = 5.95 + alpha_curve / 0.45 * 8.25
Y = 1.35 + 2.25 * curve
ax.plot(X, Y, linewidth=2)
err_y = 2.48
ax.plot([5.95, 14.20], [err_y, err_y], linestyle="--", linewidth=1.35)
ax.text(14.20, err_y + 0.08, "same total error budget", ha="right", fontsize=9)
for th in [0.10, 0.22, 0.34]:
    x = 5.95 + th / 0.45 * 8.25
    y = 1.35 + 2.25 * np.interp(th, alpha_curve, curve)
    ax.plot([x, x], [1.35, y], linestyle=":", linewidth=0.9)
    ax.scatter([x], [y], s=18)
    ax.text(x, 1.02, f"|α| ≥ {th:.2f}", ha="center", fontsize=8.4)
ax.text(6.00, 1.70, "small defect\nmany could fit", fontsize=8.8)
ax.text(9.65, 2.34, "bigger defect\nfewer can fit", fontsize=8.8)
ax.text(12.55, 3.38, "large defect\none may exceed budget", fontsize=8.8)
ax.text(14.15, 3.64, "candidate per-pair defect", ha="right", fontsize=8.8)

ax.add_patch(FancyBboxPatch((0.90, 0.66), 14.00, 0.72,
                            boxstyle="round,pad=0.04", fill=False, linewidth=1.15))
ax.text(7.90, 1.12,
        "Exact information: a distance observable refines the binary pair type.   "
        "Operationally: the error floor leaves a near-line tube unresolved.",
        ha="center", va="center", fontsize=9.9, fontweight="bold")
ax.text(7.90, 0.87,
        "Strongest strategy: keep the inertia pair-count ceiling, then tighten it by distance "
        "wherever the Hermitian defect is detectable.",
        ha="center", va="center", fontsize=9.7)

fig.savefig(SVG, format="svg", bbox_inches="tight")
fig.savefig(PNG, dpi=180, bbox_inches="tight")
plt.close(fig)
print(SVG)
print(PNG)
