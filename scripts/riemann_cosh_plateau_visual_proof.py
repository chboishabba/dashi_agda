#!/usr/bin/env python3
"""Deterministic visual proof observer for the Hermitian Phi-excess lane.

This renders the actual geometric content behind

  Phi(-2 i alpha)-Phi(0)
    = integral phi(u)^2 (cosh(2 alpha u)-1) du

on the source taper plateau phi^2=1.  The rendered shaded area is the proof
observer; it is not mathematical authority.  Any recovered statement must be
re-proved/formalized separately.

The introspective round-trip exposed the stronger plateau floor

  integral_{-a}^{a}(cosh(2 alpha u)-1)du
    = sinh(2 a |alpha|)/|alpha| - 2a   (alpha != 0),

whose quadratic coercivity is only the small-alpha tangent floor.
"""

from pathlib import Path
import numpy as np
import matplotlib.pyplot as plt


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    out = root / "Docs" / "support" / "reference"
    out.mkdir(parents=True, exist_ok=True)
    svg = out / "RiemannCoshPlateauVisualProof.svg"
    png = out / "RiemannCoshPlateauVisualProof.png"

    # Dimensionless specimen.  The geometry is scale-covariant: a=1 represents
    # the plateau half-width; alpha controls transverse displacement.
    a = 1.0
    alpha = 0.9
    u = np.linspace(-1.35, 1.35, 1600)
    exact = np.cosh(2 * alpha * u)
    baseline = np.ones_like(u)
    quadratic = 1 + 2 * (alpha * u) ** 2
    mask = (u >= -a) & (u <= a)

    fig = plt.figure(figsize=(12, 8))
    ax = fig.add_axes([0.08, 0.12, 0.86, 0.8])
    ax.plot(u, exact, linewidth=2.2, label=r"$\\cosh(2\\alpha u)$")
    ax.plot(u, baseline, linewidth=1.4, linestyle="--", label=r"$1$")
    ax.plot(u, quadratic, linewidth=1.5, linestyle=":",
            label=r"$1+2\\alpha^2u^2$")
    ax.fill_between(u[mask], baseline[mask], exact[mask], alpha=0.22)
    ax.fill_between(u[mask], baseline[mask], quadratic[mask], alpha=0.14)
    ax.axvline(-a, linewidth=1.2)
    ax.axvline(a, linewidth=1.2)
    ax.annotate("", xy=(a, 0.78), xytext=(-a, 0.78),
                arrowprops=dict(arrowstyle="<->", linewidth=1.5))
    ax.text(0, 0.67, "source plateau where phi^2 = 1",
            ha="center", va="center", fontsize=12)
    ax.scatter([0], [1], s=30, zorder=5)
    ax.text(0.04, 1.08, "double contact", fontsize=10)
    ax.set_xlim(-1.35, 1.35)
    ax.set_ylim(0.55, np.cosh(2 * alpha * 1.35) + 0.7)
    ax.set_xlabel("u")
    ax.set_ylabel("kernel weight")
    ax.set_title("Transverse displacement creates unavoidable plateau area",
                 fontsize=16, fontweight="bold")
    ax.legend(loc="upper center", ncol=3, frameon=False)

    inset = fig.add_axes([0.64, 0.56, 0.26, 0.24])
    x = np.linspace(0, a, 500)
    true_excess = np.cosh(2 * alpha * x) - 1
    lower = 2 * (alpha * x) ** 2
    inset.plot(x, true_excess, linewidth=2)
    inset.plot(x, lower, linestyle=":", linewidth=1.5)
    inset.fill_between(x, 0, true_excess, alpha=0.18)
    inset.fill_between(x, 0, lower, alpha=0.12)
    inset.set_title("one half of symmetric excess", fontsize=9)
    inset.set_xticks([0, a])
    inset.set_yticks([])
    inset.set_xlabel("|u|", fontsize=8)

    fig.savefig(svg, format="svg", bbox_inches="tight")
    fig.savefig(png, dpi=180, bbox_inches="tight")
    plt.close(fig)
    print(svg)
    print(png)


if __name__ == "__main__":
    main()
