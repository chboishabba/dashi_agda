#!/usr/bin/env python3
"""Plot baseline-vs-LILA training loss and its first difference."""

from __future__ import annotations

import argparse
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd


def derivative(values: np.ndarray) -> np.ndarray:
    if len(values) < 2:
        return np.zeros_like(values, dtype=float)
    return np.gradient(values)


def load_series(csv_path: Path) -> tuple[np.ndarray, np.ndarray]:
    df = pd.read_csv(csv_path)
    if "step" not in df.columns or "train_loss" not in df.columns:
        raise ValueError(f"{csv_path} must contain step and train_loss columns")
    return df["step"].to_numpy(dtype=float), df["train_loss"].to_numpy(dtype=float)


def plot_csv(csv_path: Path, label: str) -> None:
    steps, loss = load_series(csv_path)
    plt.plot(steps, loss, label=f"{label} loss")
    plt.plot(steps, derivative(loss), linestyle="--", label=f"{label} d(loss)")


def parse_args() -> argparse.Namespace:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--baseline", required=True, help="Baseline training CSV")
    ap.add_argument("--lila", required=True, help="LILA training CSV")
    ap.add_argument("--out", default="training_dynamics.png", help="Output image path")
    return ap.parse_args()


def main() -> int:
    args = parse_args()
    baseline = Path(args.baseline)
    lila = Path(args.lila)

    plt.figure(figsize=(10, 6))
    plot_csv(baseline, "baseline")
    plot_csv(lila, "lila")
    plt.xlabel("step")
    plt.ylabel("train_loss / d(train_loss)")
    plt.title("Training dynamics comparison")
    plt.legend()
    plt.tight_layout()
    plt.savefig(args.out, dpi=160)
    print(f"[ok] wrote: {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
