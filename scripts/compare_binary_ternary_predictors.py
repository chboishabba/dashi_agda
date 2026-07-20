#!/usr/bin/env python3
"""Walk-forward binary vs ternary market-prediction experiment.

This is a research harness, not a trading recommendation.  It keeps the
strategy/execution boundary explicit and learns only a dimensionless
abstention knob on past data.

Input CSV columns:
    timestamp, close

Without --csv, a deterministic synthetic regime series is generated so the
pipeline and invariants can be tested without network access.

Models:
  binary   : always emits down/up from the sign of the current return
  ternary  : emits HOLD when |return| / trailing_volatility < learned k
  3-adic   : optional suffix-backoff predictor over ternary return digits

The threshold k is selected independently in each walk-forward training fold.
No future rows enter feature construction or knob selection.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence

import numpy as np

SELL = -1
HOLD = 0
BUY = 1


@dataclass(frozen=True)
class FoldResult:
    fold: int
    train_start: int
    train_end: int
    test_start: int
    test_end: int
    selected_k: float
    binary_accuracy: float
    ternary_active_accuracy: float
    ternary_coverage: float
    binary_net_return: float
    ternary_net_return: float
    binary_turnover: float
    ternary_turnover: float
    padic_accuracy: float | None
    padic_coverage: float | None


def load_close_csv(path: Path) -> np.ndarray:
    values: list[float] = []
    with path.open(newline="") as handle:
        reader = csv.DictReader(handle)
        if "close" not in (reader.fieldnames or []):
            raise ValueError("CSV must contain a 'close' column")
        for row in reader:
            try:
                value = float(row["close"])
            except (TypeError, ValueError):
                continue
            if math.isfinite(value) and value > 0:
                values.append(value)
    if len(values) < 300:
        raise ValueError("need at least 300 valid close observations")
    return np.asarray(values, dtype=np.float64)


def synthetic_close(n: int = 6000, seed: int = 7) -> np.ndarray:
    """Deterministic seeded series with alternating trend/chop regimes."""
    rng = np.random.default_rng(seed)
    ret = np.empty(n, dtype=np.float64)
    block = 300
    for i in range(n):
        regime = (i // block) % 4
        if regime == 0:
            drift, sigma, phi = 0.00035, 0.0040, 0.28
        elif regime == 1:
            drift, sigma, phi = 0.0, 0.0075, -0.35
        elif regime == 2:
            drift, sigma, phi = -0.00030, 0.0045, 0.22
        else:
            drift, sigma, phi = 0.0, 0.0120, 0.0
        previous = ret[i - 1] if i else 0.0
        ret[i] = drift + phi * previous + rng.normal(0.0, sigma)
    return 100.0 * np.exp(np.cumsum(ret))


def returns(close: np.ndarray) -> np.ndarray:
    out = np.zeros_like(close)
    out[1:] = np.diff(np.log(close))
    return out


def trailing_volatility(ret: np.ndarray, window: int) -> np.ndarray:
    """Past-only sample volatility; value at t uses returns through t."""
    if window < 2:
        raise ValueError("volatility window must be at least 2")
    out = np.full(ret.shape, np.nan, dtype=np.float64)
    c1 = np.concatenate(([0.0], np.cumsum(ret)))
    c2 = np.concatenate(([0.0], np.cumsum(ret * ret)))
    for t in range(window - 1, ret.size):
        start = t + 1 - window
        total = c1[t + 1] - c1[start]
        total2 = c2[t + 1] - c2[start]
        mean = total / window
        variance = max((total2 - window * mean * mean) / (window - 1), 0.0)
        out[t] = math.sqrt(variance)
    return out


def sign_action(x: np.ndarray) -> np.ndarray:
    return np.where(x > 0, BUY, np.where(x < 0, SELL, HOLD)).astype(np.int8)


def ternary_action(ret: np.ndarray, vol: np.ndarray, k: float) -> np.ndarray:
    scale = np.divide(
        np.abs(ret), vol, out=np.zeros_like(ret), where=np.isfinite(vol) & (vol > 0)
    )
    direction = sign_action(ret)
    return np.where(scale >= k, direction, HOLD).astype(np.int8)


def next_direction(ret: np.ndarray) -> np.ndarray:
    target = np.zeros_like(ret, dtype=np.int8)
    target[:-1] = sign_action(ret[1:])
    return target


def strategy_metrics(
    action: np.ndarray,
    future_return: np.ndarray,
    fee_rate: float,
) -> tuple[float, float, float, float]:
    active = action != HOLD
    correct = (action == sign_action(future_return)) & active
    active_accuracy = float(correct.sum() / active.sum()) if active.any() else 0.0
    coverage = float(active.mean())

    previous = np.concatenate(([HOLD], action[:-1]))
    turnover_series = np.abs(action.astype(np.float64) - previous.astype(np.float64))
    net = action.astype(np.float64) * future_return - fee_rate * turnover_series
    return active_accuracy, coverage, float(net.sum()), float(turnover_series.sum())


def knob_loss(
    action: np.ndarray,
    future_return: np.ndarray,
    fee_rate: float,
    abstention_penalty: float,
) -> float:
    """Cost-aware decision loss, fixed before fold evaluation.

    Wrong active direction pays |return|, correct active direction receives the
    same amount, turnover pays fee_rate, and abstention pays a small opportunity
    term proportional to |return|.  This learns an action boundary rather than
    selecting a threshold from test PnL.
    """
    previous = np.concatenate(([HOLD], action[:-1]))
    signed_gain = action.astype(np.float64) * future_return
    turnover = np.abs(action.astype(np.float64) - previous.astype(np.float64))
    abstained = action == HOLD
    return float(
        (-signed_gain + fee_rate * turnover + abstention_penalty * abstained * np.abs(future_return)).mean()
    )


def choose_k(
    ret: np.ndarray,
    vol: np.ndarray,
    future_return: np.ndarray,
    candidates: Sequence[float],
    fee_rate: float,
    abstention_penalty: float,
) -> float:
    scored = []
    for k in candidates:
        action = ternary_action(ret, vol, k)
        scored.append((knob_loss(action, future_return, fee_rate, abstention_penalty), k))
    scored.sort(key=lambda pair: (pair[0], pair[1]))
    return float(scored[0][1])


def digit_from_action(action: int) -> int:
    return {SELL: 0, HOLD: 1, BUY: 2}[int(action)]


def padic_suffix_predict(
    train_digits: np.ndarray,
    train_targets: np.ndarray,
    test_digits: np.ndarray,
    max_depth: int,
    min_support: int,
) -> np.ndarray:
    """3-adic suffix backoff.

    A recent-first ternary history is represented by its base-3 suffix.  The
    predictor uses the longest suffix with sufficient past support and backs
    off when necessary.  HOLD means the past is insufficient or tied.
    """
    tables: list[dict[tuple[int, ...], np.ndarray]] = [dict() for _ in range(max_depth + 1)]
    for t in range(max_depth, train_digits.size - 1):
        target = int(train_targets[t])
        target_index = {SELL: 0, HOLD: 1, BUY: 2}[target]
        for depth in range(1, max_depth + 1):
            key = tuple(int(x) for x in train_digits[t - depth + 1 : t + 1])
            counts = tables[depth].setdefault(key, np.zeros(3, dtype=np.int64))
            counts[target_index] += 1

    history = np.concatenate((train_digits[-max_depth:], test_digits))
    pred = np.full(test_digits.size, HOLD, dtype=np.int8)
    for j in range(test_digits.size):
        end = max_depth + j
        for depth in range(max_depth, 0, -1):
            key = tuple(int(x) for x in history[end - depth + 1 : end + 1])
            counts = tables[depth].get(key)
            if counts is None or int(counts.sum()) < min_support:
                continue
            winners = np.flatnonzero(counts == counts.max())
            if winners.size == 1:
                pred[j] = np.asarray([SELL, HOLD, BUY], dtype=np.int8)[winners[0]]
            break
    return pred


def walk_forward(
    close: np.ndarray,
    train_size: int,
    test_size: int,
    vol_window: int,
    candidates: Sequence[float],
    fee_rate: float,
    abstention_penalty: float,
    padic_depth: int,
    padic_min_support: int,
) -> list[FoldResult]:
    ret = returns(close)
    vol = trailing_volatility(ret, vol_window)
    future = np.zeros_like(ret)
    future[:-1] = ret[1:]
    target = next_direction(ret)

    results: list[FoldResult] = []
    start = max(vol_window, train_size)
    fold = 0
    while start + test_size < ret.size:
        train_start = start - train_size
        train_end = start
        test_start = start
        test_end = start + test_size

        train_slice = slice(train_start, train_end)
        test_slice = slice(test_start, test_end)
        k = choose_k(
            ret[train_slice],
            vol[train_slice],
            future[train_slice],
            candidates,
            fee_rate,
            abstention_penalty,
        )

        binary = sign_action(ret[test_slice])
        ternary = ternary_action(ret[test_slice], vol[test_slice], k)
        b_acc, _, b_net, b_turn = strategy_metrics(binary, future[test_slice], fee_rate)
        t_acc, t_cov, t_net, t_turn = strategy_metrics(ternary, future[test_slice], fee_rate)

        p_acc: float | None = None
        p_cov: float | None = None
        if padic_depth > 0:
            train_actions = ternary_action(ret[train_slice], vol[train_slice], k)
            test_actions = ternary
            p_pred = padic_suffix_predict(
                np.asarray([digit_from_action(x) for x in train_actions], dtype=np.int8),
                target[train_slice],
                np.asarray([digit_from_action(x) for x in test_actions], dtype=np.int8),
                padic_depth,
                padic_min_support,
            )
            active = p_pred != HOLD
            p_acc = float((p_pred[active] == target[test_slice][active]).mean()) if active.any() else 0.0
            p_cov = float(active.mean())

        results.append(
            FoldResult(
                fold=fold,
                train_start=train_start,
                train_end=train_end,
                test_start=test_start,
                test_end=test_end,
                selected_k=k,
                binary_accuracy=b_acc,
                ternary_active_accuracy=t_acc,
                ternary_coverage=t_cov,
                binary_net_return=b_net,
                ternary_net_return=t_net,
                binary_turnover=b_turn,
                ternary_turnover=t_turn,
                padic_accuracy=p_acc,
                padic_coverage=p_cov,
            )
        )
        start += test_size
        fold += 1
    return results


def mean(values: Iterable[float]) -> float:
    seq = list(values)
    return float(np.mean(seq)) if seq else float("nan")


def report(results: Sequence[FoldResult]) -> dict[str, object]:
    if not results:
        raise ValueError("no folds produced; reduce train/test sizes or provide more data")
    summary: dict[str, object] = {
        "folds": len(results),
        "mean_selected_k": mean(r.selected_k for r in results),
        "binary_accuracy": mean(r.binary_accuracy for r in results),
        "ternary_active_accuracy": mean(r.ternary_active_accuracy for r in results),
        "ternary_coverage": mean(r.ternary_coverage for r in results),
        "binary_net_return_sum": float(sum(r.binary_net_return for r in results)),
        "ternary_net_return_sum": float(sum(r.ternary_net_return for r in results)),
        "binary_turnover_sum": float(sum(r.binary_turnover for r in results)),
        "ternary_turnover_sum": float(sum(r.ternary_turnover for r in results)),
    }
    padic = [r for r in results if r.padic_accuracy is not None]
    if padic:
        summary["padic_accuracy"] = mean(float(r.padic_accuracy) for r in padic)
        summary["padic_coverage"] = mean(float(r.padic_coverage) for r in padic)
    return {"summary": summary, "folds": [asdict(r) for r in results]}


def parse_candidates(text: str) -> list[float]:
    values = sorted({float(item) for item in text.split(",") if item.strip()})
    if not values or values[0] < 0:
        raise argparse.ArgumentTypeError("candidates must be non-negative")
    return values


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--csv", type=Path)
    parser.add_argument("--train-size", type=int, default=1200)
    parser.add_argument("--test-size", type=int, default=240)
    parser.add_argument("--vol-window", type=int, default=48)
    parser.add_argument("--fee-rate", type=float, default=0.0004)
    parser.add_argument("--abstention-penalty", type=float, default=0.05)
    parser.add_argument(
        "--candidates",
        type=parse_candidates,
        default=parse_candidates("0,0.25,0.5,0.75,1,1.25,1.5,2"),
    )
    parser.add_argument("--padic-depth", type=int, default=6)
    parser.add_argument("--padic-min-support", type=int, default=8)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    close = load_close_csv(args.csv) if args.csv else synthetic_close()
    results = walk_forward(
        close=close,
        train_size=args.train_size,
        test_size=args.test_size,
        vol_window=args.vol_window,
        candidates=args.candidates,
        fee_rate=args.fee_rate,
        abstention_penalty=args.abstention_penalty,
        padic_depth=args.padic_depth,
        padic_min_support=args.padic_min_support,
    )
    payload = report(results)
    print(json.dumps(payload["summary"], indent=2, sort_keys=True))
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    main()
