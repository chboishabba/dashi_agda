#!/usr/bin/env python3
"""Development-only diagnostics for the Occupy governance evidence lane.

Inputs are the six development OWS records whose source text explicitly pays a
meeting duration. No prospective-holdout record appears in this script.

The lexical fields are DASHI-derived counts from
OccupyOWSDevelopmentTextProcessPanelExact.agda.  This script tests only whether
a one-predictor ordinary-least-squares model improves leave-one-out mean
absolute error over an intercept-only development baseline.  It does not
estimate coordination burden or a causal effect.
"""

ROWS = [
    dict(index=3, duration=450, words=182, consensus=3, block=0, proposal=0, anon=0),
    dict(index=26, duration=140, words=5337, consensus=4, block=0, proposal=13, anon=8),
    dict(index=28, duration=440, words=14678, consensus=24, block=20, proposal=65, anon=17),
    dict(index=38, duration=60, words=2708, consensus=1, block=1, proposal=3, anon=21),
    dict(index=40, duration=65, words=2673, consensus=0, block=1, proposal=2, anon=32),
    dict(index=43, duration=220, words=14643, consensus=31, block=26, proposal=72, anon=99),
]


def mean(xs):
    return sum(xs) / len(xs)


def ols_predict(train, row, feature):
    xs = [r[feature] for r in train]
    ys = [r["duration"] for r in train]
    xm, ym = mean(xs), mean(ys)
    sxx = sum((x - xm) ** 2 for x in xs)
    if sxx == 0:
        return ym
    slope = sum((x - xm) * (y - ym) for x, y in zip(xs, ys)) / sxx
    intercept = ym - slope * xm
    return intercept + slope * row[feature]


def loo_mae(feature=None):
    errors = []
    for i, row in enumerate(ROWS):
        train = [r for j, r in enumerate(ROWS) if j != i]
        if feature is None:
            prediction = mean([r["duration"] for r in train])
        else:
            prediction = ols_predict(train, row, feature)
        errors.append(abs(prediction - row["duration"]))
    return mean(errors)


if __name__ == "__main__":
    models = [("intercept", None)] + [(x, x) for x in ("words", "consensus", "block", "proposal", "anon")]
    scores = [(name, loo_mae(feature)) for name, feature in models]
    for name, score in scores:
        print(f"{name:10s} LOO_MAE_minutes={score:.6f}")
    baseline = scores[0][1]
    promoted = [(name, score) for name, score in scores[1:] if score < baseline]
    print("nontrivial_models_beating_baseline=", promoted)
