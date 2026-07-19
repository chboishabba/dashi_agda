# Learned ternary abstention boundary

This lane formalises and tests a narrow claim:

> A ternary predictor may improve a binary directional baseline by learning
> when to abstain, while keeping HOLD, FLAT, direction, and execution as
> distinct semantics.

It does **not** claim market predictability or profitable execution.

## Formal contract

`DASHI/Control/LearnedAbstentionBoundary.agda` separates:

1. `Direction = down | neutral | up`
2. `Action = sell | hold | buy | flatten`
3. `Decision.direction` from `Decision.abstain`
4. ordinary decisions from the explicit `RiskDirective.closeExposure`
5. calibration candidates from their validation relation
6. a learned candidate from its optimality certificate
7. static calibration from walk-forward availability

The exact executable invariants are:

- abstention compiles to `hold` for every direction;
- neutral direction does not compile to `flatten`;
- only an explicit close-risk directive compiles to `flatten`;
- executing `hold` preserves exposure definitionally;
- executing `flatten` returns the explicit flat exposure;
- ternary carrier zero is directional neutrality, not an implicit close order.

The calibration record deliberately leaves the loss relation abstract.  The
formal layer should not silently promote a particular financial objective into
a theorem about economic value.

## Executable comparison

`scripts/compare_binary_ternary_predictors.py` provides a deterministic,
walk-forward benchmark with three lanes:

- **binary:** sign of the current return, always active;
- **ternary:** the same direction, but HOLD when normalised signal magnitude is
  below a learned boundary;
- **3-adic suffix backoff:** an optional predictor over recent ternary digits.

The only learned ternary knob is `k` in

```text
abs(current_return) / trailing_volatility >= k
```

`k` is dimensionless and is selected separately on each past-only training
fold from a declared candidate family.  Test rows do not participate in knob
selection.

The validation loss is fixed before evaluation and includes:

- signed next-return decision loss;
- turnover cost;
- an explicit abstention opportunity term.

This is still a baseline rather than a final economic objective.  Its purpose
is to replace embedded magic numbers with a visible, auditable calibration
problem.

## Usage

Synthetic deterministic regime series:

```bash
python scripts/compare_binary_ternary_predictors.py
```

Historical CSV:

```bash
python scripts/compare_binary_ternary_predictors.py \
  --csv path/to/bars.csv \
  --json-out benchmarks/results/binary-ternary-walk-forward.json
```

The CSV must contain a `close` column; a `timestamp` column is recommended but
is not required by the current runner.

Useful ablations:

```bash
# Disable the 3-adic lane
python scripts/compare_binary_ternary_predictors.py --padic-depth 0

# Collapse ternary to the always-active boundary
python scripts/compare_binary_ternary_predictors.py --candidates 0

# Change only the finite candidate family
python scripts/compare_binary_ternary_predictors.py \
  --candidates 0,0.125,0.25,0.5,1,2
```

## Interpretation discipline

A useful result is not merely higher aggregate net return.  Report at least:

- active directional accuracy;
- coverage/HOLD rate;
- turnover;
- cost-adjusted return under identical execution assumptions;
- selected-boundary stability across folds;
- 3-adic suffix coverage and accuracy;
- performance dispersion rather than only the mean.

A ternary advantage is supported only when it survives unchanged execution,
walk-forward separation, candidate-family ablation, and multiple time periods.
