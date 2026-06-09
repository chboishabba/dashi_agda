# YM Margin-Parametric Balaban Receipt

Canonical receipt:
`DASHI/Physics/Closure/YMMarginParametricBalabanReceipt.agda`

## Closed Diagnostic

The one-loop diagnostic still records three useful computations:

- scale selection crosses the bare seed near `k ~= 42.2`
- post-seed `q < 1` at the diagnostic level
- leakage is geometrically tiny in the one-loop model

These are diagnostics only.

## Failed Naive Transfer

The finite `43`-step target is not accepted as a proof target for Clay YM.
The live theorem must be continuum-uniform in the initial lattice scale and
nonperturbative corrections.

## Margin Tiers

The strict seed is:

```text
beta * c_min - a > log(2p)
```

with the current p=7 BT convention giving:

- bare seed: `beta ~= 13.631603`
- weak robust target: `beta >= 13.7`, `rho ~= 0.98655`
- usable contraction: `beta ~= 14.1637`, `rho <= 0.90`
- strong contraction: `beta ~= 15.0845`, `rho <= 0.75`

The one-loop step diagnostics shift accordingly:

- bare seed: `k ~= 42.2`
- `rho <= 0.90`: `k ~= 45.1`
- `rho <= 0.75`: `k ~= 50.2`

## Remaining Promotion Lemma

The exact YM blocker is:

```text
YMBalabanContinuumLimitWithMargin
```

It requires continuum-uniform rho bounds and continuum-uniform leakage bounds.
All Yang-Mills and Clay promotion flags remain false.
