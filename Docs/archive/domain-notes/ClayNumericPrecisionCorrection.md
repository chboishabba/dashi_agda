# Clay Numeric Precision Correction

This note records the sharper numeric ledger behind the existing coarse
hundredths-level Clay bookkeeping.

The Agda surface is:

```text
DASHI/Physics/Closure/ClayNumericPrecisionCorrectionReceipt.agda
```

The formula-choice governance surface is:

```text
DASHI/Physics/Closure/ClayKPCorrectedSeriesIdentityReceipt.agda
```

## Corrected YM Numbers

For connected-animal counting,

```text
sum_{d >= 1} d * p^(d - 1) * q^d = q / (1 - p*q)^2
```

The separate KP identity receipt records this corrected expression and rejects
the legacy `p*q/(1-p*q)^2` expression for this route.  It does not formalise
the analytic infinite-series theorem in Agda.

with `p = 7` and `c_min = 0.242`, the threshold is:

```text
beta_CA = 9.593637
gap_CA  = 3.593637
```

This is KP convergence only.  It is not a Balaban seed and should not be used
to claim Balaban induction.

Under the BT-tree convention `a = 0.06`, `c_min = 0.198`:

```text
beta_BT     = 10.13086
gap_BT      = 4.13086
beta_strict = 13.631603
gap_strict  = 7.631603
```

The rounded ledger values remain readable:

```text
9.594, 10.13, 13.64, 16.56
```

The safe active Balaban seed is the strict condition:

```text
beta * c_min - a > log(2p)
```

`13.64` is barely above the precise strict threshold in the `c_min = 0.198`
convention.  The beta-space clearance is about `0.008397`, while the strict
inequality residual at `13.64` is only about `0.00166`.  A more robust numeric
theorem should either keep the exact
inequality or use a sample such as:

```text
beta_eff >= 13.7
```

## Gate3 PAWOTG Precision

For the one-density PAWOTG series

```text
S_p(sigma) = sum_{d >= 1} p^d * exp(-((log p)^2 * d^2) / (4*sigma^2))
```

at `p = 3`:

```text
sigma_digit  = 0.288675
sigma_target = 0.302511
sigma_crit   = 0.505208

S_3(sigma_digit)  = 0.080284628
S_3(sigma_target) = 0.110976368
```

So the taper arithmetic has slack in the one-density model.  The live Gate3
blocker remains the bridge:

```text
PhysicalSSPEmbedding3D -> PhysicalSSPSpreadBound
```

The receipt explicitly separates this one-density calculation from the
three-density gravity/physical-spread target that uses `0.302511` as the
binding physical spread threshold.

## Worker Assignment

- `W2-YM-Precision`: owns the precise YM threshold and margin ledger.
- `W5-Gate3-Taper-Precision`: owns the one-density PAWOTG arithmetic and its
  separation from physical 3D embedding.
- `W6-Governance-Precision`: owns the rule that numerical slack does not
  promote open analytic lemmas.

## Boundary

This receipt proves only numeric ledger refinements.  It does not prove
nonperturbative Balaban transfer, Shimura-to-Euclidean universality,
OS/Wightman reconstruction, mass-gap survival, NS cumulative tail dominance,
projection-defect absorption, physical SSP spread, uniform frame lower bound,
Gate3 closure, or Clay.
