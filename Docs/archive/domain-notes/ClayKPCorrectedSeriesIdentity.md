# Clay KP Corrected Series Identity

This note records the connected-animal KP formula correction as an inhabitable
repo-governance surface.

The Agda receipt is:

```text
DASHI/Physics/Closure/ClayKPCorrectedSeriesIdentityReceipt.agda
```

## Correct Formula

For connected-animal counting, the formula is:

```text
sum_{d >= 1} d * p^(d - 1) * q^d = q / (1 - p*q)^2
```

The old expression:

```text
p*q / (1 - p*q)^2
```

is rejected for this route.  The receipt records that distinction mechanically
with:

- `correctedClosedFormTextIsQOverOneMinusPqSquared`
- `legacyWrongClosedFormTextIsPqOverOneMinusPqSquared`
- `correctedClosedFormIsPrimary`
- `legacyWrongClosedFormIsRejected`
- `legacyWrongClosedFormAllowedAsKPRouteIsFalse`

## What This Buys

This closes the repo-internal formula-choice hazard.  The connected-animal
route now consistently uses the corrected expression and the precision receipt:

```text
beta_CA = 9.593637
gap_CA  = 3.593637
```

The receipt also consumes the solved ledger guard:

```text
connectedAnimalThresholdMillis = 9594
```

so the rounded `9.59` value is not used as a strict theorem statement.

## What It Does Not Buy

The receipt does not formalise the analytic infinite-series proof in Agda.
It records the corrected formula and the governance consequences only.

It also does not prove:

- strict Balaban seed
- nonperturbative Balaban transfer
- Shimura-to-Euclidean universality
- OS/Wightman reconstruction
- continuum mass-gap survival
- Clay Yang-Mills

The strict Balaban seed remains:

```text
beta * c_min - a > log(2p)
```

or, for a robust numeric sample:

```text
beta_eff >= 13.7
```

## Worker Assignment

- `W1-YM-KP-Activity`: owns the corrected connected-animal formula surface.
- `W2-YM-Balaban-RG`: may consume this only as KP convergence support, not as a
  strict Balaban seed.
- `W6-Governance`: owns the rejection of the old `p*q/(1-p*q)^2` formula and
  the false-promotion boundary.

## Boundary

This receipt is a concrete, inhabitable ledger update.  It prevents the old KP
formula from silently re-entering the Clay route.  It does not solve Clay.
