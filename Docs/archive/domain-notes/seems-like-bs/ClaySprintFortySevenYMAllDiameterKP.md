# Clay Sprint 47B YM All-Diameter KP Target

Date: 2026-06-04

Sprint 47B records the next Yang-Mills proof target without extending the
diagnostic harness.

The required theorem is:

```text
AllDiameterKPActivityBound:
  exists A q,
    q < 1
    and forall diameter d,
      KPActivity(d) <= A * q^d
```

## Why No Harness Change

The Sprint 43 YM harness already records geometric KP/rho/leakage diagnostics
and fail-closes unless actual all-diameter certificate columns are supplied.
There is not yet a real certificate input for:

```text
actual Wilson activity envelope
uniform constants
actual KP incompatibility neighborhood
tail closure below one
```

Changing the harness now would only rename an open proof gate.

## Open Gates

Sprint 47B leaves these gates open:

```text
AllDiameterKPActivityBound
certificate input format
continuumUniformRhoBound
continuumUniformLeakageBound
YMBalabanContinuumLimitWithUsableMargin
constructive QFT terminal stack
mass gap
```

## Boundary

This is a theorem-target receipt only.  It supplies no all-diameter certificate,
no continuum rho/leakage proof, no Balaban continuum transfer, no mass gap, and
no Clay Yang-Mills promotion.
