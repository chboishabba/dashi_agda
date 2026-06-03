# YM Balaban Margin Split

This is the concrete Yang-Mills worker receipt that prevents the KP/Balaban
thresholds from being conflated.

## Four Margins

```text
9.593637:
  connected-animal KP convergence

10.13086:
  p=7 BT-tree convergence margin

13.631603:
  exact strict KP absorption / Balaban seed threshold

13.7:
  robust numeric sample for theorem statements

16.56:
  direct T7A counting, demoted because it is worse than connected animal
```

The older bridge receipts also record a legacy strict threshold near `12.97`.
This receipt keeps that as historical/legacy bridge context and declares
`beta*c_min-a>log(2p)` the active exact margin for new Balaban-seed
statements.  The rounded value `13.64` is barely safe; use `13.7` for robust
numeric statements.

## Concrete Routes

```text
ConnectedAnimalKPRoute:
  beta_eff > 9.593637 -> KPConverges

BTTreeConvergenceRoute:
  beta_eff > 10.13086 -> p=7 BT-tree convergence margin

StrictBalabanSeedRoute:
  beta_eff*c_min - a > log(2p) -> strict KP absorption seed for Balaban

T7ADirectCountingRoute:
  beta_eff > 16.56 -> direct T7A count route, demoted
```

## Required Balaban Bridge

```text
NonperturbativeBalabanScaleTransfer:
  beta_phys ~= 6
  -> RGFlow beta_phys beta_eff
  -> beta_eff*c_min - a > log(2p)
  -> StrictBalabanSeed
```

No Yang-Mills, mass-gap, OS/Wightman, continuum, or Clay promotion follows
from this margin split.
