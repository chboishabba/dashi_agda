# Clay Optimal Path Requisite Lemmas

This note records the current optimal work order after the connected-animal
KP correction and the kernel compression.

The right order is not all Clay-facing lanes at once:

```text
1. Yang-Mills first, because it has the sharpest computable obstruction.
2. Navier-Stokes Path A as a publishable obstruction and Path B as Clay.
3. Gate3/W4/gravity separately as broader physics-programme infrastructure.
```

Nothing here flips a promotion flag.  Each item below is a missing theorem
target unless an existing receipt already says otherwise.

## Tier 1: Yang-Mills Clay Path

The YM campaign is the highest-payoff Clay route because the entropy side now
has a concrete standard target:

```text
sum_{d >= 1} d * p^(d-1) * exp(-beta*c_min*d) < 1
beta* ~= 9.593637
gap from beta_phys ~= 6: 3.593637
```

The direct `T7A` KP series is also proved, with `beta* ~= 16.56`, but it is a
worse counting route.  T7A remains valuable only if it proves per-polymer
activity suppression.

The stricter KP ledger now keeps three YM margins separate:

```text
connected-animal sum threshold: beta* ~= 9.593637
p=7 BT-tree convergence threshold: beta* ~= 10.13086, gap ~= 4.13086
stricter p=7 KP activity-absorption margin: beta*c_min-a>log(2p)
```

Use `beta_eff >= 13.7` as the robust numerical Balaban transfer target when the
stricter margin is the active convention; use `9.593637` only for the plain
connected-animal sum.

Required lemmas:

```text
YM-1  Connected-animal KP series bound
YM-2  T7A per-polymer activity suppression for actual Wilson polymers
YM-3  Carrier KP -> Balaban contraction
YM-4  Physical beta bridge: beta_phys ~= 6 -> beta_eff above the active
      KP margin (`9.593637`, `10.13086`, or the strict seed inequality)
YM-5  Uniform continuum mass gap
YM-6  Gauge-fixed OS positivity / ghost-sector control
YM-7  OS/Wightman reconstruction
YM-8  Constructive 4D YM mass-gap promotion theorem
```

The local YM geometry remains a second-tier maturation track:

```text
YM-G1 Non-flat SFGC curvature
YM-G2 Holonomy conjugation / gauge covariance
YM-G3 Covariant derivative on the selected gauge bundle
YM-G4 Hodge star plus variation / integration by parts
YM-G5 Bianchi identity and sourced field equation D_A * F_A = J
```

These are needed to stop the internal geometry from being finite/local only,
but they do not by themselves prove the mass gap.

## Tier 2: Navier-Stokes

Path A is publishable obstruction:

```text
NS-A1 H^{-1/2} obstruction theorem
```

Path B is Clay-facing:

```text
NS-B1 Leray band bound
NS-B2 Prime-scale Bernstein inequality
NS-B3 H^{11/8} Bernoulli-band global bound
NS-B4 K* drift non-circularity
NS-B5 Existence/stability before uniqueness
NS-B6 Carrier-to-all-smooth-data extension
NS-B7 Clay NS promotion theorem
```

The central risk is circularity: any `K*` proof that imports global
regularity, Serrin, BKM, or the desired `H^{11/8}` bound fails the route.

## Tier 3: Gate3 / W4 / Gravity Infrastructure

This lane should not block the Clay papers unless a specific YM continuum
transfer consumes it.  It remains essential for the broader DASHI physics
programme:

```text
G3-1 Physical SSP/Hecke embedding spread:
     sigma_physical_SSP < 0.3025113508228815

G3-2 SSP frame uniform lower bound:
     A_split > 0, A_inert > 0, A_71 > 0 -> UniformCutoffLowerBound

G3-3 Mosco / no-spectral-pollution / isolated mass-shell transfer

W4-1 Candidate256 physical calibration external receipt

W4-2 Wald / stress-energy selection and conservation authority

GR-1 Schwarzschild weak-field match
```

## Six Parallel Workers

```text
W1-YM-Activity:
  YM-1, YM-2, connected-vs-T7A KP comparison, and small-depth activity
  suppression kill-tests.

W2-YM-Balaban:
  YM-3, YM-4, YM-5, non-perturbative beta bridge and continuum gap.  This
  lane must state which margin it closes: `9.593637`, `10.13086`, or the
  exact strict seed inequality.

W3-YM-OS-Geometry:
  YM-6, YM-7, YM-G1..YM-G5, gauge-fixed OS and field-equation maturity.

W4-NS:
  NS-A1 for publication, then NS-B3, NS-B4, NS-B5, NS-B6 for Clay.

W5-Gate3-W4-GR:
  G3-1..G3-3, W4-1, W4-2, GR-1 as physics infrastructure.

W6-Governance:
  source-map upkeep, kill-test records, promotion-flag audit, changelog/TODO.
```

## What This Buys

The repo now has a finite, ranked set of requisite lemmas.  The highest-yield
first theorem is now:

```text
NonperturbativeBalabanScaleTransfer
+ HyperbolicShimuraToEuclideanUniversality
```

T7A per-polymer activity suppression remains an improvement theorem, not the
primary counting route.

All Clay, Gate3, gravity, W4, Schwarzschild, YM, NS, and terminal promotion
flags remain false.
