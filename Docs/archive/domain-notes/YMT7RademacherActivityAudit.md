# YM T7 Direct Activity Audit

This note records the corrected T7 entropy accounting for the Yang-Mills lane.
The direct `T7A` KP sum is a proved diagnostic, not the best counting route:

```text
KPSum(beta) = sum_{d >= 1} c7(d) * exp(-beta * c_min * d)
KPSum(beta) < 1  at  beta* ~= 16.56
gap from beta_phys = 6: Delta beta ~= 10.56
```

The connected-animal count gives the better standard KP route:

```text
polymer_count(d) <= d * p^(d-1)
beta*_connectedAnimal ~= 9.593637
gap from beta_phys = 6: Delta beta ~= 3.593637
```

This resolves the old `C0 = 2` ambiguity.  `C0 = 2` is a rough heuristic, and
direct `T7A` is too large at small depths to replace connected-animal
counting.

The depth `1..3` coefficient audit compares the McKay-Thompson `T7A`
coefficients against the raw Monster `j` coefficients:

```text
d=1: T7A/j = 51 / 196884      ~= 2.59e-4
d=2: T7A/j = 204 / 21493760   ~= 9.49e-6
d=3: T7A/j = 681 / 864299970  ~= 7.88e-7
```

These sampled ratios sit below the Rademacher suppression envelope
`exp(4*pi*sqrt(d)*(1/sqrt(7)-1))` at depths `1`, `2`, and `3`.  This verifies
the T7 compression check at the audited depths.

The earlier envelope audit still separates the surrogate regimes:

```text
raw Monster j envelope      -> C0 ~= 287000, beta* ~= 64.9
T7 Rademacher envelope      -> C0 ~= 115.5,  beta* ~= 32.6
activity target C0 = 2      -> C0 = 2,       beta* ~= 15.9
```

The follow-up computation supersedes those surrogate regimes for the direct
T7A diagnostic, but not for the best KP count.  The correct receipt statement
is:

```text
T7ActivityIdentificationLemma:
  KPThreshold_connectedAnimal = 9.593637
  GapFromPhysical_connected   = 3.593637
  KPThreshold_T7A_direct      = 16.56
  GapFromPhysical_T7A         = 10.56
  T7A_is_best_counting_route  = false
  correctStatement       =
    T7A helps only if it proves per-polymer activity suppression:
    |z(Gamma)| <= (T7A(d)/(d*p^(d-1))) * exp(-beta*c_min*d)
```

The observed `T7A(d)/7^d` ratios decay across depths `1..5`:

```text
7.29, 4.16, 1.99, 0.88, 0.36
```

That explains why the old `C0 = 2` heuristic looked plausible near depth `3`,
but it does not make `C0 = 2` a formal theorem.

After this audit, the YM lane records:

```text
ymT7RademacherBoundVerified = true
ymT7DirectKPSumThresholdComputed = true
ymT7DirectKPSumIsBestCountingRoute = false
ymConnectedAnimalBoundComputed = true
ymBetaThreshold_connectedAnimal = 9.593637
ymBetaThreshold_T7A_direct = 16.56
ymBalabanGapFromPhysical_connected = 3.593637
ymC0TwoActivityIdentificationProved = false
clayYangMillsPromoted = false
```

The remaining Clay-relevant obligation is no longer basic entropy
bookkeeping.  Connected-animal convergence is KP-only; the non-perturbative
Balaban bridge must reach the strict seed inequality
`beta*c_min-a>log(2p)` with a robust numerical target such as `beta_eff >= 13.7`,
optionally strengthened by a T7A per-polymer activity-suppression theorem,
followed by OS positivity, infinite-volume construction, and Wightman
reconstruction.
