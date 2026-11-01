# Post-CM-Correction Clay Priority

Date: 2026-06-02

This note records the current priority after correcting the SSP prime
decomposition over `Q(sqrt(-7))`.

For the broader prize-facing dependency board across YM, Gate 3, and NS, see
`Docs/ClayPrizeLemmaRoadmap.md`.  This note is the corrected arithmetic and
Gate 3 priority companion to that board.

The current four-visualisation synthesis does not make the three Clay blockers
symmetric.  It ranks Gate 3 as the most tractable lane, YM as medium
tractability, and NS as the hardest/high-high obstruction lane.  All promotion
flags remain false.

## Corrected State

The `7+7+1` pattern is valid as atom grammar only.  It is not the CM-field
splitting pattern.

The checked CM split over `Q(sqrt(-7))` is:

| Component | Primes | Count |
|---|---|---:|
| Split | `2, 11, 23, 29, 71` | 5 |
| Inert | `3, 5, 13, 17, 19, 31, 41, 47, 59` | 9 |
| Ramified | `7` | 1 |

The important correction is that `p71` splits.  Its role is largest-SSP /
boundary grammar, not inert or self-dual CM-field arithmetic.

The relevant receipts are:

- `SSP15CMFieldSplittingCorrectionReceipt`
- `SSP7Plus7Plus1AtomGrammarReceipt`
- `MonsterMoonshineJDistributionSupportReceipt`
- `Gate3AdelicSobolevNormBindingReceipt`

The Gate 3 frame decomposition is now:

```text
A_N = A_split(5) * A_inert(9) * A_ramified(1)
```

The finite hard part is `A_N > 0`: the corrected inert block needs Mirror-B
phase/twist/dynamics information plus finite separation strong enough for a
Gershgorin-style lower bound.  Phase-blind dictionaries fail on the 9 inert
primes.

## Priority

The next priority is Gate 3, not another carrier-scale YM receipt.

YM now has a carrier-scale spine:

```text
actual p=7 Wilson activity
  -> KP threshold
  -> carrier RG contraction
  -> carrier area law
```

That is still not Clay.  It becomes Clay-relevant only through Gate 3:

```text
carrier control
  -> continuum analytic norm control
  -> no spectral pollution
  -> physical mass shell
```

## Lemmas To Clay

### Gate 3

```text
G3-L1 SplitFrameLowerBound
  A_split(5) > 0
```

Split primes can be distinguished by Mirror-A valuation/amplitude data.

```text
G3-L2 InertPhaseFrameLowerBound
  A_inert(9) > 0
```

This is the first finite load-bearing lemma.  It requires phase/twist/Mirror-B
completeness plus finite separation/Gershgorin control.  Without it the carrier
dictionary has a zero-kernel direction on the inert block.

The PAWOTG/Mosco continuation of this Gate 3 route is the uniform version:
`PAWOTGUniformSeparation`.  It also has a series-side constant condition at the
binding inert prime: the PAWOTG parameter must satisfy
`sigma < sigma_crit(p=3) = 0.5052`.  The tractable attack route is
Weil/Kozyrev: make the adelic atom map explicit, use p-adic Kozyrev/Haar
orthogonality as the model, and prove uniform Archimedean Gaussian localization
below that spread.  Recording the inequality does not prove density, Mosco
recovery, no spectral pollution, or continuum transfer.

```text
G3-L3 RamifiedStructuralBound
  A_ramified(1) > 0
```

The ramified prime is `p=7`, the CM structural prime and YM obstruction scale.

```text
G3-L4 UniformCutoffFrameBound
  inf_N A_N > 0
```

Finite cutoff bounds do not imply continuum density.  This is where finite
experiments must become `PAWOTGUniformSeparation`, not just a collection of
cutoff-specific `A_N > 0` checks.

```text
G3-L5 MoscoRecovery
  H_N -> H_phys
```

Every physical state must be approximable by phase-complete carrier states.

```text
G3-L6 NoSpectralPollution
  low carrier spectrum converges to physical low spectrum
```

No false low-energy states may appear in the cutoff limit.

```text
G3-L7 MassShellBridge
  carrier energy gap -> physical mass-shell gap
```

This is the bridge from carrier estimates to continuum physics.

### Yang-Mills

```text
YM-L1 ActualLocalKPSumBelowOne
  sum_{Gamma contains e0} |z(Gamma)| exp(a |Gamma|) < 1
```

This upgrades threshold bookkeeping into an inhabited KP margin.

For the current analytic constants tranche, use `c_min = 0.242`.  The live
same-prime `p=7` thresholds are `beta > 10.11` for convergence and
`beta > 12.97` for strict activity absorption.  The `beta6` perturbative lane is
divergent with `r = 2.70`, leaving gaps `4.11` and `6.97` from `beta6 = 6` to
the two gates.  This replaces stale `13.64`-only threshold language for live
planning.

The required KP proof is contour/action suppression with entropy `C0` and an
all-diameter geometric bound.  Threshold arithmetic is only admissible after the
actual Wilson activity, contour entropy, and diameter sum are bounded.

The beta-gap visualisation makes this a medium-tractability nonperturbative
problem, not a perturbative one.  With `b0 ~= 0.0465`, crossing the strict
`6.97` beta gap by naive perturbative running would require a scale factor
`exp(6.97 / 0.0465) ~= exp(150)`.  That diagnostic explains why the target is a
Balaban/block-spin bridge through the beta window, while still leaving the YM
promotion flags false.

```text
YM-L2 UniformVolumeKPConvergence
```

The KP margin must be uniform in volume and cutoff.

```text
YM-L3 BalabanRGScaleTransfer
```

The physical weak-coupling trajectory must enter the carrier-safe regime.  This
is the `BalabanPhysicalBetaBridge`; perturbative beta estimates do not currently
close the gap.

```text
YM-L4 CarrierAreaLawUniformInCutoff
```

The carrier area law must survive cutoff removal on the carrier side.

```text
YM-L5 CarrierAreaLawToContinuumMassGap
```

This consumes Gate 3.  It is not available before Gate 3.

```text
YM-L6 OS/WightmanConstruction
```

The continuum QFT construction and reconstruction conditions remain external
Clay-level obligations.

### Navier-Stokes

```text
NS-L1 FixedKLittlewoodPaleyTailIdentity
```

The fixed-cutoff identity must be inhabited with correct signs and constants.

```text
NS-L2 ThetaMarginImpliesTailDecay
```

This is conditional and already clean as margin grammar once NS-L1 is supplied.

```text
NS-L3 DangerShellMaximumPrinciple
```

The danger shell must not cross `theta = 1`.

This must be paired with `NonCircularKStarDriftBound`: prove the actual danger
shell remains under the viscous cutoff, e.g. `K*(t) <= K*(nu)`, before using
fixed-`K` tail decay as continuation evidence.

The theta visualisation should be read as obstruction evidence.  The high-high
paraproduct is load-bearing, and a genuinely non-circular bound may be
equivalent to the regularity step rather than a neutral lemma left open by
notation.

```text
NS-L4 UnconditionalThetaBound
```

This is the Clay-level NS step.

```text
NS-L5 TailDecayControlsBKM/Serrin
```

Tail decay must imply standard continuation criteria.  Theta alone does not give
BKM; the lane also needs `NonCircularKStarDriftBound` plus enough tail/Sobolev
control.

```text
NS-L6 Carrier/EV5-To-ContinuumLift
```

The carrier/EV5 abstraction must faithfully shadow real NS evolution.

## Working Order

1. Prove or refute finite separation/Gershgorin control for `A_N > 0`.
2. Use the Gate 3 atom-frame sweep to test phase-complete versus phase-blind
   collapse on the corrected 9-inert-prime block.
3. Prove `PAWOTGUniformSeparation` or identify the obstruction.
4. In parallel, inhabit `YM-L1 ActualLocalKPSumBelowOne` using the p=7
   enumerator plus contour/action suppression, entropy `C0`, all-diameter
   geometric bounds, `c_min = 0.242`, thresholds `10.11`/`12.97`, divergent
   `beta6` ratio `r = 2.70`, and gaps `4.11`/`6.97`.
5. Continue NS theta sweeps and target `NS-L3 DangerShellMaximumPrinciple`
   together with `NonCircularKStarDriftBound` and enough tail/Sobolev control.

## Shared Lemma To Finish

The common theorem shape after this correction is:

```text
DangerNodeEdgeInfluxBound:
  incomingEdge(v,t) <= epsilon * absorption(v,t)
  with localRatio(v,t) + epsilon < 1
```

The abstract scale-graph barrier algebra is provable once its hypotheses are
supplied.  The missing work is the analytic content behind those hypotheses:
uniform Gate 3 separation, YM contour/action KP control with physical beta
transfer, and NS non-circular `K*` drift plus tail/Sobolev continuation control.

Domain readings:

- Gate 3: `incomingEdge` is cutoff refinement / projection defect.
- YM: `incomingEdge` is block-spin polymer leakage under Balaban RG.
- NS: `incomingEdge` is adjacent-shell leakage into the theta danger shell.

The strict-margin consequence is:

```text
R'_v <= P_v + incoming_v - A_v
P_v <= theta A_v
incoming_v <= epsilon A_v
theta + epsilon < 1
--------------------------------
R'_v <= -(1 - theta - epsilon) A_v
```

Until this edge-influx bound and the lane-specific projection-faithfulness
lemmas are inhabited, the carrier margins remain diagnostics or conditional
interfaces, not Clay proofs.

Final blockers:

- `PAWOTGUniformSeparation`
- `BalabanPhysicalBetaBridge`
- `NonCircularKStarDriftBound`

## Non-Promotion Boundary

None of this proves either Clay problem today.

Allowed claim:

```text
DASHI has corrected the Gate 3 algebraic decomposition and isolated the
load-bearing inert-prime phase-completeness lemma.
```

Forbidden claims:

```text
Gate 3 is closed.
YM mass gap is proved.
NS global regularity is proved.
Clay is solved.
```
