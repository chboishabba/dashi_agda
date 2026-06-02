# YM Paper 3 Clay Target

This note records the Paper 3 Yang-Mills spine as a carrier-scale result with
an explicit Clay boundary.  It is not a continuum Yang-Mills proof and it does
not promote a Clay mass-gap claim.

## 2026-06-02 Character-Expansion Reformulation

The current reformulation is checked in:

```text
DASHI/Physics/Closure/YMCharacterExpansionContinuumReformulationReceipt.agda
```

The Osterwalder-Seiler / transfer-matrix character-expansion calculation gives
a fixed-lattice lower bound:

```text
m_latt(beta) >= -2 log(I1(beta) / I0(beta)) > 0.
```

The recorded numerical anchors are:

```text
beta = 6.00:  m_latt >= 0.183
beta = 12.97: m_latt >= 0.080
```

This clarifies the target.  The Clay problem is not fixed-lattice positivity
at `beta=6`; it is survival of a physical mass scale in the continuum limit as
`a(beta)->0` and `beta->infinity`.  The character bound weakens as
`I1/I0 -> 1`, so this calculation does not replace the nonperturbative
Balaban/continuum bridge.  It says precisely where the bridge must act:
control the rate of vanishing and preserve a nonzero continuum mass scale.

## Proof Chain

The Agda receipt is:

```text
DASHI/Physics/Closure/YMPaper3ClayTargetReceipt.agda
```

It integrates the A-lane chain:

```text
actualActivity
  -> KP
  -> Balaban
  -> carrierAreaLaw
  -> Gate3(open)
  -> continuumMassGap(open)
```

The carrier-side area-law stage is recorded as available in the finite /
conditional carrier sense:

```text
carrierAreaLawProved = true
```

This means the Paper 3 spine has a carrier area-law target to write around.
It does not mean the continuum Yang-Mills mass gap has been proved.

## Corrected Quantified Gap

The live physical-normalised constants are:

```text
c_min = 0.242
p = 7
a = 0.5
beta_KP_convergence ~= 10.11
beta_KP_strict_absorption ~= 12.97
```

The binary-to-tetralemma margin governance now records the interval
`10.11 < beta < 12.97` as the `both` state: the KP series is convergent, but
the sum is not yet strictly absorbing.  That is a real diagnostic distinction,
not a YM mass-gap theorem.

## Entropy-Constant Sensitivity

The second-pass calculation generated:

```text
Docs/Images/clay-analytic-sprint/ym_c0_threshold_sensitivity.csv
```

The refined threshold is:

```text
beta_abs(C0) = (a + log(2 p C0)) / c_min
```

So `C0` is load-bearing.  With the current `p=7`, `a=0.5`,
`c_min=0.242` normalization:

```text
C0 = 0.50 -> beta_abs = 10.10706673
C0 = 0.75 -> beta_abs = 11.78254238
C0 = 1.00 -> beta_abs = 12.97131128
C0 = 1.25 -> beta_abs = 13.89339207
```

Any entropy constant above `1` worsens the Balaban bridge target.

The checked receipt
`DASHI/Physics/Closure/YMC0EntropyThresholdSensitivityReceipt.agda` records the
current canonical sensitivity table for `C0 = 0.5, 1, 2, 5`: beta absorption
thresholds `10.107`, `12.971`, `15.836`, and `19.622`, with gaps above
physical beta `6` of `4.107`, `6.971`, `9.836`, and `13.622`.

Moonshine/15SSP language enters here only as a possible quotient/compression
control, not as an entropy multiplier.  The new governance blocker is
`MonsterMoonshineSSPQuotientControl`: prove that the 15SSP/moonshine carrier
really quotients or compresses the raw contour family before using the
`C0 ~= 1` threshold.  The raw ratio `c2/c1 ~= 109` is not the physical polymer
entropy constant `C0`.  If the quotient theorem holds, the working
`C0_eff ~= 1` target keeps `beta_abs ~= 12.97`; if only a square-root leak or
raw leak survives, the effective thresholds rise to about `22.66` or `32.35`.
This is a non-promoting blocker, not a quotient theorem and not Clay evidence.

The later `T_7` quotient evidence refines the stress model:

```text
DASHI/Physics/Closure/YMMonsterQuotientEvidenceReceipt.agda
```

It records raw Monster `c2=21493760`, McKay-Thompson `T_7(q^2)=204`,
compression by about `105000`, conservative `C0_eff~=2`, and
`beta_abs~=15.836`.  This supports a finite positive route but leaves the
nonperturbative Balaban bridge from physical beta around `6` open.

The Monster re-2 stress table is staged at:

```text
Docs/Images/clay-analytic-sprint/ym_monster_re2_C0_thresholds.csv
```

It records:

```text
c1 = 196884
c2 = 21493760
c2 / c1 ~= 109.17
sqrt(c2 / c1) ~= 10.45
irrep2 / irrep1 ~= 108.17
sqrt(irrep2 / irrep1) ~= 10.40
```

The resulting strict-absorption stress thresholds are:

```text
C0 = 1                         -> beta_abs = 12.9713
C0 = log(c2/c1) ~= 4.69        -> beta_abs = 19.3600
C0 = sqrt(irrep2/irrep1)       -> beta_abs = 22.6484
C0 = sqrt(c2/c1)               -> beta_abs = 22.6674
C0 = irrep2/irrep1             -> beta_abs = 32.3255
C0 = c2/c1                     -> beta_abs = 32.3635
```

The checked cross-lane receipt is
`DASHI/Physics/Closure/MonsterMoonshineSSPQuotientControlReceipt.agda`.  It
keeps quotient control, YM mass gap, and Clay promotion false.

The newer McKay-Thompson calculation gives positive quotient evidence and is
recorded in:

```text
DASHI/Physics/Closure/YMMonsterQuotientEvidenceReceipt.agda
```

For the `p=7` lane, the relevant Hauptmodul is the McKay-Thompson series
`T_7`, not the raw `j`-function.  Its `q^2` coefficient is `204`, compared to
the raw Monster `c2 = 21493760`, a compression factor of about `105000`.  A
conservative normalization using the `T_7` ratio gives `C0_eff ~= 2` and
therefore `beta_abs ~= 15.836`: harder than the baseline `12.971`, but far
from the raw-Monster stress thresholds `22.66`/`32.35`.  This is evidence for
the quotient-control route, not the quotient theorem itself.

The physical/lattice diagnostic recorded for the paper target is:

```text
beta_physical ~= 6
```

At `beta_physical ~= 6`, the KP ratio is:

```text
r(beta=6) ~= 2.70 > 1
```

So the physical/lattice beta diagnostic diverges, and the Balaban/RG beta
gaps are:

```text
10.11 - 6 = 4.11       -- convergence
12.97 - 6 = 6.97       -- strict activity absorption
```

This is the precise gap the paper should expose: the carrier area-law route
cannot start at physical `beta ~= 6` under the live `c_min = 0.242`
normalisation.  The RG scale-transfer argument must raise the effective beta
past convergence and, for the strict KP absorber, past `12.97`.

The evidence bundle for these constants is:

```text
Docs/Images/clay-analytic-sprint/ym_p7_polymer_kp.csv
Docs/Images/clay-analytic-sprint/ym_kp_sum_vs_beta.png
Docs/Images/clay-analytic-sprint/ym_kp_sum_vs_beta_1.png
Docs/Images/clay-analytic-sprint/ym_kp_sum_vs_beta_2.png
```

The table records:

```text
beta = 6.0:    r = 2.7017782, divergent
beta = 10.13: r = 0.99446552, convergent but not sum < 1
beta = 12.97: r = 0.50015869, boundary-level strict sum
beta = 13.64: r = 0.42529601, strict sum < 1 in the supplied sample
```

So `12.97` is the live computed strict boundary, while `13.64` is best treated
as a conservative sampled safe point.  Neither point proves the physical beta
bridge.

The revised KP proof obligation is contour/action suppression, not threshold
bookkeeping alone.  Paper 3 should state the local-sum target as:

```text
sum_{contours Gamma containing e0}
  exp(C0 * entropy(Gamma)) * exp(-S_Wilson(Gamma))
< 1
```

with a volume-uniform entropy constant `C0`, actual Wilson-action suppression,
and an all-diameter geometric bound.  The all-diameter step must dominate the
number of contours at every diameter, not just a fixed-radius shell.  Toy rho,
bare BT branching, or perturbative beta language cannot replace this estimate.

## Remaining Open Gates

The receipt keeps the remaining promotion gates false:

```text
continuumMassGapProved = false
gate3BridgeOpen = true
clayYMMassGapPromoted = false
```

Gate 3 remains open at:

- finite `A_N > 0` from finite separation plus a Gershgorin lower bound;
- `PAWOTGUniformSeparation`, the uniform refinement version of finite
  separation needed by density/Mosco;
- no-spectral-pollution / isolated-sector control;
- carrier-energy to physical mass-shell transport;
- continuum Yang-Mills construction and mass-gap promotion.

The YM-specific blocker is `BalabanPhysicalBetaBridge`: after contour/action KP
control exists in the carrier-safe regime, the physical beta trajectory must be
bridged into that regime without promoting perturbative estimates to a
nonperturbative Balaban theorem.

The blocker classification is checked at:

```text
DASHI/Physics/Closure/ClayBlockerAsymmetryReceipt.agda
```

For YM, this records `BalabanPhysicalBetaBridge` as quantitative completion of
the Balaban RG programme with the measured beta gap, not as a solved carrier
threshold comparison and not as a symmetric peer of the NS paraproduct
obstruction.

## Why The Beta Bridge Is Still Open

The sprint quantified the target but did not bridge it.  A Clay-level bridge
would need to prove that the nonperturbative Balaban/block-spin flow carries
the physical lattice normalization around beta `6` into the KP-safe carrier
regime, while keeping polymer activities and generated correction terms under
uniform control.  The perturbative beta function gives heuristic running, but
it is not a replacement for the finite-volume/infinite-volume small-field and
large-field estimates required by a Balaban theorem.

Thus Paper 3 can honestly publish the reduction:

```text
beta 6 is KP-divergent;
strict carrier absorption starts at the measured safe regime;
the missing theorem is BalabanPhysicalBetaBridge.
```

It cannot publish a continuum mass-gap proof until that bridge and the Gate 3
transfer are inhabited.

## Submission Angle

Paper 3 should be framed as a carrier-scale theorem spine plus a sharply
quantified Clay gap.  The strongest honest claim is:

```text
Carrier area-law target uses the live p=7 KP thresholds
beta_convergence ~= 10.11 and beta_strict_absorption ~= 12.97;
physical beta ~= 6 is divergent with r ~= 2.70, so Balaban/RG must
close gaps ~= 4.11 and ~= 6.97.
```

The paper can present the A1-A4 chain as evidence that the carrier side is now
organized enough to state a precise target.  It must not claim a Clay
Yang-Mills proof until the Gate 3 and continuum mass-shell bridges are
inhabited.

Final Paper 3 blockers:

- `PAWOTGUniformSeparation`
- `BalabanPhysicalBetaBridge`

## Quantitative Physical Beta Bridge Reduction

The next checked receipt is
`DASHI/Physics/Closure/YMBetaBridgeQuantitativeGapReceipt.agda`.
It records the physical beta bridge as a nonperturbative theorem target:

```text
physical beta ~= 6
KP convergence beta ~= 10.11
strict KP absorption beta ~= 12.97
gap to convergence ~= 4.11
gap to strict ~= 6.97
```

The perturbative diagnostic is deliberately negative.  With the one-loop
coefficient recorded as `b0 ~= 0.0465`, a naive perturbative scale bridge for
the strict gap requires:

```text
exp(6.97 / 0.0465) ~= exp(150) ~= 1e65
```

Equivalently, this is an `~1e65` scale ratio.  That is not a proposed RG proof;
it rules out the perturbative bridge as a practical finite proof and is the
reason the proof must be nonperturbative.  Paper 3 should use this as the
clean statement of the Balaban gap:

```text
carrier KP/Balaban control is available only after the physical theory is
connected to the carrier-safe beta window by a nonperturbative block-spin
or strong-coupling bridge.
```

The nonperturbative crossover beta window remains:

```text
beta in [2,10.11]
```

No continuum Yang-Mills construction, physical mass gap, or Clay promotion
follows from recording the gap.

The target receipt
`DASHI/Physics/Closure/YMBalabanPhysicalBetaBridgeTargetReceipt.agda`
now pins down the exact next theorem shape after that quantitative gap:

```text
physical beta ~= 6
  -> nonperturbative block-spin/RG flow
  -> KP-safe carrier beta > 12.97
  -> strict activity absorption
  -> carrier area law connected back to the physical lane
```

It records the open obligations explicitly: strong/weak coupling
interpolation, polymer activity control through the crossover, summable RG
corrections, reflection positivity/OS compatibility through the flow, and a
separate continuum construction.  It keeps `perturbativeBridgeSuffices=false`,
`nonperturbativeInputRequired=true`, and all YM/Clay promotion flags false.
