# Clay Prize Lemma Roadmap

Status: prize-facing lemma board; non-promoting.

This document answers the narrow question: what lemmas would take the current
DASHI programme from its present proof architecture to actual Clay-level
claims?  It is not a proof of Navier-Stokes, Yang-Mills, Gate 3, or full
unification.

The current repo has the shared grammar, the scale-graph theorem shape, the
NS theta surface, the YM KP/Balaban surface, and the Gate 3 cutoff-frame
surface.  The missing work is not more vocabulary.  It is a short list of
analytic inhabitants that turn the margin surfaces into genuine estimates.

## Canonical Final Frontier Map

The checked citation point for "what remains for Clay?" is now:

```text
DASHI/Physics/Closure/ClayFinalAnalyticFrontierMapReceipt.agda
```

That receipt records the solved shared component and the exact remaining
frontier surfaces:

| Layer | Existing Agda surfaces | Clay-level inhabitant still missing |
| --- | --- | --- |
| Shared algebra | `ScaleGraphBarrierAlgebraProofReceipt`, `UniversalScaleGraphBarrierTargetReceipt` | Lane-specific edge laws and analytic hypotheses; the algebra alone does not close a lane. |
| Margin governance | `BinaryTetralemmaMarginStateReceipt` | Nothing analytic: this is a governance refinement.  It records true/false/both/neither diagnostic states while keeping binary fail-closed promotion. |
| Monster / entropy control | `MonsterMoonshineSSPQuotientControlReceipt` | `MonsterMultiplicityQuotientControl`: raw `q^2`/second-irrep growth must be quotiented before YM `C0` or Gate 3 overlap entropy consume it. |
| Gate 3 | `Gate3PAWOTGUniformSeparationTargetReceipt`, `Gate3NestingTaperConditionReceipt`, `Gate3MoscoConstructiveSequenceReceipt`, `Gate3NoSpectralPollutionConditionalProofReceipt` | `PAWOTGUniformSeparation`, Gaussian taper damping of Archimedean parent-child nesting below the binding `p=3` threshold, then Mosco/no-pollution/mass-shell transfer. |
| YM | `YMC0EntropyThresholdSensitivityReceipt`, `YMBalabanPhysicalBetaBridgeTargetReceipt`, `YMPhysicalBetaBridgeOpenReceipt`, `CarrierOS3ReflectionPositivityReceipt`, `WightmanReconstructionCandidateReceipt` | Actual all-diameter KP with the effective quotient-controlled `C0`, the nonperturbative Balaban physical beta bridge, and continuum OS/Wightman mass-gap transfer. |
| NS | `NSTailRestrictedThetaDiagnosticReceipt`, `NSNegativeSobolevDangerShellReceipt`, `NSNonCircularKStarDriftBoundTargetReceipt`, `NSDangerShellMaximumPrincipleReceipt` | Tail-restricted theta barrier, non-circular high-high `H^{-1/2}` defect control, `K*` drift containment, and the danger-shell maximum principle. |

The receipt keeps all promotion channels empty and all Clay flags false.  It is
an index of related proof surfaces and remaining theorem targets, not a theorem
inhabitant for any Clay problem.

## 2026-06-02 Computed Lemma Update

The latest computation sharpens all three final blockers without promoting
any of them.

### Binary To Tetralemma Margin Governance

The shared barrier remains binary at the final promotion point:

```text
P + I < A
theta + epsilon < 1
```

But the diagnostics are now recorded as four-valued:

| State | Meaning | Sprint example |
| --- | --- | --- |
| True | absorbed; pressure decreases | Gate 3 digit expansion passes the strict taper. |
| False | leaking; absorber loses | NS local `H^-1/2` absorption ratio diverges as viscosity decreases. |
| Both | mixed; convergence without strict absorption or split diagnostics | YM beta between convergence and strict absorption. |
| Neither | wrong seam/out of domain | `Theta_global` dominated by low `k=2` rather than the tail seam. |

Checked receipt:

```text
DASHI/Physics/Closure/BinaryTetralemmaMarginStateReceipt.agda
```

This is governance only.  It does not promote PAWOTG, YM, NS, Gate 3, Clay, or
terminal closure.

### Taper And H^-1/2 Obstruction Refinement

The Gate 3 taper calculation now has a stricter threshold hierarchy:

```text
sigma_digit = 0.288675
sigma_taper(p=3) = 0.318022
sigma_crit(p=3) = 0.5052
S_p3(sigma_digit) ~= 0.0803
```

The digit-expansion embedding therefore satisfies the depth-1 nesting taper
and the full PAWOTG series target with headroom.  The open theorem is narrower
than before: prove the actual SSP/Hecke embedding spread is below
`0.318022`, not merely below `0.5052`.

The NS `H^{-1/2}` calculation now records obstruction evidence rather than an
absorption estimate.  The sampled ratio

```text
||P_{>K}(u.grad u)||_{H^-1/2}
/ (nu ||P_{>K}u||_{H^3/2})
```

is above one in all reported rows and diverges as `nu -> 0`:

| nu | Kolmogorov | Smooth | Rough |
| --- | ---: | ---: | ---: |
| `0.10` | `1.38` | `2.30` | `1.67` |
| `0.01` | `3.99` | `7.19` | `7.42` |
| `0.002` | `19.85` | `35.97` | `38.98` |

This supports a Paper 1 obstruction theorem: `Theta_tail` needs the
negative-Sobolev defect ratio bounded, but Kolmogorov scaling drives that
ratio upward in the small-viscosity regime.  It does not prove
`NonCircularKStarDriftBound` or NS regularity.

Checked receipts for this refinement:

```text
DASHI/Physics/Closure/Gate3NestingTaperConditionReceipt.agda
DASHI/Physics/Closure/NSHminus1Over2ObstructionReceipt.agda
DASHI/Physics/Closure/ClayFinalAnalyticFrontierMapReceipt.agda
```

| Lane | New calculation | What advances | Remaining wall |
| --- | --- | --- | --- |
| Gate 3 / PAWOTG | The digit-expansion embedding `phi_digit : Z_p -> [0,1]` has variance `1/12` for every prime, hence `sigma = 1/sqrt(12) ~= 0.2887 < 0.5052`; at BT level `j`, `sigma_j = p^{-j}/sqrt(12)`. | PAWOTG is achievable for a natural adelic-to-Archimedean map, and Kozyrev's `p=2` Haar case is the model instance of this computation. | The SSP/CM/Hecke atom dictionary may not use `phi_digit`; proving the actual SSP embedding has the same uniform spread remains the Gate 3 theorem. |
| YM / beta bridge | The character-expansion transfer-matrix bound gives a positive fixed-lattice mass `m_latt(beta) >= -2 log(I1(beta)/I0(beta))`; at `beta=6`, `m_latt >= 0.183`, and at `beta=12.97`, `m_latt >= 0.080`. | The blocker is reformulated: fixed-lattice positivity is not the issue. | Clay YM requires survival in the continuum limit as `a(beta)->0`, `beta->infinity`; the character bound weakens in that limit, so nonperturbative continuum control is still required. |
| NS / theta | The paraproduct split confirms low-high is controlled by low-frequency gradient/Bernstein terms, while high-high forces the `L3`/`H^{1/2}` route. | The theta criterion is correctly framed as a tail-localized pressure-margin condition. | The stale claim that `H^{11/8}` is weaker than `H^{1/2}` is retracted; spatially it is stronger.  The open step is still non-circular high-high control without importing Serrin/BKM-class regularity. |

Checked receipts for this update:

```text
DASHI/Physics/Closure/Gate3DigitExpansionPAWOTGPartialResultReceipt.agda
DASHI/Physics/Closure/YMCharacterExpansionContinuumReformulationReceipt.agda
DASHI/Physics/Closure/NSThetaPressureMarginCorrectionReceipt.agda
```

## Evidence Bundle And Checked Receipt Links

The current analytic sprint artifacts are staged in:

```text
Docs/Images/clay-analytic-sprint/
```

Use `Docs/Images/clay-analytic-sprint/README.md` as the artifact manifest.  The
bundle contains the supplied CSV and PNG diagnostics:

- `gate3_frame_extended.csv` and `pawotg_sigma_crit*.png`
- `gate3_sampler_quality.csv`
- `gate3_frame_sampler_quality.csv`
- `ym_p7_polymer_kp.csv` and `ym_kp_sum_vs_beta*.png`
- `ym_c0_threshold_sensitivity.csv`
- `ym_beta_threshold_sensitivity_C0.csv`
- `ns_theta_full_sweep.csv` and `ns_theta_profile*.png`
- `ns_theta_tail_restricted.csv`
- `ns_global_vs_tail_theta_summary.csv`
- `computed_margin_summary.txt`
- `ym_monster_re2_C0_thresholds.csv`
- `gate3_monster_re2_sigma_crit.csv`
- `ns_monster_re2_low_shell_vs_tail_summary.csv`
- `monster_re2_recalculation_summary.txt`

These artifacts are linked to the following checked Agda surfaces:

| Lane | Checked surface | Artifact reading |
| --- | --- | --- |
| Universal | `DASHI/Physics/Closure/ScaleGraphBarrierAlgebraProofReceipt.agda` | The abstract algebra closes only after projection, node margin, edge influx, and absorber positivity are supplied. |
| Gate 3 | `DASHI/Physics/Closure/Gate3PAWOTGConcreteConditionReceipt.agda`, `DASHI/Physics/Closure/Gate3DigitExpansionPAWOTGPartialResultReceipt.agda`, and `DASHI/Physics/Closure/Gate3NestingTaperConditionReceipt.agda` | The concrete PAWOTG series target is `sigma < 0.5052` at the binding prime `p=3`.  Kozyrev wavelets are orthogonal in `L2(Q_p)`, so the p-adic Gram is identity.  The finite-frame CSV failure came from Archimedean digit-image nesting, and PAWOTG is the Gaussian taper condition that must damp that nesting leakage. |
| YM | `DASHI/Physics/Closure/YMKPThresholdCorrectionReceipt.agda`, `DASHI/Physics/Closure/YMActualKPLocalSumDiameter1Receipt.agda`, and `DASHI/Physics/Closure/YMActualKPLocalSumDiameter2Receipt.agda` | The supplied KP table records `r(beta=6) = 2.7017782 > 1`; beta 6 diverges.  Beta 10.13 is convergent but not strictly absorbing, and beta 13.64 is strictly absorbing in the supplied table. |
| NS | `DASHI/Physics/Closure/NSTailFluxLPIdentityFullDerivationReceipt.agda`, `DASHI/Physics/Closure/NSAdjacentShellLeakageBoundReceipt.agda`, and `DASHI/Physics/Closure/NSThetaTailToBKMBridgeReceipt.agda` | The supplied theta sweep includes stress/failure regimes with `Theta > 1` and negative margins.  It is a danger-shell locator, not evidence of unconditional theta preservation. |

All rows and plots in this bundle are evidence-only.  They do not inhabit
`PAWOTGUniformSeparation`, `BalabanPhysicalBetaBridge`, or
`NonCircularKStarDriftBound`.

The new cross-lane governance blocker above YM/Gate 3 is
`MonsterMoonshineSSPQuotientControl`.  Its role is quotient/compression
control for the 15SSP/moonshine carrier, not multiplication of contour entropy.
The raw carrier ratio `c2/c1 ~= 109` must not be substituted for the physical
polymer entropy constant `C0`.  If the quotient/compression theorem is actually
proved, the effective YM entropy can remain `C0_eff ~= 1` and the live strict
absorption threshold remains `beta_abs ~= 12.97`; if a square-root leak or raw
leak survives, the thresholds rise to about `22.66` or `32.35`.  This records a
blocker and failure mode only: no quotient theorem, Gate 3 closure, YM mass
gap, or Clay claim follows.
Gate 3 has its own stress branch: if Monster multiplicity leaks into overlap
entropy, the `p=3` sigma threshold tightens from `0.5052` to about `0.296`
under square-root leakage or about `0.228` under raw leakage.  This keeps
`MonsterMoonshineSSPQuotientControl` load-bearing above both YM entropy and
Gate 3 sampler/PAWOTG quality.

The YM lane now has a checked companion receipt,
`DASHI/Physics/Closure/YMC0EntropyThresholdSensitivityReceipt.agda`, for the
latest C0 threshold table and Monster re-2 stress calculation.  It records
`C0 = 0.5, 1, 2, 5` with beta absorption thresholds `10.107`, `12.971`,
`15.836`, and `19.622`, and fixes the Monster values `c1=196884`,
`c2=21493760`, `c2/c1 ~= 109.17`, `sqrt(c2/c1) ~= 10.45`.  It is
non-promoting: raw Monster multiplicity is not physical polymer entropy,
quotient control remains open, and YM/Clay promotion remains false.

The checked positive evidence surface is
`DASHI/Physics/Closure/YMMonsterQuotientEvidenceReceipt.agda`.  It records the
McKay-Thompson `T_7` compression: raw Monster `c2=21493760` versus
`T_7(q^2)=204`, a factor of about `105000`.  The later Rademacher audit
supersedes the old `C0_eff ~= 2` reading: the T7 envelope gives
`C0 ~= 115.543` and `beta* ~= 32.60`, while the later direct `T7A`
generating-sum audit gives the live KP threshold `beta* ~= 16.58` with gap
`10.58` from physical `beta ~= 6`.  The old `C0 = 2` line is heuristic only.
This is quotient/effective-activity evidence only; the Balaban bridge remains
open.

The cross-lane quotient-control receipt is:

```text
DASHI/Physics/Closure/MonsterMoonshineSSPQuotientControlReceipt.agda
```

It records the Monster re-2 stress model across all three Clay-facing lanes:

| Lane | Raw multiplicity stress | Consequence |
| --- | --- | --- |
| YM | `ym_monster_re2_C0_thresholds.csv` treats `log(c2/c1)`, square-root leakage, and raw `c2/c1` as possible `C0` stress values. | `beta_abs` rises from `12.9713` at `C0=1` to `19.36`, about `22.66`, or about `32.35`. |
| Gate 3 | `gate3_monster_re2_sigma_crit.csv` inserts the same multiplier into the PAWOTG overlap count. | Binding `p=3` tightens from `sigma_crit=0.505208` to `0.3375`, about `0.296`, or about `0.228`. |
| NS | `ns_monster_re2_low_shell_vs_tail_summary.csv` leaves the PDE estimate unchanged but reinforces the low-depth/low-shell warning. | Continue using `Theta_tail`, not `Theta_global`, for the Clay tail seam. |

This is now the shared blocker immediately above YM/Gate 3 entropy readings:
prove effective multiplicity control, or all downstream thresholds must be
read in the harsher stressed regime.

The second-pass calculations add three sharper diagnostic targets:

| Lane | Refined diagnostic | Updated target |
| --- | --- | --- |
| NS | `ns_theta_tail_restricted.csv` separates `Theta_global = sup_k theta(k)` from `Theta_tail = sup_{k >= K_diss(nu)} theta(k)`.  The current global maximum is low-shell `k=2`, not a dissipative-tail shell. | Use `Theta_tail`, `danger_shell_tail`, and `low_shell_warning` in Paper 1.  Smooth and Kolmogorov pass the sampled tail barrier; near-critical and rough fail; inviscid has no sampled tail rows because `K_diss` exceeds the CSV range. |
| YM | `ym_c0_threshold_sensitivity.csv` and uploaded `ym_beta_threshold_sensitivity_C0.csv` show `beta_abs(C0) = (a + log(2 p C0)) / c_min`. | Treat entropy constant `C0` as load-bearing.  `C0=0.5` gives `beta_abs=10.1071`, `C0=0.75` gives `11.7825`, `C0=1` gives `12.9713`, and `C0=1.25` raises it to `13.8934`; larger `C0` worsens the Balaban bridge. |
| Gate 3 | `gate3_sampler_quality.csv` shows every un-tapered Archimedean image row has `sampler_quality=FAIL_CLUSTERED`, with `mu_N` near `1` and `(N-1)mu_N >> 1`. | Stop treating this as p-adic atom failure.  Kozyrev wavelets are orthogonal in `L2(Q_p)`; the next theorem target is `Gate3NestingTaperCondition`, proving the Gaussian taper damps parent-child nesting and yields uniform frame control. |

The checked receipt for this refinement is:

```text
DASHI/Physics/Closure/ClayRefinedDiagnosticTargetsReceipt.agda
```

The checked asymmetry ledger for the three final blockers is:

```text
DASHI/Physics/Closure/ClayBlockerAsymmetryReceipt.agda
```

That receipt deliberately prevents the paper stack from flattening the final
blockers into three identical "open lemmas": Gate 3 is new adelic localization
mathematics, YM is a quantified Balaban-program completion, and NS is the
high-high paraproduct obstruction.

The four-visualisation synthesis sharpens the ordering:

- **Gate 3 is the most tractable blocker.**  The visible target is now the
  `p=3` PAWOTG threshold `sigma_crit = 0.5052`, with a concrete
  Weil/Kozyrev attack route: build the explicit adelic atom map, use
  Kozyrev/Haar orthogonality as the p-adic model, and prove uniform
  Archimedean localization below the critical spread.  The finite frame plots
  are obstruction diagnostics until that transfer theorem exists.
- **Yang-Mills is medium tractability.**  The strict carrier-safe beta gap from
  `beta = 6` is `6.97`; with `b0 ~= 0.0465`, a naive perturbative bridge has
  scale factor `exp(6.97 / 0.0465) ~= exp(150)`.  That is evidence against a
  perturbative closure route, not a proof of impossibility for Balaban RG.
- **Navier-Stokes is the hardest lane.**  The visualised failure/stress regimes
  point to the high-high paraproduct as load-bearing.  The non-circular
  estimate may be an obstruction equivalent to regularity, not merely an
  ordinary open lemma awaiting bookkeeping.

## Irreducible Clay Boundary

The current sprint reduced the Clay-facing programme to three measured seam
conditions with explicit constants.  It did not solve any of the three.  Each
remaining inhabitant is a genuinely new analytic theorem, not a missing Agda
wrapper or a documentation task.

The three blockers are also not symmetric:

| Final inhabitant | Blocker type | What the sprint supplied | Why it remains open |
| --- | --- | --- | --- |
| `PAWOTGUniformSeparation` | Most tractable: new adelic localization mathematics with a Weil/Kozyrev attack route. | The BT-overlap threshold is explicit: the binding inert prime is `p=3`, with `sigma_crit = 0.5052`; the finite plots identify where phase-blind/toy frames collapse. | A proof needs a concrete adelic-to-Archimedean atom map whose images have uniformly bounded Gaussian spread as `N -> infinity`.  Kozyrev orthogonality in `L2(Q_p)` does not by itself imply Archimedean localization in `L2(R^3)`. |
| `BalabanPhysicalBetaBridge` | Medium tractability: quantitative completion of the existing Balaban RG programme. | The `p=7` KP threshold is quantified: beta `6` is divergent with `r = 2.7017782`; the strict beta gap is `6.97`, and perturbative iteration would require scale factor `exp(150)`. | A proof needs a nonperturbative Balaban RG bridge from the physical lattice normalization to the KP-safe carrier regime, controlling polymer errors through the flow, summable corrections, and reflection positivity/OS compatibility.  Perturbative beta-function language is not enough, and continuum construction remains separate. |
| `NonCircularKStarDriftBound` | Hardest: obstruction/high-high paraproduct frontier; its non-circular form may be equivalent to the NS regularity problem. | The NS obstruction is localized to the danger shell and the high-high paraproduct/leakage term; the theta sweep is a stress locator, not preservation evidence. | A proof must show `Diss_{>K*}` dominates `Flux_{>K*}` without assuming the regularity it is trying to prove.  The high-high term is the classical 3D NS obstruction, so this is recorded as `OpenWithHighHighParaproductObstruction`, not a neutral `OpenUnknown` lemma. |

The correct publication claim is therefore a reduction theorem programme:

```text
measured seam constants
  + checked fail-closed margin grammar
  + explicit final analytic inhabitants
  -> precise Clay target map
```

not a Clay proof.

The paper boundaries should follow this asymmetry:

- **Paper 1 / NS:** conditional regularity reduction plus danger-shell
  diagnostic; do not claim the non-circular high-high bound.
- **Paper 2 / Gate 3:** finite-frame and PAWOTG reduction with the
  `sigma_crit(p=3) = 0.5052` threshold; do not claim continuum density.
- **Paper 3 / YM:** quantitative KP/Balaban gap reduction; do not claim the
  physical beta bridge or continuum mass gap.
- **Paper 0 / grammar:** should summarize the asymmetric blocker ledger after
  Papers 1-3 are stable, not present the three blockers as equivalent closure
  tasks.

## Three Final Reduction Receipts

The current prize-facing surface is now pinned to three companion receipts:

```text
Gate3AdelicLocalizationReductionReceipt
YMBetaBridgeQuantitativeGapReceipt
NSNonCircularObstructionReceipt
```

They sharpen the final blockers without promoting any of them.

### PAWOTGUniformSeparation

The Gate 3 blocker is no longer a vague density phrase.  The usable reduction
is:

```text
explicit adelic embedding phi
  + uniform Archimedean localization of phi(psi_j)
  + sigma(phi(psi_j)) < 0.5052 at the binding inert prime p=3
  -> inf_N A_N > 0
  -> Mosco/no-pollution route becomes accessible
```

The computable side condition is the BT overlap series:

```text
sum_{d>=1} p^d exp(- (log p)^2 d^2 / (4 sigma^2)) < 1
```

The Weil/Kozyrev route is the preferred attack path: make the adelic atom map
explicit, use Kozyrev/Haar orthogonality as the p-adic localization model, and
then prove uniform Archimedean Gaussian spread below the `p=3` threshold.  The
Kozyrev/Haar result at `p=2` is the model case, not the SSP theorem.  The SSP
inert block requires a uniform adelic-to-Archimedean localization theorem; that
is exactly `PAWOTGUniformSeparation`.

### PhysicalBetaBridge

The YM blocker is not threshold arithmetic alone.  The reduction now records:

```text
beta_phys ~= 6
beta_convergence ~= 10.11
beta_strict ~= 12.97
gap_to_convergence ~= 4.11
gap_to_strict ~= 6.97
```

With a one-loop coefficient `b0 ~= 0.0465`, a naive perturbative bridge across
the strict gap has scale factor:

```text
exp(6.97 / 0.0465) ~= exp(150) ~= 10^65
```

That number is not proposed as a proof.  It is the diagnostic showing why the
physical beta bridge must be nonperturbative: a Balaban/strong-coupling or
block-spin theorem has to cross the beta window; iterating perturbation theory
does not close the Clay gap.

### NonCircularKStarDriftBound

The NS blocker is now stated as an obstruction record.  The high-high
paraproduct term is where a circular proof would accidentally import Serrin,
BKM, or `H^{1/2}` velocity control:

```text
Flux_{>K*} <= (1-c) Diss_{>K*}
```

must be proved without assuming the regularity criterion it is meant to
produce.  The admissible replacement target is the negative-Sobolev defect
estimate:

```text
||P_{>K*}(u.grad u)||_{H^{-1/2}}
  <= epsilon * nu * ||P_{>K*}u||_{H^{3/2}}
```

paired against `P_{>K*}u` in `H^{1/2}`.  The publishable contribution is
therefore:

```text
Theta < 1 is a new seam/regularity criterion and danger-shell locator.
Theta preservation is equivalent to controlling the high-high obstruction.
The non-circular high-high estimate is the Clay-level step.
```

The repo should not treat `Theta < 1` as equivalent to BKM, and should not
claim that the high-high term is handled until `NonCircularKStarDriftBound` is
inhabited.
`DASHI/Physics/Closure/NSNonCircularKStarDriftBoundTargetReceipt.agda` now
records that inhabitant target exactly: prove the danger-shell strict
absorption inequality, or equivalent theta preservation, without importing
`H^{1/2}` velocity regularity, Serrin, BKM, or stronger regularity.
`DASHI/Physics/Closure/NSNegativeSobolevDangerShellReceipt.agda` records the
sharpened H^{-1/2} nonlinear-defect theorem target.  The target receipt records
low-high as non-core, high-high as load-bearing, and keeps the defect estimate,
drift containment, edge influx, theta preservation, and tail-to-continuation
discharge open.

## Current Priority Order

The post-Hecke/CM correction changes the dependency order.  The useful
publication/runtime sprint can still run YM enumerators in parallel, but the
Clay-solving dependency order is now:

1. **Gate 3 continuum transfer.**  This is the shared bottleneck.  Carrier YM
   area laws, finite atom frames, and EV5/NS carrier diagnostics do not become
   continuum theorems without density, Mosco recovery, no spectral pollution,
   and mass-shell transfer.
2. **Yang-Mills actual rho / KP / Balaban.**  Once Gate 3 has a viable
   transfer route, the YM lane needs actual same-prime `p=7` Wilson polymer
   activity, strict KP absorption, and Balaban RG contraction.
3. **Navier-Stokes danger-shell maximum principle.**  The NS theta grammar is
   sharp, but preserving `theta < 1` under actual flow is the hard regularity
   estimate.
4. **Paper 0 publication.**  Publish the shared margin grammar and fail-closed
   term index now, while the Clay lanes continue as target papers.

This order separates dependency priority from implementation convenience.  YM
has concrete finite computations available today, but Gate 3 is the bridge
that prevents every carrier-scale success from being overclaimed.

## Current Position After The Hecke/CM Correction

The repo now has a clean vocabulary fence:

```text
CM arithmetic over Q(sqrt(-7)):
  5 split + 9 inert + 1 ramified

DASHI / Hecke atom grammar:
  MirrorA7 + MirrorB7 + Sign1
```

Checked surfaces:

- `HeckeCarrierVsCMSplittingReceipt`: CM `5+9+1` and Hecke `7+7+1` are
  distinct partitions; `notSamePartitionFlag = true`.
- `P71HeckeMirrorSignLaneReceipt`: `p71` is split in the CM table and is only
  the terminal SSP sign/carry/reaction-orientation lane in the Hecke grammar.
- `KeyTermCorrespondenceIndexReceipt`: public terminology rejects reading
  `7+7+1` as the CM split and rejects `p71` as inert/time theorem.
- `Paper0SharedMarginGrammarConsolidationReceipt`: Paper 0 consumes those
  correction receipts while keeping all Clay promotion flags false.

So the current gap is not vocabulary.  The remaining gap is analytic:
projection fidelity, edge accounting, and absorber dominance at danger nodes.

## Yang-Mills Lemma Chain

The preferred YM prize route is:

```text
actual p=7 Wilson polymer activity
  -> same-prime KP absorption
  -> carrier area law
  -> Balaban RG contraction to the physical scale
  -> continuum OS/Schwinger construction
  -> Gate 3 mass-shell transfer
  -> positive continuum YM mass gap
```

| Lemma | Required content | Current repo state | Clay consequence |
|---|---|---|---|
| `YMActualP7WilsonPolymerActivity` | Define actual edge-rooted same-prime polymer activity from the carrier Wilson action, not toy rho. | Targeted by `YMActualPolymerActivityDefinitionReceipt`; not inhabited as analytic activity. | Without this, KP ratios are diagnostic grammar only. |
| `YMSamePrimeKPAbsorption` | Prove the local KP sum is strictly below `1` from contour/action suppression, entropy constant `C0`, and an all-diameter geometric bound. | Same-prime overlap reduction, BT path counting, convergence threshold, and absorption threshold are recorded; contour/action suppression and the all-diameter bound remain open. | Gives a real carrier strong-control margin. |
| `YMCarrierAreaLaw` | Convert strict KP absorption into `|<W(C)>| <= exp(-sigma Area(C))` with `sigma > 0`. | Carrier area-law target exists in Paper 3 docs; no continuum promotion. | Gives carrier confinement only. |
| `YMBalabanRGContraction` | Prove a nonperturbative recurrence `rho_{k+1} <= q rho_k + delta_k`, `q < 1`, `sum delta_k < infinity`, across scales. | `YMBalabanRGScaleTransferFrontierReceipt` records this as hard open. | This is the main YM Clay blocker after actual activity. |
| `YMContinuumOSConstruction` | Construct a continuum gauge-invariant Schwinger/Wightman object with OS positivity and infinite-volume/cutoff control. | Older YM roadmaps name this as an external continuum obligation. | Required for Clay existence. |
| `YMGate3MassShellBridge` | Transfer carrier area law/spectral control to the physical continuum mass shell without spectral pollution. | Gate 3 density/Mosco/no-pollution/mass-shell surfaces are conditional/open. | Required for Clay mass gap. |

The live YM lane priority is therefore:

```text
actual activity first, Balaban recurrence second, Gate 3 mass-shell third.
```

Current analytic constants for this lane:

- Use `c_min = 0.242` for the live same-prime `p=7` threshold bookkeeping.
- KP convergence requires `beta > 10.11`; strict activity absorption requires
  `beta > 12.97`.
- The `beta6` perturbative lane is divergent with ratio `r = 2.70`; it does not
  close either gate.  Relative to `beta6 = 6`, the remaining gaps are `4.11`
  for convergence and `6.97` for strict absorption.
- The supplied `ym_p7_polymer_kp.csv` also includes the older `13.64` sample:
  in that table beta `12.97` is effectively at the strict-boundary
  (`KP_inf ~= 1.0006`) while beta `13.64` is safely strict
  (`KP_inf ~= 0.7400`).  Use `12.97` as the live computed boundary and
  `13.64` as a conservative sampled safe point, not as a separate theorem.

The proof target is not a bare threshold comparison.  The KP estimate must bind
polymer contour entropy by a constant `C0`, suppress each contour by the actual
Wilson action, and sum all diameters with a geometric bound.  The final YM
blocker is `BalabanPhysicalBetaBridge`: the physical running must enter the
carrier-safe KP/Balaban regime without replacing the action estimate by a toy
rho or a perturbative beta slogan.

This is an open nonperturbative RG theorem.  The repo can record the beta gap
and the recurrence shape, but it does not construct the Balaban bridge from
the physical regime.  Until that bridge is inhabited, carrier KP thresholds do
not imply continuum Yang-Mills mass gap.

## Navier-Stokes Lemma Chain

The NS route is:

```text
fixed-K LP identity
  -> theta < 1 implies fixed-K tail decay
  -> danger-shell edge conservation
  -> danger-shell maximum principle
  -> tail control to BKM/Serrin continuation
  -> global smoothness
```

| Lemma | Required content | Current repo state | Clay consequence |
|---|---|---|---|
| `NSTailFluxLPIdentity` | Prove the fixed-`K` Littlewood-Paley tail identity with signs, pressure cancellation, dissipation, and nonlinear flux terms. | `NSTailFluxLPIdentityAnalyticReceipt` records the analytic surface; commutator bound remains an obligation. | Locks the actual-flow quantity theta measures. |
| `NSThetaImpliesTailDecay` | From `theta(K,t) < 1` and positive dissipation, prove fixed-`K` tail energy decreases. | Implemented as a conditional receipt. | Gives conditional absorption, not preservation. |
| `NSDangerShellEdgeConservation` | Prove incoming adjacent-shell flux into the danger shell is controlled and cannot appear as hidden production. | Named by the danger-shell and edge-conservation receipts; open. | Prevents the worst shell from being fed from outside the margin model. |
| `NSDangerShellMaximumPrinciple` | Prove the worst theta value cannot cross `1` if it starts below `1`. | `NSDangerShellMaximumPrincipleReceipt` states the target; not proved. | This is the hard NS regularity estimate. |
| `NSTailControlToBKM` | Convert preserved theta, non-circular `K*` drift control, and enough tail/Sobolev control into the BKM or Serrin continuation hypotheses. | Recorded as one-way target only. | Gives global continuation if all previous estimates hold. |
| `NSGlobalRegularity` | Remove conditional assumptions for all smooth divergence-free data. | Open. | Clay NS closure. |

The live NS priority is therefore:

```text
fixed-K identity and commutator bound first, danger-shell maximum principle second.
```

The NS fixed-`K` route also needs a non-circular `K*` drift condition: prove that
the actual danger shell does not drift beyond the viscous cutoff, i.e. a bound of
the form `K*(t) <= K*(nu)`, before consuming fixed-`K` tail decay as BKM/Serrin
control.  The danger shell cannot be redefined by the moving cutoff and then used
as the proof of its own containment.

In particular, `theta < 1` alone does not imply BKM.  It must be accompanied by
`NonCircularKStarDriftBound` plus enough tail/Sobolev control to reach a standard
continuation criterion.

The supplied `ns_theta_full_sweep.csv` is not a pass certificate.  Its trace
summaries include `Theta > 1` and negative margins in the sampled regimes, so
the correct reading is: the diagnostic locates barrier failure/stress cases and
therefore sharpens the need for edge-influx control and non-circular `K*` drift.

The analytic obstruction is the high-high paraproduct term.  Low-high flux can
be organized by Bernstein-type estimates, but high-high flux is where a priori
3D regularity is hidden.  Any proof of `NonCircularKStarDriftBound` must control
that term through the H^{-1/2} nonlinear-defect estimate, without importing
`H^{1/2}` velocity regularity or stronger regularity as an assumption.

## Gate 3 Lemma Chain

Gate 3 is the transfer route from carrier control to continuum control.  It is
where most overclaims would otherwise enter.

```text
phase-complete finite cutoff frame
  -> uniform lower frame control
  -> PAWOTG / adelic Sobolev density
  -> Mosco recovery
  -> no spectral pollution
  -> mass-shell bridge
```

| Lemma | Required content | Current repo state | Clay consequence |
|---|---|---|---|
| `PhaseCompleteFrameLowerBound` | Prove `A_N > 0` on each finite cutoff subspace with phase/twist included, using finite separation and a Gershgorin-style lower bound. | Upper bound and conditional lower-bound surface recorded; finite separation/Gershgorin discharge remains open. | Finite evidence only. |
| `UniformFrameLowerBound` | Prove the relevant lower control does not collapse as `N -> infinity`; equivalently, prove PAWOTG uniform separation. | Open. | Needed before carrier estimates can survive refinement. |
| `PAWOTGUniformSeparation` | Prove phase-aware carrier/PAWOTG separation uniformly across refinement, giving the density/Mosco input rather than only finite `A_N`. | Named by the Gate 3 PAWOTG roadmap and Mosco receipt; open. | Blocks continuum transfer. |
| `MoscoRecovery` | Prove strong recovery plus weak-limit compatibility for cutoff subspaces. | Condition II is recorded as trivial on the abstract surface; condition I is blocked by density. | Needed for operator convergence. |
| `NoSpectralPollution` | Prove limiting spectra do not gain ghost eigenvalues from phase loss or cutoff artifacts. | Conditional on phase/twist completeness plus Mosco. | Required for physical gap transfer. |
| `MassShellBridge` | Identify the limiting carrier operator spectrum with the physical gauge-invariant mass shell. | Open. | Required for YM Clay promotion. |

The live Gate 3 lane priority is therefore:

```text
phase-complete finite lower bound, then PAWOTG density, then no-pollution.
```

The finite `A_N` step is a finite separation problem: prove the relevant
Gram-matrix rows stay separated enough for a Gershgorin lower bound.  The
continuum step is stronger: prove `PAWOTGUniformSeparation`, a uniform version of
that separation across refinement.  The PAWOTG density/Mosco route also has the
series-side condition `sigma < 0.505`.  These are documented analytic conditions
only; they are not yet a density theorem, Mosco recovery proof, or continuum
transfer.

The supplied `gate3_frame_extended.csv` should be cited as a finite-diagnostic
obstruction: the sampled Gershgorin lower bound is negative in every row, and
toy-frame `A_N` collapses toward numerical zero at larger cutoffs.  This does
not contradict the conditional Agda theorem: it shows that the sampled
dictionaries did not satisfy the required finite separation hypothesis.

The missing theorem is not finite linear independence alone.  It is uniform
Archimedean localization of the PAWOTG/atom images under refinement.  Without
an explicit transfer map and a proof of uniform spread `sigma < 0.5052`, finite
Kozyrev or toy-frame evidence does not become a continuum density/Mosco theorem.

The checked pin for this exact next theorem obligation is
`DASHI/Physics/Closure/Gate3PAWOTGUniformSeparationTargetReceipt.agda`.  It
records the implication from explicit adelic embedding plus uniform Gaussian
spread below the `p=3` threshold to `inf_N A_N > 0`, and keeps the Mosco,
no-spectral-pollution, mass-shell, Gate 3, and Clay steps conditional/open.

## Shared Finish Theorem

All three lanes are instances of the same target:

```text
faithful projection to a scale graph
  + strict node margin dynamics
  + conservative or absorbable edge transfer
  + absorber dominance at danger nodes
  + initial worst ratio < 1
  -> worst ratio never crosses 1
```

Existing citation surfaces:

- `StrictMarginImpliesAbsorptionReceipt`: proved domain-free grammar.
- `DangerScaleEdgeConservationReceipt`: edge-accounting hypothesis.
- `ScaleGraphBarrierTargetReceipt`: worst-scale comparison-principle target.
- `UniversalScaleGraphBarrierTargetReceipt`: joined NS/YM/Gate 3 theorem
  shape.

The abstract scale-graph barrier algebra is provable as domain-free margin
bookkeeping: if projection, node margin, edge-influx, and absorber-dominance
hypotheses are supplied, the worst ratio cannot cross the barrier.  What remains
open is not the algebraic implication but the lane-specific analytic hypotheses:
Gate 3 projection/separation, YM contour/action KP control plus Balaban transfer,
and NS non-circular `K*` drift plus enough tail/Sobolev control.

The most important common lemma is:

```text
DangerNodeEdgeInfluxBound:
  incomingEdge(v,t) <= epsilon * absorption(v,t)
  with theta(v,t) + epsilon < 1
```

Once this exists in each lane, the strict-margin grammar can fire as a real
barrier:

```text
R'_v <= P_v + incoming_v - A_v
P_v <= theta A_v
incoming_v <= epsilon A_v
theta + epsilon < 1
--------------------------------
R'_v <= -(1 - theta - epsilon) A_v
```

Domain readings:

- NS: incoming edge is adjacent-shell leakage into the danger shell.
- YM: incoming edge is block-spin / polymer-overlap leakage under RG.
- Gate 3: incoming edge is refinement / projection defect across cutoffs.

## Immediate Sprint

1. Prove finite Gate 3 separation and the Gershgorin lower bound needed for
   `A_N > 0`.
2. Lift finite cutoff frame evidence to `PAWOTGUniformSeparation`, or identify
   the obstruction.
3. Prove PAWOTG / adelic-to-Archimedean density, then Mosco recovery and no
   spectral pollution; the PAWOTG series side must satisfy `sigma < 0.505`.
4. In parallel, implement actual `p=7` Wilson polymer activity from the
   carrier action and reject every toy-rho input at the KP boundary.  Use
   `c_min = 0.242`, thresholds `10.11`/`12.97`, and keep the `beta6` gaps
   `4.11`/`6.97` explicit.
5. Prove the YM contour/action suppression estimate with entropy `C0`, the
   all-diameter geometric bound, and then `BalabanPhysicalBetaBridge`.
6. Prove the NS fixed-`K` LP identity and isolate the commutator/edge-leakage
   term that must be dominated at the danger shell, including the non-circular
   `K*(t) <= K*(nu)` drift condition and enough tail/Sobolev control for BKM.

Final blockers:

- `PAWOTGUniformSeparation`
- `BalabanPhysicalBetaBridge`
- `NonCircularKStarDriftBound`

## Non-Promotion Boundary

The Clay prize is not reached by naming the shared grammar, observing theta,
recording a carrier gap, or proving a finite frame bound.  The prize requires:

- for YM: continuum Yang-Mills existence plus a positive physical mass gap;
- for NS: unconditional global smooth continuation for the required data
  class;
- for Gate 3: a valid bridge from carrier estimates to the continuum operator
  and mass shell.

Until the listed lemmas are inhabited, all Clay promotion flags remain false.
