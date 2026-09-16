# YM PR #944 BIDI Audit — R345 through R386

Status: archaeology / bookkeeping reference. **Not theorem authority.**

Parent survey: `YMRHPRRoundArchaeologyAudit.md`  
Live scheduler: `YMRHGlobalGoalParetoBoard.md`  
PR: #944 — `YM: carry literal CMP116 marked amplitude directly into canonical B`

This appendix records the dense internal-round chronology on #944 so future investigation does not reconstruct it from 100+ commits and PR comments.

## 1. Fixed terminal consumer

```text
quantitative connected-correlation decay
  on the SAME reconstructed continuum family
-> clustering-to-spectral-gap compiler
-> SameHamiltonianPhysicalMassGap.
```

CMP116/Row-C/Heat-Doob/polymer/coefficient routes are producer families beneath that consumer.

## 2. Round map

| Internal round | Main role | Current status |
|---|---|---|
| R345 | amplitude-parametric subgap upper | donor / compiler |
| R346 | shared marked amplitude direct carrier | active terminal-facing donor; literal selected localization + D_time remain physical |
| R347–R348 | selected coefficient / mixed-log attachment split | `C_attach` remains application debt; stale missing R347 import repaired to canonical R346 levels |
| R349 | selected distance carrier weld | stronger distance route donor |
| R350 | split selected Hessian comparison into `H_stab` + `H_sub` | structural cut retained; stale R347 import now also repaired to R346 |
| R351 | source substitution displacement + selected attachment | historical-mark route |
| R352 | source local Hessian stability + selected attachment | historical route |
| R353–R363 | marked-walk/H_scale/collar/charging route | optional producer |
| R364 | direct analytic-path/Hessian route | superseded as mandatory by Cauchy recut |
| R365–R369 | perturbative fixed-point/map-defect route | optional producer |
| R368 | direct CMP116 fixed-parameter contraction | source donor |
| R370 | direct Cauchy/mean-value parametric fixed-point sensitivity | compatibility donor |
| R371 | published CMP116 parametric fixed-point source ABI | active source parent |
| R372 | direct local-Hessian Cauchy sensitivity | active generic compiler |
| R373 | joint selected Hessian scalar attachment | compatibility carrier |
| R374 | one canonical CMP116 radius for first + second derivative consumers | duplicate radius debt removed |
| R375 | direct Hessian sensitivity -> existing coefficient Cauchy lift | H_scale no longer mandatory |
| R376 | R351 historical H_sub splice into R375 | compatibility compiler |
| R377 | one canonical selected substitution-distance coordinate | duplicate R351/R373 equality removed |
| R378 | R370 parametric displacement -> R351 source ABI via historical-mark calibration | valid optional compatibility route |
| R379 | audit R375 consumer: semantic `markedInput` -> arbitrary proof-bearing `distanceUpper` | consumer recut |
| R380 | first R370 distance-upper composition into R379 | compatibility route |
| R381 | choose one R370/R373 boundary carrier; selected-distance map/equality become `refl` | representation debt removed |
| R382 | Hessian Cauchy parameter metric = exact R370 fixed-point output metric | representation debt removed |
| R383 | specialize generic Hessian family to literal R103 marked Hessian | compatibility specialization |
| **R384** | minimal fixed-point distance producer with NO legacy `boundaryHessianStable` socket | **acyclic producer recut** |
| **R385** | R384 distance + literal R103 Hessian meet directly at R379 | **preferred local comparison producer** |
| **R386** | coefficient comparison != absolute selected localization | **terminal firewall / route demotion** |

## 3. Historical direct BIDI spine through R380

```text
CMP116 published analytic fixed-point family (R371)
  -> direct parametric sensitivity (R370)
  -> d_boundary^R370 <= U_par
     U_par := L_par(M,r) * d_parameter
  -> R380
  -> R379
  -> R375 coefficient comparison.
```

The R351–R378 historical-mark branch remains useful only when a downstream theorem actually observes the historical marked coordinate.

## 4. R381 — one selected boundary object

`BalabanCMP116CanonicalR370R373BoundaryRound381Exact.agda` chooses R373's boundary carrier to be the R370 boundary carrier and defines

```text
R373.selectedBoundarySubstitutionDistance
  := R370.boundarySubstitutionDistance.
```

The R380 boundary map and selected-distance equality are therefore `refl`.

WrongType correction discovered during implementation:

```text
fixed-point parametric Lipschitz
!=
Hessian-family Lipschitz.
```

R373's selected Lipschitz is the R372 Hessian Lipschitz. No equality between the two constants is required.

## 5. R382/R383 — useful compatibility reductions

R382 measures Hessian Cauchy sensitivity in the exact R370 fixed-point-output metric, removing a second R372↔R370 distance weld.

R383 fixes the Hessian family to the already-owned R103 literal

```text
cmp116PhysicalMarkedHessian
```

and chooses the R373 boundary norm as the difference scalar by construction.

These are useful compatibility presentations, but the downstream audit found a more important dependency problem: full R370 still contains historical `boundaryHessianStable` because it compiles all the way back to R364. Requiring full R370 before the new Hessian producer can therefore reintroduce the old Hessian theorem as a prerequisite.

## 6. R384 — remove the hidden H_local cycle

`BalabanCMP116MinimalFixedPointDistanceRound384Exact.agda` splits out the least-privilege fixed-point-distance producer.

It keeps only what is observed by

```text
d_boundary <= U_par.
```

It deliberately drops:

- `boundaryHessianStable`;
- left/right physical Hessian domains;
- physical field variations.

A source-native R371 application now compiles directly into this minimal distance object without paying H_local first.

So:

```text
published CMP116 fixed-point family
-> selected fixed-point distance upper
```

is now acyclic.

## 7. R385 — two minimal producers meet only at the metric

`BalabanCMP116MinimalDistanceLiteralHessianRound385Exact.agda` composes:

```text
R384 minimal fixed-point distance producer
+
R103 literal CMP116 marked-Hessian Cauchy producer
----------------------------------------------
R379 coefficient comparison.
```

The Hessian Cauchy parameter metric is definitionally the fixed-point output metric. The selected distance is the R384 boundary distance.

The route no longer needs as mandatory prerequisites:

- a full R370 record;
- R380–R383 compatibility chain;
- historical marked input;
- equality of fixed-point and Hessian Lipschitz constants.

The surviving local same-object theorem is

```text
R373 boundary norm
  = target-space distance between the two literal R103 Hessian values.
```

## 8. R386 — comparison is not absolute localization

The coefficient lane is now small enough that its exact scope is visible.

R385 proves a **difference/comparison** bound. The actual R346/R338/R341 terminal-facing source consumer is an **absolute selected mixed-log / connected-response localization** theorem.

`BalabanCMP116ComparisonVsAbsoluteLocalizationRound386Exact.agda` includes a finite exact counterexample to the generic promotion

```text
endpoint difference bounded
=>
absolute endpoint bounded.
```

Equal nonzero endpoints have zero difference, so an absolute reference/anchor or an already-absolute source localization theorem is an independent coordinate.

Therefore:

```text
R385 comparison != R346 literal absolute localization.
```

R385 is an optional subproducer for B1, not a canonical B prerequisite.

## 9. Source blocker repairs

Two files imported the absent module

```text
BalabanCMP116SelectedMarkedBoundaryFrontierRound347Exact
```

only for status coordinates already owned by R346.

- R348 was repaired earlier to import R346 directly.
- R350 is now repaired the same way.

No replacement R347 facade was introduced.

## 10. Canonical B-facing cut after R386

```text
B1 literal selected differentiated CMP116 localization
   |D²_{J_L,J_R} log Z| <= selected rooted/source envelope
   on the SAME active density, J pair, root and physical distance;

B2 selected physical support distance = Euclidean spectral time;

B3 selected-test/Wilson-cylinder same-carrier admissibility where needed;

B4 same-family finite -> continuum connected-covariance transport;

B5 existing clustering -> positive transfer-gap compiler.
```

R309/R338/R341 already show that most transport around B1 is compiler-owned. The actual source/application payment is the selected same-object localization / applicability theorem.

## 11. Optional R385 coefficient producer for B1

If the coefficient route is used to manufacture B1, its remaining non-dominated coordinates are:

```text
P1 published fixed-point family/domain attachment;
P2 selected parameter-distance calibration;
P3 literal R103 Hessian analyticity/magnitude/radius/common-neighbourhood;
P4 R373 boundary norm = literal Hessian target distance;
P5 R348 coefficient/mixed-log same-object attachment;
P6 absolute anchor/reference OR the direct absolute source-localization theorem.
```

P6 is not derivable from R385 comparison alone.

## 12. Aristotle bundle donor audit

The supplied `ym-clay-final-output-20260916` bundle is useful as a theorem/producer donor but is not Agda authority.

Its Lean files show substantial downstream closure once source-shaped inputs are present:

- `CMP116ActivityRate.lean`: source volume/tree rate -> block-unit rate; exact block-size cancellation; explicit entropy margin;
- `MarkedPolymerDecay.lean`: fixed-order source derivatives cost a polynomial in polymer size, absorbed by an arbitrarily small decay-rate loss;
- `RowBShellEnergy.lean`: exponential activity + entropy -> geometric shell energy;
- `PolymerActivityDecay.lean`: Mayer/product smallness -> explicit activity rate;
- `WeightedInfluenceRows.lean`: one weighted row -> all iterates/quasi-locality;
- `RowBToRowCTemporalFusion.lean`: Row-B marked shell + covariance response -> much of Row-C temporal accumulated-curvature debt.

But the bundle remains fail-closed at the same physical source step: the literal differentiated CMP116 activity/source majorant (`hact`) and same-object source identification remain inputs. Thus it compresses producer plumbing but does not pay B1.

## 13. Primary source evidence

Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions*, Commun. Math. Phys. 116 (1988), DOI `10.1007/BF01239022`.

Retained source extract:

`Docs/support/reference/balaban-source-extracts/cmp116-effective-actions-part-ii.txt`

Relevant Sect. 1 landmarks include decoupling parameters, fixed-point equations, small-ball preservation/contraction, analytic dependence, substituted background, uniform bounds, derivative localization and Cauchy representations.

This supports the source theorem shapes. Citation/source text alone does not identify the selected DASHI family, selected physical distance, root or response.

## 14. Current first live physical theorem

After the current compiler/representation reductions, the first B-facing physical theorem remains:

```text
|D²_{J_L,J_R} log Z|
  <= selected rooted/source exponential envelope
```

on the same selected physical T5 carrier.

The attachment's activity-rate route is a plausible producer tactic for this theorem, but its literal CMP116 activity-majorant identification remains open.

## 15. Selected source receipts

```text
R375 RED:       1518978e...
R375 BIDI:      0e0e78f9...
R376 RED:       123882fd...
R376 splice:    38407483...
R375 literal Hessian family repair:
                 daedbcf53509423b7528a4f84d9fdf91caee5b0c
R377 corrected head:
                 f328de90539921b548a8477c7a0db28ddfd4550f
R378 RED:       19c862a371aa495952ac8d9d22317b30ecaba047
R378 GREEN:     c51dc43798161ee018844bffe75120489624f779
R379 source:    c0cf2fe1b2e1a47729d330870ef3875307e27e47
R380 repair:    e8c7ff0fce6a30bc9fa62d27ff95371c97cc5c10
R348 stale-import repair:
                 4f8fc45c0c7b08a5eafcd50fb5ed1e34f220d14a
R381 corrected: aff90bccb33d27ac1a4e9e3115e9837896180670
R382 source:    2f506e23b3a01397e914523a8ca8c96be9ea6e3f
R383 source:    845b1e617761511ad02dd992403db3321572f3de
R384 source:    ddb3e511e63c25265b018d4e14c86994a8a04876
R385 source:    2a8efafe024c836d63cbbab95aee67843008f801
R386 source:    20918c606eefaa300ef73f076e946d8a3b93af87
R350 stale-import repair:
                 20d4354d9dd031ce38e21ac93f1a1104b502c150
```

## 16. Verification boundary

R381–R386 are source-written reductions. `machineChecked` fields are repository classification values, not a fresh exact-head Agda receipt. The stale-import repairs remove known source blockers but do not constitute a kernel run. No continuum YM construction, mass gap, Clay completion or external acceptance is claimed here.
