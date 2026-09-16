# YM PR #944 BIDI Audit — R345 through R380

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

CMP116/Row-C/Heat-Doob/polymer routes are producer families beneath that consumer.

## 2. Round map

| Internal round | Main role | Current status |
|---|---|---|
| R345 | amplitude-parametric subgap upper | donor / compiler |
| R346 | shared marked amplitude direct carrier | active downstream donor; literal selected localization + D_time remain physical |
| R347–R348 | selected coefficient / mixed-log attachment split | `C_attach` remains application debt; stale missing R347 import repaired to canonical R346 levels |
| R349 | selected distance carrier weld | stronger distance route donor |
| R350 | split selected Hessian comparison into `H_stab` + `H_sub` | structural cut retained |
| R351 | source substitution displacement + selected attachment | historical-mark route; reduced by R378, optional for coefficient consumer after R379/R380 |
| R352 | source local Hessian stability + selected attachment | selected attachment remains |
| R353–R363 | marked-walk/H_scale/collar/charging route | optional producer |
| R364 | direct analytic-path/Hessian route | superseded as mandatory by R372 |
| R365–R369 | perturbative fixed-point/map-defect route | optional producer |
| R368 | direct CMP116 fixed-parameter contraction | source donor |
| R370 | direct Cauchy/mean-value parametric fixed-point sensitivity | active donor |
| R371 | published CMP116 parametric fixed-point source ABI | active source parent |
| R372 | direct local-Hessian sensitivity using same parametric ABI | active donor |
| R373 | joint parametric / selected Hessian scalar attachment | active carrier |
| R374 | one canonical CMP116 radius for first + second derivative consumers | duplicate radius debt removed |
| R375 | direct Hessian sensitivity -> existing coefficient Cauchy lift | H_scale no longer mandatory |
| R376 | R351 historical H_sub splice into R375 | compatibility compiler |
| R377 | one canonical selected substitution-distance coordinate | duplicate R351/R373 equality removed |
| R378 | R370 parametric displacement -> R351 source ABI via one historical-mark calibration | valid compatibility route |
| **R379** | audit R375 consumer: replace semantic `markedInput` by arbitrary proof-bearing `distanceUpper` | **consumer recut** |
| **R380** | instantiate R379 directly with R370's `U_par` | **current preferred coefficient route** |

## 3. Current preferred BIDI spine

```text
CMP116 published analytic fixed-point family (R371)
  -> direct parametric sensitivity (R370)
  -> d_boundary^R370 <= U_par
     U_par := L_par(M,r) * d_parameter

same-object attachment:
  d_selected^R373(s) = d_boundary^R370(iota s)

  -> R380
  -> R379 least-privilege distance upper
  -> R375 coefficient/Hessian payment.
```

Local-Hessian side:

```text
same CMP116 differentiated analytic family
  -> R372 local Hessian sensitivity
  -> R373 same selected scalar carrier
  -> R375 coefficient lift.
```

Historical-mark compatibility branch:

```text
U_par <= M_marked^src
  -> R378 constructs R351 source object
  -> R377 canonical selected distance
  -> R376
  -> R375.
```

This branch remains useful when a downstream theorem actually observes the historical marked coordinate. It is not mandatory for R375's coefficient consumer.

## 4. What R378--R380 removed

Before R378, R351 exposed as primitive:

```text
d_sub^src(s) <= M_marked^src.
```

R378 factors this through existing R370:

```text
d_sub(s)
  <= U_par
  <= M_marked.
```

R379 then audits R375 itself and finds that its theorem only consumes a nonnegative scalar upper `U`, not the semantic identity of that upper as the historical mark.

R380 therefore selects

```text
U := U_par
```

directly. The remaining preferred-route weld is only the R373<->R370 selected-boundary same-object map.

Hence:

```text
historical marked calibration = valid producer
historical marked calibration != mandatory coefficient-consumer prerequisite.
```

## 5. R348 source repair discovered by the downstream audit

`BalabanCMP116SelectedCoefficientAttachmentRound348Exact.agda` imported a stale/non-existent module:

```text
BalabanCMP116SelectedMarkedBoundaryFrontierRound347Exact
```

No such file exists on the branch or master. The only two values R348 wanted from it were proof-status projections already owned by R346:

```text
round346LiteralSelectedLocalizationLevel
round346SelectedPhysicalDistanceMeaningLevel.
```

R348 now imports R346 directly. This repairs a concrete exact-head source dependency without creating a replacement R347 facade.

## 6. Primary source evidence

Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions*, Commun. Math. Phys. 116 (1988), DOI `10.1007/BF01239022`.

Retained source extract:

`Docs/support/reference/balaban-source-extracts/cmp116-effective-actions-part-ii.txt`

Relevant Sect. 1 landmarks:

- decoupling parameters `s(Delta)` / `s(Y0)`;
- fixed-point equations for `D` and `A0`;
- small-ball preservation and contraction around (1.13);
- analytic fixed-point dependence on `A'` and `s(Y0)`;
- substituted background `H_k(s(Y0),B')` at (1.17);
- uniform source bound at (1.18) and (1.21);
- localization via derivatives in the decoupling parameters;
- Cauchy representation of differentiated local activities.

This supports the R370/R371 theorem shape. It does **not** by citation alone identify the selected DASHI family, metric, boundary map, parameter distance or historical marked coordinate.

## 7. Current non-dominated search targets

1. selected/published CMP116 fixed-point family same-object attachment;
2. common source neighbourhood membership for the selected parameters;
3. canonical source radius/magnitude interpretation on that family;
4. selected parameter-distance calibration;
5. **R373 selected substitution-distance coordinate = R370 boundary fixed-point distance on the same selected physical object**;
6. R372/R373 selected local-Hessian same-object attachment;
7. R348 `C_attach`;
8. R346 literal selected differentiated-localization theorem;
9. R346 `D_time` selected physical distance = Euclidean spectral time;
10. same-family finite-to-continuum covariance transport.

Optional only when a historical mark is semantically consumed:

```text
U_par <= M_marked^src.
```

## 8. Dominated routes retained for archaeology

- R351–R378 historical-mark route for consumers that do not observe mark semantics;
- R353–R363 marked-walk/H_scale programme;
- R364 higher-derivative analytic-path presentation;
- R365–R369 contraction/cross-map-defect route;
- CMP102-Lipschitz/cross-propagator route.

These remain valid sufficient producers and lemma mines. Do not delete them; do not schedule them as mandatory while the R370/R380 route remains open.

## 9. R375--R380 source receipts

Selected receipts retained for investigation:

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
R380 source:    3fb0ced07b51f852e200ff2a8718ef7db594cc0f
R380 repair:    e8c7ff0fce6a30bc9fa62d27ff95371c97cc5c10
R348 stale-import repair:
                 4f8fc45c0c7b08a5eafcd50fb5ed1e34f220d14a
```

## 10. Verification boundary

R375–R380 are source-written reductions. `machineChecked` fields inside source are repository status values, not a fresh exact-head Agda receipt. The R348 import repair removes one known source-level blocker but does not constitute a kernel run. No continuum YM construction, mass gap, or Clay completion is claimed here.
