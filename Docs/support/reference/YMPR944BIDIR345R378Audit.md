# YM PR #944 BIDI Audit — R345 through R378

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
| R346 | shared marked amplitude direct carrier | active downstream donor |
| R347–R348 | selected coefficient / mixed-log attachment split | `C_attach` remains application debt |
| R349 | selected distance carrier weld | stronger distance route donor |
| R350 | split selected Hessian comparison into `H_stab` + `H_sub` | structural cut retained |
| R351 | source substitution displacement + selected attachment | **reduced by R378** |
| R352 | source local Hessian stability + selected attachment | selected attachment remains |
| R353 | marked-walk/H_scale resummation | optional producer after R375/R378 |
| R354 | charged CMP116 summability split | optional marked-walk producer |
| R355 | coefficient-collar charge exponent inequality | optional marked-walk producer |
| R356 | connected collar span / large-tree compiler | compiler |
| R357 | weighted collar compiler from unweighted alternative + rate calibration | compiler |
| R358 | literal support metric attachment (`G_exit`, `G_tree`) | optional route debt |
| R359 | positive source decay-rate split | optional route debt |
| R360–R363 | marked distance / exponent / summability / factorwise attachments | optional route |
| R364 | direct analytic-path/Hessian route | superseded as mandatory by R372 |
| R365 | fixed-point perturbation compiler | optional route |
| R366 | one-step map defect / boundary substitution scale | optional route |
| R367 | CMP102 / canonical substitution contraction-rate investigations | optional route |
| R368 | direct CMP116 fixed-parameter contraction | source donor |
| R369 | affine argument difference | generic compiler |
| R370 | direct Cauchy/mean-value parametric fixed-point sensitivity | **active donor** |
| R371 | published CMP116 parametric fixed-point source ABI | **active source parent** |
| R372 | direct local-Hessian sensitivity using same parametric ABI | **active donor** |
| R373 | joint parametric / selected Hessian scalar attachment | active carrier |
| R374 | one canonical CMP116 radius for first + second derivative consumers | duplicate radius debt removed |
| R375 | direct Hessian sensitivity -> existing marked coefficient Cauchy lift | H_scale no longer mandatory |
| R376 | R351 `H_sub` source/attachment feeds R375 | compiler |
| R377 | canonical selected substitution distance; duplicate R351/R373 equality becomes definitional | active carrier correction |
| **R378** | R370 parametric displacement -> exact R351 source ABI via one scalar mark calibration | **current Pareto recut** |

## 3. Current BIDI spine

```text
CMP116 published analytic fixed-point family (R371)
  -> direct parametric sensitivity (R370)
  -> d_sub <= L_par(M,r) * d_parameter
  -> [ONE source/application calibration]
       L_par(M,r) * d_parameter <= M_marked
  -> R378 constructs R351 source object
  -> R351 selected attachment
  -> R377 canonical selected distance
  -> R376
  -> R375 marked coefficient/Hessian payment.
```

Local-Hessian side:

```text
same CMP116 differentiated analytic family
  -> R372 local Hessian sensitivity
  -> R373 same selected scalar carrier
  -> R375 coefficient lift.
```

## 4. What R378 removed

Before R378, R351 exposed as primitive:

```text
d_sub^src(s) <= M_marked^src.
```

R378 factors this through existing R370:

```text
d_sub(s)
  <= sourceParametricLipschitz * sourceParameterDistance
  <= M_marked.
```

Therefore a standalone new substituted-background displacement theorem is no longer primitive. The remaining payment is the second inequality plus the same-object family/domain/radius/metric attachments required by R370/R371.

## 5. Primary source evidence

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

This source supports the R370/R371 theorem shape. It does **not** by itself identify the selected DASHI parameter metric or prove the final parameter-to-mark calibration.

## 6. R375–R378 commit receipts

User/current branch receipts retained for investigation:

```text
R375 RED:       1518978e...
R375 BIDI:      0e0e78f9...
validation fix: 04e0aea6...
R376 RED:       123882fd...
R376 splice:    38407483...
source repair:  bf63ecd7...
R375 literal Hessian family repair:
                 daedbcf53509423b7528a4f84d9fdf91caee5b0c
R377 corrected head:
                 f328de90539921b548a8477c7a0db28ddfd4550f
R378 RED:       19c862a371aa495952ac8d9d22317b30ecaba047
R378 GREEN:     c51dc43798161ee018844bffe75120489624f779
Pareto board:   355abff1543c857982cf7684224e9cd8b54a7004
```

## 7. Current non-dominated search targets

1. selected/published CMP116 fixed-point family same-object attachment;
2. common source neighbourhood membership for the selected parameters;
3. canonical source radius/magnitude interpretation on that family;
4. selected parameter-distance calibration;
5. **`sourceParametricLipschitz * sourceParameterDistance <= sourceMarkedInput`**;
6. R351 selected mark attachment / R377 selected carrier;
7. R352 selected local-Hessian attachment;
8. R348 `C_attach`;
9. R346 `D_time` / same-family continuum covariance transport.

If item 5 is source-replayable from an existing mark normalization, the dedicated `H_sub` theorem disappears entirely from this direct BIDI leg.

## 8. Dominated routes retained for archaeology

- R353–R363 marked-walk/H_scale programme;
- R364 separate higher-derivative analytic-path presentation;
- R365–R369 contraction/cross-map-defect route;
- CMP102-Lipschitz/cross-propagator route.

These remain valid sufficient producers and lemma mines. Do not delete them; do not schedule them as mandatory while the R370/R378 route remains open.

## 9. Verification boundary

R375–R378 are source-written reductions. `machineChecked` fields inside source are repository status values, not a fresh exact-head Agda receipt. No continuum YM construction, mass gap, or Clay completion is claimed here.
