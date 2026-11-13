# Yang–Mills original P0 / Killing / Casimir / G1 / E1 deep reuse audit

**13 November 2026 · canonical owner Agda #1444; perturbative source Agda #1498.**

This audit was prompted by the user's 219-line proposed all-gates construction, especially the specific call to search **Killing**, Casimir, Coxeter, Combes–Thomas, same-H, matrix trace, Peierls/polymer, and geometric Cauchy across the repository instead of reasserting "missing". The actual #1444 head was enumerated through GitHub's recursive tree (31,762 paths; not truncated), then the exact source files below were inspected. This source-audit and its newly committed modules are NOT Agda kernel acceptance. All Clay endpoints remain open.

## A. Precise pre-existing proof inventory — paid, not to redo

| Mechanism | Actual source owner / declaration | Genuine established status |
|---|---|---|
| Cartan/Killing types | `CompactSimpleClassification.SimpleLieType`, `rank`, `dimension`, `dualCoxeter` | Total A/B/C/D and E6/E7/E8/F4/G2 formula functions; low simple ranks encoded in constructors; classification completeness imported |
| Uniform adjoint Casimir | `CompactSimpleClassificationAdjointCasimirExact.classificationAdjointCasimirPositive` and `classificationStrictCasimirCarrier` | Constructive exact rational proof of strict positivity **for every classified Lie type** |
| **Uniform floor beyond positivity** | `BalabanCompactSimpleUniversalBetaFloorExact.classificationAdjointCasimirAtLeastTwo`, `classificationGroupUniversalCoefficientAtLeastElevenTwelfths` | Already source-written: (2\le C_A(G)) and (11/12\le C_A(G)\cdot11/24), **no rank-dependent lower** |
| Group remainder budget | `BalabanCompactSimpleOneLoopRemainderBudgetExact.compactSimpleRemainderGivesUniformPositiveBeta`, `BalabanCompactSimplePositiveBetaFromSharedMarkedShellExact.fullBetaStrictlyPositive` | Remainder-to-beta algebra complete **conditional on actual literal local and irrelevant-memory remainders** |
| Casimir/colour representation algebra | `YangMillsCompactSimpleCasimirDynkinTraceExact.casimirDynkinDimensionBalance`, `adjointCasimirDynkinSameDimensionBalance` | Finite same-matrix Fubini trace/Casimir/Dynkin index arithmetic source-written; the concrete physical Wilson/FP/Haar colour contraction still requires evaluated source generators |
| Classical Killing metric | `CompactSimpleBiInvariantRicciReserveExact`, `CompactLieHeatDoobRicciReserveDebtExact.ricciReserveDebtGivesLSI` | (​\mathrm{Ric}=-\tfrac14 B), (​g=-B\Rightarrow\mathrm{Ric}=g/4) recorded at **standardImported** analytic boundary; product Ricci-reserve/LSI compiler is a conditional record and still requires a *physical same-metric heat generator* and *uniform cumulative negative Hessian debt* |
| Actual original group operations | `YangMillsConcreteStructuralSemanticsRound517Exact`, `YangMillsActualGroupQuantitativeConstructorRound569Exact`, `YangMillsActualGroupFiveBlockConstructorRound570Exact`, `YangMillsActualGroupSourceFirstCompleteRound571Exact` | Constructor ensures bracket, exp, log, Ad and five-block quantitative package are the same original operations. **Actual every-group witnesses, local chart/Haar/BCH bounds and five physical scalar estimates remain input records** |
| Finite physical Combes–Thomas | `BalabanP33PhysicalCombesThomasPromotionExact.physicalGreenKernelDecay`, `BalabanP33PhysicalCombesThomasSchurExact.physicalTiltedSquaredLower` | Strong finite 3072-coordinate SU2 geometry/Schur/half-gap algebra exists; actual Hessian stencil, row/column mass, coercivity and resolvent identities are sourced premises. Finite local Green decay is not the full continuum same-H OS gap |
| Rooted polymer tail | `BalabanClayT2UrsellCauchyExact.ursellCauchyTail`, `connectedCorrelationExponentialDecay` | Exact finite geometric sum and limit/connected implication **conditional on real physical `UrsellDepthMajorant` activity and original `InfiniteUrsellLimit`** |
| Full-cutoff Cauchy compiler | `BalabanContinuumScaleLocalObservableCauchyExact.scaleLocalCauchyTail`, `renormalizedObservableCauchyModulus` | **Already contains geometric scale-Cauchy proof. Do NOT add a duplicate `P0GeometricCauchyConvergence` as if its algebra were missing.** Requires true `ScaleLocalIncrementMajorant.incrementBelowScaleShell` for original Wilson observables |
| Three distinct source grades | `BalabanSharedMarkedAnalyticShellExact` | Beta-memory, physical spatial Hessian, and composite/OPE depth are **typed separately**; a shared bound method does NOT equate those metrics. Actual original mark-wise estimates still need proofs |
| Canonical original full Wilson measure | `YMClayOriginalWilsonPhysicalF19PartitionExact`, `YMClayOriginalWilsonCanonicalBlockedMarkF19Exact.originalCanonicalBlockedNormalizedEqualsPhysicalEffective` | Actual 1024-link full physical Wilson disintegration, positive same-Z and **every canonical blocked-holonomy normalized moment** now source-written; kernel pending, not just partition-only |
| Physical original E1/R445 3→1 identity | `YMClayE1A3OriginalR445CrossCutoffSourceExact.originalE1FineBlockedIsR445EffectiveCoarse` | Actual original side-four blocked Wilson expectation equals original R445 effective; original side-two bare Wilson expectation remains a separate law |
| Original covariance telescope | `YMClayE1D1OriginalR445QuantitativeThreeMomentRGCutExact.originalR445CovarianceErrorFromThreeSourceMoments` | Three genuine original F/G/FG errors + two real moment majorants imply covariance/J11 error; physical moment sizes remain OPEN |

**Important distinct "Killing" lane:** `DASHI.Physics.Closure.YMKillingBoundarySelfAdjointnessTheoremBoundary` and `YMAKillingBoundaryLocalArithmetic` concern an **older finite YM-A Hamiltonian boundary/flux/quotient theorem**, not the Killing metric/dual-Coxeter proof above. Their lightweight `Bool` receipt indicators and SU2/SU3 arithmetic must NOT be mistaken for the full physical OS spectral gap or an all-group Yang–Mills theorem.

## Additional native trace and merged-PR reuse

The original PR search found these authoritative older donors: [Agda #143](https://github.com/chboishabba/dashi_agda/pull/143), merged generic compact Lie groups; [#153](https://github.com/chboishabba/dashi_agda/pull/153), merged SU(N) matrix/analytic stack; [#583](https://github.com/chboishabba/dashi_agda/pull/583), merged Round61–87 literal Ward/Killing/Casimir and marked-stress work. [#1281](https://github.com/chboishabba/dashi_agda/pull/1281) and [#1287](https://github.com/chboishabba/dashi_agda/pull/1287) are still open TOE consistency/convergence branches. [#393](https://github.com/chboishabba/dashi_agda/pull/393) (finite Schur/CT) and [#461](https://github.com/chboishabba/dashi_agda/pull/461) (group/gap guards) are historically closed but NOT merged; their concepts are extensively present in the current source tree and require exact import checking before any PR-head cherry-pick.

- `BalabanSU2RationalWilsonTraceBoundExact.normalizedTraceBound` **already constructs** `-1 ≤ Re(q) ≤ 1` on the true selected rational unit-quaternion SU2 carrier. Do NOT demand a generic proof of even SU2 trace range anew. The arbitrary-N real source still needs a faithful map to a genuine finite complex matrix entry/trace implementation.
- `NSTriadKNExactFiniteComplexCauchySchwarzRound65.finiteComplexInnerProduct` defines a literal complex Hermitian finite pairing on the source's `NSTriadKNComplex3ExactCarrier` and a typed `ExactFiniteComplexCauchySchwarz` record, but its `finiteCauchySchwarz` inequality field is **not** universally inhabited. This is a valid cross-PR donor for matrix row-norm proof design, not an automatically established native trace bound.
- `SU3MatrixInstance.su3MatrixGroup` constructs a group from a supplied `CertifiedSUNMatrixTheory 3`; the actual indexed complex-matrix operations and trace/eigenvalue inequalities remain standard-imported inputs, not generated by the numeral 3.
- `CompactLieRepresentationData.RootStructureData` and `HaarMeasureData` already specify roots, representation, invariant Haar, root/structure constant bounds, character/Weyl formulas; their record fields are **genuine source obligations** rather than named arbitrary constants one can discard.
- The old `YMKillingBoundary...` theorem-boundary branch is unrelated to the simple Lie Killing form: do not use boolean source flags as physical self-adjointness receipts.

## B. NEW source-specific code committed on #1444

### B1. True original E1 changing-cutoff moment weld

`YMClayE1OriginalR445ThreeMomentCutoffTransportExact.agda` proves, on the SAME source n=3 original Wilson blocked and n=1 original bare Wilson measures:

```
originalE1FineBlockedIsOriginalR445Effective
originalE1BareCoarseIsOriginalR445Bare
originalE1MomentResidualIsR445MomentResidual
originalE1ThreeMomentSameSource      -- F, G and F*G simultaneously
originalE1FineBlockedCovarianceIsR445Effective
originalE1FineMinusBareCovarianceIsR445Error
originalE1CovarianceErrorFromThreePhysicalCutoffMoments
```

It is a genuine physical-**source identity**, not the missing smallness of those moments. The final consumer takes the **original E1** F/G/FG error estimates, transports each along the exact original 3→1 R445 equality and invokes the already source-written original quantitative covariance bound. It does NOT introduce arbitrary `Measure`, a proxy effective density, a group-generic fake trace or a new number-valued RG bound.

### B2. N1 correct observable class

`YMClayN1GaussianNonlinearFourthCumulantNoGoExact.agda` proves two exact rational Wick moment combinations:

- Standard Gaussian linear X: (​\kappa_4(X)=3-3(1)^2=0).
- Nonlinear observable W=X² of the same Gaussian field: (​\kappa_4(W)=105-4\cdot15-3\cdot9+12\cdot3-6=48\ne0).

The **classical Gaussian moment identities** are cited inputs, not a formal Agda Gaussian measure construction. This invalidates the attachment's attempted inference "nonzero connected FOURTH cumulant of WILSON LOOPS ⇒ underlying field non-Gaussian"; Wilson loops are nonlinear observables too. For a valid N1, select a physical gauge-invariant continuum generating-functional/cumulant comparison with a *correctly derived* generalized-free Gaussian-null target, or exhibit another genuine interacting witness with original continuum source and bounded remainder.

### B3. Exact-rational source regression

`scripts/check_ym_source_killing_geometric_n1_20261113.py` verifies 270 finite geometric-tail identities, the two Gaussian cumulants, and 4101 classified first-rank/higher-rank group coefficient samples. The **universal all-types theorem itself** is the existing `BalabanCompactSimpleUniversalBetaFloorExact`, not the finite test. Independent Python execution: PASS.

`scripts/check_ym_r445_p0_maxcut_local.sh` and `scripts/check_ym_original_rg_p0_kernel.sh` now target the new original E1/R445 and N1 source modules. These checks require the pinned Agda 2.9/Nix source checkout; they were **not executed** in the available assistant container.

## C. Attachment claim corrections affecting the *actual* seven-gate max cut

### C1. Geometric convergence arithmetic is a paid algebraic lemma, not a physical producer

For a hypothesized actual original Wilson scale step (​|s_{k+1}-s_k|\le C4^{-k}) the **correct** tail is

```
sum_{k=n}^infinity 4^-k = (4/3) 4^-n,
```

not `(1/3) 4^-n` as stated in the attachment (except when the sum starts at `n+1`). Even that corrected elementary Cauchy theorem is already covered by `BalabanContinuumScaleLocalObservableCauchyExact` using its own (\tfrac14 2^{-n}) shell envelope. The actual source (​|E_{k+1}[W]-E_k[W]|\le C_W g_k^2 4^{-k}) remains unproved; neither Wilson-loop closedness nor a guessed covariance Green bound establishes it without real gauge fixing, Wilson perimeter renormalization, Hessian/Taylor remainder and uniform volume/cutoff estimates.

A physical **relevant/marginal** Wilson observable need not enjoy a free (4^{-k}) irrelevant-operator factor. One must identify the renormalized observable, not merely insert an (a_k^2/R^2) unit factor.

### C2. Coupling trajectory orientation must match Bałaban source

`BalabanYM4SourceNormalizedCouplingRecurrenceExact` already proves original (​u_k=u_{k+1}+\beta_{k+1}), (​u_k=1/g_k^2). Increasing `k` in this source runs **coarser**, while positive beta makes inverse coupling grow toward **UV** when iterated BACKWARD. The attachment's (​k\to k+1) UV formula silently changes direction. This matters before identifying a `g_k²~1/k` asymptotic with any actual original source RG step.

### C3. D1 group and polymer activities

`BalabanP33PhysicalCombesThomasPromotionExact`, `BalabanSharedMarkedAnalyticShellExact`, `BalabanClayT2UrsellCauchyExact`, `CompactLieHeatDoobRicciReserveDebtExact` and its positive Killing-metric reserve are strong reusable compilers. The **actual physical** source-dependent small/large-field cluster activities, original heat/Doob negative Hessian debt and correct physical-distance scaling remain uninhabited. A proposed (​ m_1= -\log(C_1g_k^2+e^{-c_0/g_k^2})) only evaluates an algebraic envelope after a true Wilson/KP/Peierls cluster estimate with measured constants; it is not the estimate itself.

### C4. D2 same-H

The OS spectral theorem implication is standard. A common decay **exponent** on a norm-dense original vacuum-orthogonal core can eliminate hidden sub-threshold spectral components (even if pre-exponential constants depend on each test, via spectral-support arguments), provided the semigroup and original-time covariance identity are actually proved. The source physical continuum OS reconstruction, correct time translation, spectral-domain density and common original Wilson decay remain real physics. Do not weaken the problem to a finite (P33) Hessian gap or a selected correlator.

### C5. N1 vs nonlinear Wilson-loop cumulant

See B2. The Gaussian comparison target in the attachment is false for general nonlinear observables. A nonzero Wilson-loop 4-point connected cumulant does not by itself rule out a Gaussian underlying gauge field. A true interacting witness needs source-appropriate regularized gauge-invariant fields and a certified **correct** free/null comparison.

### C6. G1 is MUCH further advanced in-repo, but the last physical construction is not a Coxeter integer

The existing group Lie-type code proves (C_A\ge2) and (b_G\ge11/12) at the original repo's rational **`C_A*11/24`** one-loop source normalization. The attachment uses a different (16\pi^2) convention. Do not silently identify them; an exact source coefficient-map must precede universal beta comparisons.

Moreover G1 requires **actual** `YangMillsConcreteStructuralSemanticsRound517Exact.StructuralSourceBundle`, `YangMillsActualGroupQuantitativeConstructorRound569Exact.ActualGroupQuantitativeSource`, and `YangMillsActualGroupFiveBlockConstructorRound570Exact.ActualGroupFiveBlockCompleteSource` for the same group operations. The R571 and `YangMillsCompactSimplePerGroupQuantitativeTheoremExact` constructors already compose them and remove operation-alignment boilerplate. Still open: constructing those actual physical packages across each global compact-simple group (not merely Lie algebra type), with source heat/LSI, Haar/BCH and Wilson/FP/Haar beta matching, physical continuum E1 and D1/D2/N1.

## D. Source-specific physical maximum-cut (avoid redoing the paid algebra)

The existing `BalabanClayHighestAlphaRound83SevenAnalyticLemmaExact` already lists the sharpened **seven genuinely new analytic families**, not seven missing formal connectors:

1. L1 source literal Wilson + reduced-FP + Haar Ward tensor scalar = classified (C_A\cdot 11/24) with real physical local remainder.
2. L2 one original **mark-parametric differentiated shell norm** and three *correctly graded* same-source beta-history, spatial-Hessian and composite insertion identifications.
3. L3 continuous-time negative Hessian **per-shell integral** under the original group heat/Doob path (aggregate LSI compiler is paid).
4. L4 same-E1 original continuum gauge-invariant renormalized curvature/composite fields.
5. L5 true original composite/OPE source and asymptotic-free coefficient identification (geometric tail algebra paid).
6. L6 original continuum renormalized stress tensor and translation Ward identity.
7. L7 original continuum stress-charge integral equals the **same** OS self-adjoint Hamiltonian.

These physical leaves are not all independent of the E1/D1/D2/N1/G1 route, but each has a different original-source semantic target. The other P0 physical matched F/G/FG three-moment effective-vs-bare estimates remain open. **No new Clay physical endpoint is closed by this audit or the attached proposed estimates.**

## E. Receipt & next paid step

| Scope | This turn |
|---|---|
| Broad original GitHub source tree | 31,762 paths on #1444 head, recursive tree **not truncated** |
| Original Killing, Ricci, group, Combes–Thomas, Cauchy, Marked Shell and R571 sources | Retrieved exact declarations and source boundary comments |
| Actual source-code addition | Original E1/R445 3→1 three-moment/covariance bridge; Gaussian nonlinear-observable N1 counterexample |
| Exact rational checks | 270 geometric, 4101 Casimir lower-bound samples, linear/nonlinear Gaussian (​\kappa_4=0/48): PASS |
| Local Agda 2.9 | Not available; cannot mark kernel accepted |
| New physical Wilson RG/continuum/spectral result | **None** |

**Next highest-alpha producer** is the actual marked source-normalized Wilson/FP/Haar L1 coefficient and the physical *marked scale-local* increment from original R445 n=3 to n=1 with arbitrary cutoff/volume. Scalar Bishop transport and a genuinely normalized arbitrary SU(N) entrywise trace are separate source prerequisites; neither can be paid by (Z_{\rm fine}>0) in the independent postulated legacy real type. The attached choice to work on source-level killing/Casimir is correct but the key Casimir arithmetic is already proved; the hard target is its original physical estimate/normalization.
