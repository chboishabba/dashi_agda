# Yang–Mills E1/D2/N1/G1 — executable maximum-cut roadmap
**Date:** 2026-11-09. **Owner:** PR #1444 on `research/ym-voyager2026-completeness-crosswalk-20261101`.
**Rule:** This is a phase/deliverable/theorem inventory, not a claim to have solved 4D Yang–Mills. An artifact is DONE only with an Agda 2.9 kernel receipt on the exact source; physics gates additionally require proof of independently selected ORIGINAL Wilson/E1 identities and nonvacuous physical conditions.

## Selected canonical route and reused producers
Use the **same** group-indexed original Wilson measure family throughout:
- `YMClayE1OriginalSUNDependentCylinderExact.agda`: `ActualLinks n`, `actualOriginalWilsonMeasureAt n`, `actualOriginalWilsonCylinderExpectation`, `nativeSUNSelectedFiniteExpectationIsLiteralWilson`. This pays the *finite source* identity only.
- `YMClayE1VariableCutoffCylinderLimitExact.agda`: `ActualVariableCutoffCylinderFamily`, especially its field `originalWilsonConverges`; conditional positivity/linearity/normalisation transport already exists.
- `YangMillsClayCriticalPathRound562Exact.agda`: existing A3/T1/T5/B1/B2/G1/H6 maximal-cut scheduler. Do not reopen R499 all-observable, Prokhorov, printed-J or finite-Mosco detours merely to create work.
- `YMClayDirectSourceOSMassGapFrontierExact.agda`: direct H1/H2/H3 → OS mass-gap route, using original Wilson tests and same reconstructed OS Hamiltonian; its `physicalDirectSourceOSRouteLevel` is conditional.
- `YangMillsClayMinimalH6NontrivialityRound550Exact.agda`: `Goal1MinimalH6Bridge`; only the actual same-family Ward/gap-to-interacting physical witnesses are unpaid, not another OPE compiler.
- `YangMillsDirectSourceOSCompactSimpleH5Exact.agda`: `LiteralCompactSimpleDirectSourceContinuation.continueLiteralDirectSource`, not automatic SU(N) relabelling.
- `YangMillsClayTopDownFiveTheoremClosureExact.agda`: full official Clay endpoint requires *all* construction/OS/field/nontriviality facts on the same `LiteralYangMillsConstruction`.

## Phase 0 — source, acceptance and no-go regression (P0, first)
**Deliverable D0:** One native regression root importing the exact E1 changing-carrier, Round562 critical path, direct H1/H2/H3, H6, H5 modules; check `agda --safe` where dependencies permit; store exact command, source SHA, Agda version, exit status, holes/postulates and transitive import failures. DO NOT label source-written code kernel-checked.
**Exact leaves:** `originalWilsonConverges`, `a3ProjectiveConsistencyLevel`, `a3ContinuityAtEmptyLevel`, `w3ConnectingWeightTailLevel`, `h3TransferCoordinateOfOSHamiltonianLevel`, `literalRound550MinimalWardKernelLevel`, `continueLiteralDirectSource`.
**Negative controls:** arbitrary cutoff-parity cylinder sections have no limit; an unrenormalised fixed-support plaquette variance may collapse; a finite Markov/heat-bath generator is not the OS Hamiltonian; SU(N) covers neither B/C/D nor exceptional types.

## Phase 1 — E1: original interacting continuum existence (P0/P1)
**Selected obligation:** For a *defined nonempty gauge-invariant, local, continuum-labelled original Wilson cylinder algebra* \(\mathcal A\), for each cylinder \(F\) prove existence of \(L(F)\) with
\[
\lim_{n\to\infty}\mathbb E_{\mu^{\mathrm{Wilson}}_{G,n}}[F_n]=L(F)
\]
with same selected bare-coupling trajectory, lattice spacing, volume/thermodynamic scaling and actual group. NOT the full type of arbitrary sections \(n\mapsto F_n\).

**Exact existing terminal field:** `ActualVariableCutoffCylinderFamily.originalWilsonConverges`.
**Proposed exact source-native leaves to implement (not extant theorems):**
1. `originalWilsonAdmissibleLocalCylinderIsNonempty`: the selected original local/gauge-invariant cylinder class contains a nonconstant test; no parity-varying arbitrary sections.
2. `originalWilsonCylinderProjectiveComparison`: same-observable comparison across two actual lattice cutoffs/volumes using the selected refinement maps and RG history, not a fictitious common configuration carrier.
3. `originalWilsonCylinderUniformCauchy`: a *uniform in finite volume* modulus for the exact source expectations of each admissible cylinder as physical lattice spacing tends to zero.
4. `originalWilsonCylinderLimitInRealCompletion`: construct real limits via the pinned Bishop/real completion, independent of arbitrary extraction choices.
5. `originalWilsonConvergesFromNativeModulus`: inhabit the existing `originalWilsonConverges` for each selected \(F\); prove actual-Wilson source identity via `nativeSUNSelectedFiniteExpectationIsLiteralWilson`.
6. `originalWilsonLimitOsterwalderSchraderAndInteracting`: prove projective/OS positivity, Euclidean covariance/locality, nontrivial interaction and the continuum axiom requirements, not just positivity of a functional.
**Completion criterion E1:** a kernel-accepted inhabitant of the selected original-family convergence with OS/QFT axioms and genuine interaction; one subsequence on a constant cylinder, a conditional input record or a free/zero theory does NOT close E1.

## Phase 2 — D2: same-E1 OS Hamiltonian and physical mass gap (P0/P1, dependent on E1)
**Exact owner:** `YMClayDirectSourceOSMassGapFrontierExact.directSourceOSBuildsPhysicalMassGap`; `YangMillsClayCriticalPathRound562Exact` B1/B2; selected R333/R331/R316 OS source.
**Proposed source-native leaves:**
1. `sameE1WilsonReflectionPositiveGram`: actual E1 reflection-positive Wilson cylinder Gram, not a different selected measure or fine-positive-weight surrogate.
2. `sameE1OSNullQuotientAndCompletion`: physical Hilbert space by null quotient and dense completion with noncollapsed tests.
3. `sameE1PhysicalTimeTranslationSemigroup`: actual Euclidean physical-time transfer on that completion, with correct scale and one reconstructed self-adjoint nonnegative \(H\).
4. `originalWilsonTwoMarkClusterActivityUniform`: original sparse frustrated/mixed activity estimate; source-specific `BalabanLiteralTwoWilsonCMP116ConnectingTailExact.chargeSumBelowPhysicalRootedShell`, not counting-only P06.
5. `sameE1SelectedWilsonPhysicalTimeDecay`: a strictly positive rate for the same E1 observable subspace from the original source, cutoff-uniform in *physical units*, not only integer lattice shells.
6. `sameE1OSSpectrumAbovePositiveMass`: establish \(\inf\sigma(H|\mathcal H_{\mathrm{vac}}^\perp)>0\), including density/spectral transfer, excluding vacuum and spectral pollution.
**Completion criterion D2:** mass gap for the **same E1** OS Hamiltonian with common physical-time decay and a nontrivial complement; an arbitrary Markov mixing estimate, formal half-rate translator, or different OS carrier fails.

## Phase 3 — N1: continuum observable and interacting noncollapse (P0/P1, dependent on E1)
**Existing owners:** `YangMillsClayMinimalH6NontrivialityRound550Exact.Goal1MinimalH6Bridge` and R549 minimal Gaussian Ward contradiction; finite SU(2) original-plaquette fluctuation work.
**Proposed source-native leaves:**
1. `originalWilsonRenormalizedLocalTestDefined`: construct one nonconstant gauge-invariant local observable family \(O_{n,f}\) with fixed physical smearing/renormalization and exact original Wilson provenance.
2. `originalWilsonRenormalizedTestUniformMomentBound`: finite expectation/tightness/moment control for that same observable under the E1 family.
3. `originalWilsonRenormalizedVariancePositiveLimit`: prove \(\liminf_n\mathrm{Var}_{\mu_{G,n}}(O_{n,f})>0\) with a **cutoff-independent** positive constant; fixed-\(\beta\) finite plaquette variance does not suffice.
4. `sameE1ObservableLimitAndVarianceIdentity`: identify E1 continuum test and variance with the actual original Wilson limits.
5. `sameE1MinimalWardKernel`: instantiate R549's same-family Ward kernel or another valid non-Gaussianity witness; avoid replacing nontrivial interaction by mere nonzero variance of a free field.
6. `sameE1InteractingWitnessPreserved`: instantiate the two relevant `Goal1MinimalH6Bridge` physical fields, yielding original continuum interacting nontriviality.
**Completion criterion N1:** nonzero surviving same-E1 observable AND a non-Gaussian/interacting witness when required, with actual local QFT sourcing. No tautological witness or arbitrary continuum observable.

## Phase 4 — G1: every compact simple G, not only SU(N) (P1/P2, dependent on E1/D2/N1)
**Existing owner:** `YangMillsDirectSourceOSCompactSimpleH5Exact.LiteralCompactSimpleDirectSourceContinuation.continueLiteralDirectSource` (currently conditional); `YangMillsCompactSimpleGroupPromotionExact` firewall; `CompactSimpleClassificationAdjointCasimirExact`.
**Proposed source-native leaves:**
1. `compactSimpleLiteralGroupRoundtrip`: reuse existing classified↔literal group roundtrip without changing group universe.
2. `compactSimpleOriginalWilsonHaarAndRG`: construct actual original Yang–Mills Wilson and RG/Gibbs data for each classified A/B/C/D/G2/F4/E6/E7/E8 and required isogenies, not just \(C_A>0\).
3. `compactSimplePerGroupUniformInCutoffPhysicalBounds`: for each G, cutoff-independent-in-physical-units required estimates; constants **may depend on G**.
4. `compactSimplePerGroupE1D2N1`: derive completed same-G E1 continuum, same-H gap and interacting nontriviality from source data.
5. `continueLiteralDirectSourceFromNativeGroupData`: inhabit existing `continueLiteralDirectSource` for every classified G, retaining exact type correspondence.
6. `clayEveryCompactSimpleGroup`: quantified final `Top.LiteralYangMillsConstruction` evidence, no SU(N) promotion shortcut.
**Completion criterion G1:** explicit quantified physical source and terminal proof for every compact simple group, not an inhabited abstract record whose fields restate the goals.

## Execution order and hard stops
Priority ordering:
- **P0 E1.01/E1.02:** select admissible original local cylinders and actual projective/refinement comparisons; they unlock the meaning of all downstream same-E1 claims.
- **P0 B1/D2.04:** source-specific sparse frustrated/mixed activity + CMP116 connecting sum. Generic animal-count/P06 and KP finite compilers already exist.
- **P0 N1.01/N1.02:** choose actual renormalized Wilson test and source moments *before* making noncollapse claims.
- **P1 E1.03→E1.06, D2.01→D2.06, N1.03→N1.06:** develop original analytic inequalities, explicit constants, and kernel receipts.
- **P1/P2 G1.02→G1.06:** group-by-group reuse after fixed-G physics, with quantified parametric continuation.
- Gate status is determined by proof evidence, not whether the roadmap line or conditional compiler exists.

**Precise critical dependency:** G1 requires a functorial parametric continuation of the completed same-source E1/D2/N1 theory; E1 is not automatically proved by existence of finite Wilson Gibbs measures, D2 not by positivity of finite weights, N1 not by finite positive variance.


## 2026-11-09 execution update — preferred Round578 and actual original-source E1 unit base case

**Correction of canonical path:** `YangMillsClayCriticalPathRound578Exact.agda` is newer and narrower than Round562. It imports `YangMillsClayPreferredA3FiniteProjectionRound566Exact`, `YangMillsWilsonPathFiniteFactorizationRound568Exact`, `YangMillsPreferredWilsonWEXTSourceRound576Exact`, `YangMillsPreferredSameHamiltonianTransferRound577Exact`, `YangMillsActualGroupSourceFirstCompleteRound571Exact`, and `YangMillsSameFamilyWardKernelSourceRound563Exact`. For all follow-on implementation, **use Round578 as the shortest preferred critical route**; Round562 remains historical comparison, not the canonical remaining cut.

**Repaid finite E1 source leaf:** `YMClayE1OriginalSUNDependentCylinderExact.agda` now contains:
- `originalWilsonUnitCylinderExpectationIsOne`: transports **the existing actual original Wilson** R445 `originalWilsonExpectationOfUnitIsOne` for every changing-cutoff link carrier. Inputs are actual selected one-link Haar ordered laws, strict positivity, strict-to-weak order and scalar self-division cancellation. Not an arbitrary finite-state normalisation assertion.
- `originalWilsonUnitCylinderConverges`: uses `SelectedScalarConvergence.convergenceCongruent` and `constantConverges` to show the literal original Wilson *unit cylinder* converges to `1ℝ` on every cutoff. It does not assume an E1 all-observable limit.

This is the source-level **normalisation/convergence base case**. It does not establish the nonconstant gauge-invariant Wilson finite-projection factorization on the independently selected continuum projective configuration system, projective event consistency, continuity at empty, or the actual continuum convergence of interacting Wilson products. Avoid counting this as E1 closure.

**Revised highest-alpha E1 exact leaves:** construct the original selected Wilson path-to-projective-coordinate identification (R568 remaining `literalRound568PathProjectionBelongsToSelectedProjectiveSystemLevel`), prove A3 event consistency and continuity at empty (R566), and recover nonconstant selected expectations with an original-source uniform/Cauchy or projective representation theorem. Reuse R568 finite-path word factorization; do not rewrite it. B1 remains the R576 actual two-source mixed-log cluster expansion and connected-weight tail; B2 remains the R577 physical transfer coordinate of *the reconstructed* Hamiltonian; G1 remains R571, H6 R563.

**Verification honesty:** source written and repository readback only; no Agda kernel receipt. The E1 constant-cylinder proof is a nontrivial finite integration/same-source consumer but not a Clay continuum construction.


## 2026-11-09 E1/A3 source-native arbitrary-word finite-support proof

New module `YMClayE1A3OriginalAllWordPathSupportExtensionalExact.agda`, imported into `YMClayOriginalWilsonPhysicalRegression.agda`, reuses actual original signed Wilson path support rather than assuming independent finite coordinates.

The module defines `appendSource` with constructive `appendSourceLeft`/`appendSourceRight` membership transports, and `originalWordActualFlatPositiveBondSupport` (the recursively flattened **actual** positive-link lookup list for a sequence of original source plaquettes). It then supplies:

- `originalPlaquetteTraceSourceExtensional`: original SU(N) one-plaquette *real trace* equality whenever actual underlying positive-link fields agree on the signed path lookup support, via existing `originalWilsonPlaquetteHolonomyExtensional`;
- `originalWordRealSourceExtensional`: induction over the original all-length source plaquette word. If two actual cutoff-n link configurations agree on **every positive bond genuinely read by the full word**, their actual real Wilson word values agree. This includes negative-step predecessor links, not just geometric endpoint adjacency.

This discharges the *all-word finite support/locality* proof obligation in the actual changing-cutoff SU(N) source. It **does not** identify that support with an independently selected continuum projective coordinate. The still-open R568/R566 producer is `literalRound568PathProjectionBelongsToSelectedProjectiveSystemLevel` plus A3 positive event semantics, Boolean algebra, projective consistency, continuity-at-empty, and the finite-to-continuum expectation/measure comparison. In particular, finite path dependence cannot itself prove equality of independently selected cutoff Gibbs marginals.

Physical B1: source-first KP cluster bidegree (1,1) germ, original marked log-jet equality, pointwise source Wilson localization and `localizedLiteralShellChargeSum` remain to be instantiated (R578/B1Source); the generic P06 polymer-animal counting is already available. B2: R577 transfer of actual reconstructed H. H6: R563 non-Gaussian Ward kernel on the same E1 system. G1: R571 actual group data and physical five-block bounds, not classification alone.

**Acceptance:** code committed and source read back. Agda command missing from environment; kernel acceptance unresolved. Do not claim original interacting continuum E1 or any Clay terminal gate from this finite locality lemma.

**Additional finite A3 size theorem:** `YMClayE1A3OriginalAllWordPathSupportExtensionalExact.originalWordActualLookupSlotsExactlyFourPerPlaquette` gives exactly four native signed-path positive-link lookup slots per original plaquette for all finite source words and every periodic side length. It composes `sourceLookupSlotsAppend` with the existing original four-slot path theorem; read-slot count is not confused with number of distinct positive-link variables. Source-written only, kernel receipt pending.


## 2026-11-09 E1/A3 concrete finite-list projection and extension consistency

`YMClayE1A3OriginalFiniteCoordinateProjectionExact.agda` now supplies a concrete, source-paid finite projective coordinate `originalWilsonWordFiniteValues`: a **List (SUNMatrixElement theory)** of the actual original positive-link values read by the signed path of each selected original plaquette word. It does not use a full link field disguised as a finite coordinate. The following declarations are source-written:

1. `consHeadInjective` / `consTailInjective`: constructive list equality destructors.
2. `sameOriginalFiniteBondValuesImpliesPointwiseAgreement`: if the actual sampled group-value lists agree, the original link fields agree at each bond on the selected finite list; repeated bonds are allowed.
3. `originalWilsonWordFactorsThroughActualFiniteValues`: use the existing all-word actual signed-path extensional theorem to prove equality of real Wilson-word observables whenever those actual sampled value lists agree.
4. `originalFiniteValuesAppend`: restriction to a concatenation of source support lists equals concatenation of the actual sampled coordinate lists.
5. `originalWilsonWordFiniteCoordinateCons`: prepending an original plaquette to a Wilson word prepends precisely its four signed-path positive-link values to the earlier word projection.

This completes the *finite source-link-value projection factorization and word-extension algebra* proof contract at the source-written level (Agda kernel receipt outstanding). It **does not** discharge R568's external selected-projective-system identification: that requires an actual continuum projective configuration carrier and compatible refinement projections, not just the finite source list. Nor does finite-coordinate concatenation prove measure/projective consistency of original Gibbs distributions at different cutoffs. Keep R566 A3 projective event consistency and continuity-at-empty, R576 original mixed-log and connecting polymer bound, R577 reconstructed OS physical-time transfer, R563 Ward noncollapse, and R571 all-group physical source open.

Implementation also imported to `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda`. Verification state: committed/readback only; no Agda 2.9 compiler available.


## 2026-11-09: original signed-link positive-value DIRECT evaluator (E1/A3)

New source file: `DASHI/Physics/YangMills/YMClayE1A3OriginalSignedPathValueEvaluatorExact.agda`; imported into `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda`.

This strengthens previous E1/A3 finite-support extensionality and equality-under-projection results: it constructs a *direct computational evaluator* on the actually sampled finite positive-link values, with no full original field hidden inside the coordinate.

- `SignedPositiveLinkValues`: indexed by the actual signed-axis path, but stores values of underlying **positive** bonds only.
- `orientSample`: positive direction uses the sampled group element; negative direction applies the actual source inverse to the sampled predecessor-positive-link group element.
- `sampleOriginalSignedPath`: recursively reads exactly the same source bonds as the original nonabelian path evaluation; `evaluateOriginalSignedPath`: independently computes the ordered group product from those sampled values.
- `sampledOriginalSignedPathComputesHolonomy`: direct induction, ordered nonabelian multiplication preserved, proves equality with the actual `Bond.pathHolonomy`.
- `OriginalWordPositiveLinkValues`, `sampleOriginalWilsonWord`, `evaluateOriginalWilsonWord`: finite dependent tuple of all original plaquette-path positive-link samples and their real Wilson trace word evaluator.
- `originalWilsonWordDirectFiniteEvaluation`: original SU(N) signed Wilson word equals the finite tuple evaluator at every cutoff, by induction and the existing original `periodicSUNPositivePlaquette` trace semantics. The two sides are actual original Wilson functions, not newly invented continuum coordinates.

**Critical independence:** none of this invokes a generalized measure/projective authority or new source-specific physical hypothesis. The proof is finite lattice algebra only. It is the necessary R568 selected finite-coordinate *evaluation* ingredient, not the R568 assertion that this coordinate is a coordinate of the independently defined CONTINUUM projective system.

**Exact next E1/R566 consumer:** produce the selected continuum projective coordinate family and its refinement/forgetting maps from the existing repository original-lattice projection owner; identify each finite sampled original Wilson word with a compatible member of that family, then prove consistency of the **original cutoff-dependent interacting Gibbs expectations**. The finite evaluator is now available to phrase this identity without hidden full-field witnesses. It does not assert projective consistency of distinct Wilson Gibbs measures: an interacting RG/coarse-graining estimate is still needed.

**B1/B2/H6/G1:** unchanged mathematical original-source obligations in R576/R577/R563/R571. No source-dependent analytic bound is manufactured from this algebraic improvement.

**Verification:** GitHub source commits and readback; no Agda 2.9 binary available in working container. These declarations are **not** kernel-accepted until their regression and transitive imports typecheck.


## Same-cutoff original Wilson *finite* projective prefix seam (2026-11-09)

The direct source-value evaluator `YMClayE1A3OriginalSignedPathValueEvaluatorExact.agda` has been extended with actual dependent finite-coordinate inverse-system maps:
- `appendPlaquetteWords`: original plaquette-word concatenation;
- `forgetOriginalWordSuffix`: take the actual sampled values on a longer word `prefix ++ suffix` and forget precisely the suffix, returning the correctly indexed prefix sample;
- `sampleOriginalWordPrefixCommuting`: proves the commuting diagram
  `forgetOriginalWordSuffix prefix suffix (sampleOriginalWilsonWord realization (prefix ++ suffix)) ≡ sampleOriginalWilsonWord realization prefix`
  for **every** actual finite Wilson link realization, arbitrary original plaquette words and every periodic side length.

This pays a concrete *same-lattice word-index* projective naturality lemma; no additional abstract projective axioms, fake measure, or complete-field-as-coordinate trick.

**Do not promote as R566 probability consistency:** the group-valued sample forgetting diagram is not equality of `μ_n` original Wilson Gibbs marginals at distinct lattice cutoffs. The remaining P0 E1 cut is a selected common continuum projective carrier with physical-scale refinement maps and source-selected original expectation comparisons plus continuity-at-empty. The existing R538/R539/R534 and `YangMillsLiteralProjectiveCylinderSourceExact` compilers consume those source facts. This pass produced GitHub code only; no Agda binary or kernel acceptance available. 


## 2026-11-09 E1/A3 normalized original Gibbs expectation weld

New: `DASHI/Physics/YangMills/YMClayE1A3OriginalFiniteValueExpectationWeldExact.agda`, imported into `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda`.

This is the first source-written *measure-level* E1/A3 finite-coordinate result, not another abstract cylinder record. It reuses `YMClayOriginalVariableWilsonCovarianceSourceExact.originalWilsonExpectationExtensional`, itself proved from the genuine source one-link product Haar integral congruence, and `YMClayE1A3OriginalSignedPathValueEvaluatorExact.originalWilsonWordDirectFiniteEvaluation`:

- `directFiniteWilsonWord`: real-valued Wilson word evaluated entirely through the sampled source positive-link group values and original signed group inverse/holonomy operations;
- `originalDirectFiniteValueExpectationIsOriginalWilson`: for **every** cutoff, original word and finite-value evaluator have equal expectations under the **same actual normalized Wilson Gibbs/Haar measure**;
- `originalDirectFiniteValueExpectationIsOriginalE1Cylinder`: the expectation is precisely the actually selected E1 original cutoff-dependent plaquette-word cylinder expectation, not an alternative probability law;
- `originalPrefixFromExtendedFiniteSample` and `originalPrefixFromExtendedSampleEqualsDirect`: evaluate a selected word prefix by forgetting the suffix from a longer actual original sampled-value word; the evaluation is pointwise equal to direct prefix evaluation, via the native prefix commuting proof;
- `originalPrefixFromExtendedSampleExpectationIsWilson`: apply the actual source Wilson expectation extensionality to establish equality of normalized Gibbs expectations of those two fixed-cutoff representations.

**Sharp maximal cut after this:** the normalized *same-cutoff*, same-Gibbs, same-word finite-coordinate and prefix naturality calculation is now source-written. It does NOT imply a change-of-cutoff consistency theorem `E_{mu_upper}[f∘pi_{upper→lower}] = E_{mu_lower}[f]`. The actual Wilson RG blocking/pushforward and its physical scaling must discharge that statement, or one must prove convergence via the alternative marginal compactness/subsequence route with a selected continuum-limit identification. R566 A3 event consistency/continuity-at-empty, R576 B1 actual connecting activities, R577 B2 physical transfer, R563 H6 noncollapse and R571 G1 group physics remain live.

**Verification:** committed and read back from GitHub; no Agda 2.9 typecheck has been run. Neither same-cutoff source-written lemma nor roadmap is a Clay terminal proof.

 
## 2026-11-10 E1/A3 actual one-step original Wilson RG pushforward

The repository already contained the **genuine interacting** R445 4-to-2 periodic SU(N) two-link holonomy block in `YMClaySUNSideFourBlockedPushforwardCylinderAlgebraExact.agda` and the full marked partition/fine-to-effective-functional equality in `YMClayOriginalWilsonNativeMarkedPushforwardExact.agda`. These use the *same* `Constructed.actualPeriodicProductMeasure` at cutoff 3 as the original E1 cutoff family, not an invented auxiliary rational measure.

New `YMClayE1A3OriginalR445CrossCutoffSourceExact.agda` directly defines:
- `originalFineBlockPullbackCylinder`: a cylinder on the genuine cutoff-dependent original SU(N) links whose n=3 section is `f ∘ actualBlockedLinkMap` for a side-two coarse test `f`;
- `originalBareCoarseCylinder`: the same coarse test on the independently selected original bare Wilson n=1 family, with no demand that its measure match R445;
- `originalR445EffectiveCoarseExpectation`, `originalE1FineBlockedExpectation`, `originalE1BareCoarseExpectation`: three *source-selected* expectations; the first and second coincide by definition, whereas the third is genuinely different;
- `originalE1FineBlockedIsR445EffectiveCoarse`: exact `E_{mu_Wilson,3}[f ∘ B] = (B_* mu_Wilson,3)(f)` on the same true 1024-link Wilson Gibbs density, normalized Haar and beta(3), for every coarse test;
- `originalE1BlockedCoarseWordIsR445`: instantiate this source identity for **all original side-two Wilson plaquette words** (not merely the unit test);
- `originalE1CoarseIsBareWilson`: definitional identification with the separate original n=1 normalized Wilson expectation at beta(1);
- `originalR445UnitEqualsOriginalBareCoarseUnit`: the only unconditional cross-measure consistency presently established: the constant unit test, derived using the original product-Haar ordered/strict normalization and division cancellation at both levels.

This is a substantial upgrade over **fixed-cutoff** prefix projection: it reaches an **actual physical RG block between two differently sized original Wilson lattices**, preserving the full interacting fine Gibbs weight and the exact effective coarse functional. However, the equality of the effective coarse functional to a **bare** coarse Wilson Gibbs state at beta(1) for arbitrary nonconstant observables remains mathematically unproved and is not generally true at finite cutoff without extra effective operators/couplings. The correct continuum target is controlled mismatch for a *renormalized* selected physical cylinder family and its observables, not a spurious exact bare-action equality.

The narrowest next high-alpha leaf is therefore a genuine original RG effective-action/marginal comparison estimate, uniform in continuum physical scaling, or an independently sourced finite-marginal compactness/diagonal subsequence plus selected-measure uniqueness argument. The R566 projective event consistency/continuity at empty requires that producer. D2/B1 R576 physical activity, D2/B2 R577 same-H transfer, N1/H6 R563 and G1 R571 stay independent analytic fronts.

**Verification:** commit and readback of source only; Agda 2.9 kernel receipt remains outstanding, and the transitive `RealAnalysisAxioms`/one-link Haar physical authorities are not discharged by this bridge.


## 2026-11-10 E1/D1 original R445 three-moment maximum cut

New `YMClayE1D1OriginalR445ThreeMomentRGCutExact.agda`, imported by `YMClayOriginalWilsonPhysicalRegression.agda`.

**Recovered rather than reimplemented:** `YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact.originalN3LiteralMixedLogJetIsActualR320PushforwardCovariance` already proves that the selected original fine Wilson two-source formal J11 germ equals the R445 original blocked effective coarse covariance. It uses the actual original side-four Gibbs and native ordered two-link SU(N) map, not a second auxiliary coarse theory.

**New source-native outputs:**
- `sourceEffectiveExpectation`, `sourceBareExpectation` and `sourceCoarseProduct`: original R445 effective coarse vs independent original bare side-two Wilson expectations, selected from the actual E1/R445 owners.
- `sourceEffectiveCovarianceIsActualR445`: definitional identity of R445's true pushed-forward connected covariance with the new selected source expression.
- `sourceBareCovarianceIsOriginalWilson`: definitional identity of independently selected original side-two bare Wilson covariance.
- `originalThreeRGEqualMomentsImplyCovariance`: proof by `cong₂` on the **actual** original real product and subtraction, showing that source moment comparisons on `F`, `G`, `FG` suffice for covariance comparison; no new separate physical covariance premise.
- `originalThreeRGEqualMomentsWeldFineJetToBareCoarseCovariance`: transitive composition with R445/R320's original same-fine-source mixed-log theorem. This gives a complete formal proof that **three real RG moment equalities** imply the original Wilson fine mixed J11 source equals the bare coarse Wilson covariance. The three equalities are explicitly unpaid original RG physical hypotheses—not silently deduced from a naive bare-Wilson closure.
- `coarseOriginalWordTest` and `originalThreeRGWordMomentMatchesWeldFineJet`: specialize the cut to **arbitrary original side-two SU(N) Wilson plaquette-word pairs** rather than unrelated arbitrary independent source test families.

This replaces a possible wrong proof strategy (assume (B_*\mu^W_3=\mu^W_1)) with the exact three-source-moment requirement. The *future quantitative RG theorem* should estimate each of these three **errors** in the physical scale/volume, use ordinary real inequalities to turn the three source estimates into connected covariance control, and propagate through admissible iterated blocking. An exact finite-cutoff equality of effective and bare Wilson moments is not generally expected in interacting lattice gauge theory.

**Verification:** module created and imported; exact source paths/commit readback; no Agda compiler/kernel receipt. The conditional three-moment theorem is a verified-by-source-inspection proof candidate, NOT physical E1 convergence or D1 decay.


### Unconditional same-E1 two-source identity (2026-11-10)

Added `sourceE1FineBlockedCovariance`, `sourceE1FineBlockedCovarianceIsR445`, and `originalFineMixedJ11IsSameE1BlockedCovariance` in `YMClayE1D1OriginalR445ThreeMomentRGCutExact.agda`. Unlike the three-moment *bare* coarse comparison, these declarations require **no RG matching hypotheses**. The already-established source-first original side-four mixed J11 coefficient equals the connected covariance of the **same original cutoff-3 E1 physical Wilson state** with native two-link blocked original coarse observables. The construction uses `Same.originalN3LiteralMixedLogJetIsActualR320PushforwardCovariance` and `Cross.originalE1FineBlockedIsR445EffectiveCoarse` with real-product/subtraction congruence.

This pays the finite *E1-selected covariance source identity*, not the analytic source-J differentiation, physical decay, UV continuum convergence, or a comparison to the independent bare cutoff-1 Wilson measure. The latter still requires actual quantitative moment discrepancies on F, G, and FG or a continuum RG alternative. This prevents inadvertent reuse of a bare-closure assumption in B1/D2.

**All source-written; Agda typecheck and transitive physical authority receipts pending.**


## 2026-11-11 Quantitative three-moment original RG residual (source-written)

New `YMClayE1D1OriginalR445QuantitativeThreeMomentRGCutExact.agda`, imported by `YMClayOriginalWilsonPhysicalRegression.agda`, reuses the CMP116 `BalabanDecoupledActivityHessian.productHeadTelescope`, the existing marked-product `absNonnegative`, and the real-analysis absolute-value/monotonicity axioms. It proves the independent two-factor difference majorant and `threeMomentCovarianceErrorBound` for the **explicit rearranged moment residual**
`(E_eff(FG)-E_bare(FG)) - (E_eff(F)E_eff(G)-E_bare(F)E_bare(G))`.
The concrete same-source `originalR445ThreeMomentResidualBound` instantiates this on the actual R445 effective coarse and independent original bare side-two Wilson expectations.

**Quantitative inequality:** given |Δ(FG)|≤ε_FG, |Δ(F)|≤ε_F, |Δ(G)|≤ε_G, |E_eff(G)|≤M_eff,G, |E_bare(F)|≤M_bare,F, then the absolute explicit three-moment residual is ≤ ε_FG + ε_F M_eff,G + M_bare,F ε_G.

**Important precise distinction:** the subtraction-interchange identity `(a-b)-(c-d) = (a-c)-(b-d)`, needed to rewrite the difference of *connected covariances* into that residual, is not provided as a named theorem in `RealAnalysisAxioms`. Do not treat the current module as a kernel-proven covariance difference bound until that scalar lemma is derived and accepted. The **physical** Wilson RG error bounds ε_F, ε_G, ε_FG and majorants also remain unpaid; the same original Wilson source selection is preserved.

Next true high-alpha target: source-specific CMP109/CMP119 effective-action bounds for the three original coarse Wilson moments with cutoff/volume-uniform physical scaling, then transport via the scalar subtraction-interchange lemma to the same E1 source mixed-J11/CMP116 covariance. The R576 polymer and R577/H6/G1 cuts are unchanged. Agda 2.9 acceptance remains unverified.


### Quantitative downstream covariance and original mixed-J transport

The same module now also source-writes `originalR445CovarianceErrorFromThreeSourceMoments` and `originalMixedJ11MinusBareCovarianceQuantitativeBound`, transporting the three-moment estimate to (1) the genuine difference of original R445 effective and bare coarse covariances, and (2) the already proved original fine Wilson formal mixed J11 coefficient. **Both signatures explicitly request the scalar-ring subtraction-interchange equality** `(a-b)-(c-d) ≡ (a-c)-(b-d)` at the selected six source moments. They do **not** request equality of effective and bare coarse Wilson probability laws.

The next standalone P0 mathematics leaf is therefore to discharge the pure ordered-real scalar interchange once from a coherent selected real ring (or extend `RealAnalysisAxioms` with an independently verified ring theorem, not a Yang–Mills postulate), then supply three nontrivial original Wilson RG physical source moment errors at all relevant scales and volumes. Together those will yield honest quantitative same-source covariance comparison.

**Acceptance limit:** committed source terms and current GitHub readback only. This is a conditional quantitative transport theorem, not a computed physical error bound, E1 continuum existence or D2 mass gap. No kernel/Agda receipt available in the execution environment.


### 2026-11-11: pure scalar interchange discharged from repository axioms

**Correction to the immediately preceding note:** `YMClayOriginalRealSubtractionInterchangeExact.agda` now proves `subtractionInterchange`:
`(a-b)-(c-d) ≡ (a-c)-(b-d)`.
The derivation uses only the existing `subAddCancelMiddle`, `+-comm`, `subAddDistributes`, `subSelf` and `+-identityʳ` laws of `DASHI.Foundations.RealAnalysisAxioms`. There is no new postulate, and the theorem respects the transitive axiomatic nature of the selected real carrier.

The quantitative E1/D1 original Wilson module was then updated to **eliminate the scalarInterchange argument entirely** from:
- `originalR445CovarianceErrorFromThreeSourceMoments`: actual connected covariance difference of native effective R445 pushed-forward vs original bare coarse Wilson sources;
- `originalMixedJ11MinusBareCovarianceQuantitativeBound`: actual original fine Wilson two-source formal J11 vs original bare coarse covariance.

Given original selected-source bounds `|Δ(FG)| ≤ ε_FG`, `|Δ(F)| ≤ ε_F`, `|Δ(G)| ≤ ε_G`, `|E_eff(G)| ≤ M_eff,G`, `|E_bare(F)| ≤ M_bare,F`, with nonnegative error and majorant inputs where needed, their proof-contract bound is
`|Cov_eff(F,G) − Cov_bare(F,G)| ≤ ε_FG + ε_F M_eff,G + M_bare,F ε_G`.
The original finite J11 bound has the same RHS. This is a materially stronger **physical-error-conditional theorem** with no independent covariance, real-scalar interchange or bare-action closure input.

**Unpaid physical highest-alpha leaves (unchanged):** actual nonconstant Wilson RG moment errors on F,G,FG uniformly in physical cutoff/volume, plus the two moment majorants, and iterative renormalized cutoff comparison/compactness. The generic error transport is not source-dependent and cannot prove these inequalities itself.

**Trust/verification:** the new scalar lemma uses a transitive postulated real-ring surface, and the existing marked-factor `absNonnegative` authority; no new postulate. Both new modules are committed and imported by the original Wilson physical regression. No Agda 2.9 executable is installed locally: GitHub readback is NOT kernel acceptance.


## 2026-11-11 — original Wilson *physical numerator* moment-majorant leaf

New theorem module `DASHI/Physics/YangMills/YMClayOriginalWilsonFiniteNumeratorOrderExact.agda`, imported into `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda`, directly consumes the selected n-dependent original SU(N) Wilson Gibbs density, native one-link product Haar and `YMClayOriginalWilsonFiniteTwoSourceJetExact.originalWilsonFiniteIntegrationLaws`. It does **not** create another source measure or independent integration-law record.

Completed source-written declarations:
- `originalWilsonNumeratorCongruent`: same original density, product Haar, denominator-independent numerator integral respects equality of original observables.
- `originalWilsonNumeratorPositive`: for every cutoff n and original pointwise nonnegative test F, the **actual** weighted Wilson insertion numerator is nonnegative.
- `originalWilsonNumeratorAdd`: actual original weighted Wilson numerator is additive, from already-proved selected product-Haar laws.
- `originalWilsonNumeratorMonotoneFromSlack`: if F+S=G pointwise with S≥0, original numerator(F)≤original numerator(G), derived from the existing ordered-real addition monotonicity and native integration positivity; no new order axiom.
- `originalWilsonNumeratorBelowItsPartition`: if original test F has a pointwise nonnegative complement S satisfying F+S=1, its actual weighted insertion numerator is at most the **same cutoff's Wilson partition** Z_n. This is a genuinely selected source majorant, not a rational T5 proxy, and it applies at every periodic cutoff.

**What is paid:** the source-dependent finite numerator positivity/order and partition majorant; if the relevant original Wilson F or G is shown to admit the complement, no new Haar positivity/linearity estimate is needed. **Still unpaid:** a concrete certified uniform [0,1] Wilson test complement for each selected renormalized nonconstant F,G, conversion to normalized moment bounds using the pinned positive-division order, and most importantly actual original RG effective-versus-bare moment errors ε_F, ε_G, ε_FG uniform in physical scaling. The conditional quantitative covariance bound and source mixed J11 transport from the preceding round remain available; no E1 continuum convergence or D2 gap follows.

**Verification:** source-written on PR #1444 and imported in its original physical regression; no local Agda 2.9 compiler. Do not mark as kernel accepted.


### 2026-11-11 independent exact-rational regression

Added `scripts/check_ym_original_three_moment_rg.py`. The same six-moment algebra was run locally under Python `fractions.Fraction` exhaustively on the sixfold grid `{-2,-1,0,1,2}^6`: **15,625/15,625** exact-rational covariance-rearrangement and three-error-bound cases passed, including 125 exact matching-moment cases. An explicit *algebraic* negative control confirms that different moment triples can have different covariances; it is **not** represented as a physical SU(N) Wilson counterexample. This is supplementary algebra regression, not Agda kernel checking or physical RG validation.


## 2026-11-11 P0 original Wilson normalized source majorants and bounded RG cut

A source review found two defects in the earlier `YMClayOriginalWilsonFiniteNumeratorOrderExact.agda`: missing real multiplication import, and the wrong equality orientation in its `lowerNum+0=lowerNum` substitution. Both were repaired before extending the proof.

The same original all-cutoff numerator module now includes:
- `originalWilsonPartitionStrictlyPositive` directly from the original `Family.physicalFinitePartitionPositive`;
- `originalWilsonNormalizedBelowOne`: if the selected original test F has a certified nonnegative complement to 1, then **the original Wilson normalized expectation** at arbitrary cutoff n satisfies E_W,n[F]≤1;
- `originalWilsonNormalizedNonnegative`: pointwise nonnegative original Wilson F gives 0≤E_W,n[F].

These use only the previously sourced product-Haar integration laws and **explicit standard scalar ordered-division premises**: monotonicity of numerator under division by a positive denominator, division of zero, and self-division. They do **not** silently infer quotient order from the currently minimal `RealAnalysisAxioms`.

New `YMClayE1D1OriginalR445BoundedMomentMajorantsExact.agda` uses these directly on the actual physical R445 3→1 block:
- `originalEffectiveMomentAtMostOne` applies original n=3 Wilson source normalization to F∘B using the native ordered SU(N) blocked-link map;
- `originalBareMomentAtMostOne` applies the independent original n=1 Wilson source to F;
- `originalEffectiveMomentAbsoluteAtMostOne` and `originalBareMomentAbsoluteAtMostOne` turn certified [0,1] source moments into |E|≤1, using an explicit standard abs(x)=x for nonnegative real x;
- `originalR445CovarianceBoundForNativeUnitBoundedTests` invokes the previously source-written quantitative R445 covariance theorem with **both one-point majorants set to the actual scalar unit 1**, not additional physical source assumptions. This applies to any original coarse tests with explicit [0,1] certificates and still requires only the three source RG errors on F,G,FG. The RHS is ε_FG+ε_F·1+1·ε_G, with simplification to a three-error sum available from basic ring identities.

**Precise unpaid P0:** actual cutoff/volume-uniform physical source RG moment discrepancy estimates ε_F, ε_G, ε_FG on a concrete chosen renormalized interacting Wilson cylinder family; certifying bounded/coarse complements on the selected (possibly rescaled/shifted) observable class; identifying physical blocking with the E1 limit. R576 mixed-log shell activity, R577 same-OS transfer, R563 H6 noncollapse and R571 G1 physical group continuation remain unpaid.

**Verification:** source-written/committed and imported into original physical regression, not Agda-kernel-accepted. No CI-based acceptance inferred.


## 2026-11-11 original RG finite-source continuation

The bounded-moment module constructs an explicit product-complement test: given F+Fc=1 and G+Gc=1 with nonnegative summands, the complementary test Fc+F*Gc satisfies FG+(Fc+F*Gc)=1. Source-written proofs establish pointwise positivity and unit completion, and reuse actual R445 and bare Wilson normalized moments to show both product expectations have magnitude at most one. This extends the certified bounded test class to all three RG moment inputs F, G, FG.

New `YMClayE1A3OriginalR445WeightedCrossNumeratorExact.agda` defines the actual original Wilson effective fine-block numerator N_eff(F), independent bare coarse numerator N_bare(F), and their respective source partition functions Z_fine, Z_bare. It constructs X(F)=N_eff(F)*Z_bare-N_bare(F)*Z_fine and proves its literal interacting Haar/Gibbs expansion plus unit-test cancellation X(1)=0. Nonconstant physical RG errors remain unresolved: no matching of effective and bare Wilson actions is asserted.

Agda kernel verification has not been performed. Remaining highest-alpha physical target: a uniform nonconstant original Wilson weighted cross-numerator bound, followed by positive-denominator normalization and existing three-moment covariance transport. R576/R577/R563/R571 physical gates remain open.


## 2026-11-11 P0.01–04 original bare centering admission

New `YMClayE1D1CrossNumeratorCenteringAlgebraExact.agda` is imported into the original Wilson physical regression root. Source-written targets `originalRealSubtractionAsAddition`, `originalWilsonCrossNumeratorSubtractionCenteringClosed`, `originalBareExpectationMultiplyPartition`, and `originalBareCenteredNumeratorZero` now compose the actual n=1 Wilson bare partition and normalized expectation with the existing n=3-to-n=1 original cross-numerator shift identity. Critically this is **conditional algebra**: `OriginalRealCenteringLaws` (subtraction-via-negation and centered additive cancellation) and `OriginalRealPositiveDivisionLaws` (positive denominator quotient reconstruction) must be instantiated by an actual coherent real field backend; the minimal `RealAnalysisAxioms` does not make those implications available. The existing Wilson partition strict positivity is reused as an actual source theorem, not an extra assumed positive constant. No new postulate was inserted.

Next exact tasks: first instantiate the selected scalar-field law interfaces with an actual real carrier; then P0.05 `originalWilsonCrossNumeratorIsFineCenteredInsertion`, P0.06 source-native SU(N) plaquette trace range/affine boundedness, P0.07 literal plaquette one-sided formula, and kernel check. Physical P0.09 remains the uniform nonconstant RG cross-numerator estimate; finite cancellation alone is not that estimate.


## 2026-11-11 P0.05 and P0.07 original-source centered fine insertion

At PR #1444, `YMClayE1D1CrossNumeratorCenteringAlgebraExact.agda` now source-writes:
- `originalWilsonCrossNumeratorIsFineCenteredInsertion` (P0.05), composing the previously written genuine original R445 scalar-shift identity and the original bare n=1 Wilson centered-numerator cancellation, then using only `mulZeroˡ`, the **explicit** selected scalar `subtractionZeroRight` and `*-comm`: `X(F) = Z_b * N_f(F - E_b(F))` on the actual same-source fine and bare Wilson measures;
- `originalPlaquetteCrossNumeratorIsCenteredFineInsertion` (P0.07), instantiating P0.05 at the literal `Center.originalCoarsePlaquetteTrace p`, defined from `Words.originalWordObservable ... 1 (p :: [])`.

The selected `OriginalRealCenteringLaws` now additionally requests the standard `x - 0 = x` law. This is **not** a new postulate, and is not internally supplied by the existing minimal `RealAnalysisAxioms`. Thus P0.05/07 are source-written **conditional theorems** under the explicit real-field and positive-division authorities; no unconditional real-field instance has been constructed or Agda-kernel accepted.

**P0.06 precise gate:** `YMClaySUNMatrixWilsonTraceGaugeExact.SUNMatrixRealTrace` provides `normalizedRealTrace` and `traceCyclic` only. `SUNMatrixCarrier.CertifiedSUNMatrixTheory` provides abstract matrix product/dagger/SU(N) group laws, but not finite complex inner-product inequalities or a trace norm estimate. Therefore `|Tr_norm U| <= 1` for *arbitrary selected abstract matrix SU(N)* is not derivable from the currently exposed trace signature. A physical source proof must instantiate an actual concrete finite matrix and normalized trace and prove its bound; the rational SU(2) quaternion trace inequality is not itself such an SU(N) source proof. Pointwise [0,1] test normalization for the selected real Wilson plaquette must then be constructed from these bounds and coherent scalar division. The centered **identity** needs none of those inequalities; the physical contraction bound does.

**Next highest-alpha gate:** (a) instantiate the scalar ordered field compatibility laws with a real backend; (b) typecheck full original-Wilson regression on Agda 2.9; (c) prove concrete matrix SU(N) trace bound; (d) original nonconstant scale-uniform Wilson RG blocked-to-coarse effective-action/polymer fluctuation bound `abs X(F_p) <= epsilon_p * Z_f Z_b`. Full E1/D1/D2/N1/G1 remain OPEN. No RG rate inferred from centering.
