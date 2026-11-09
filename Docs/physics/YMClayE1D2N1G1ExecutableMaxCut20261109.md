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
