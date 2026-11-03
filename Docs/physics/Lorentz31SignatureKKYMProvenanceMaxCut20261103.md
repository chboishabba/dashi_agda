## 2026-11-03 complete theorem roadmap / lemma ledger

The [canonical new P00–P11 cross-lane roadmap](../roadmaps/Emergent31QuantumYMKKExactLemmaRoadmap20261103.md) enumerates **176 exact lemmas** with phase deliverables, original-source owners, real physical dependencies, negative tests, and criteria for kernel versus physical completion. P07 (same observed clock = OS Hamiltonian on the same metric and quantum state) is the key new cross-domain theorem. P05/P06 remain the independent pure 4D YM Clay route, and P08 spacelike 5D KK remains an optional EFT for Clay but necessary for the proposed five-sector consistency theory. Current #1460 does not yet contain latest #1444 variable-periodic Haar files; a source-controlled merge/rebase and typecheck are explicitly required.

## New five-sector BIDI steelman and exotic-gravity source map (3 Nov 2026)

[Full physical hypothesis / exact lemma cut](YMClayFiveSectorBidiSteelman20261103.md); new `YMClayFiveSectorBidiSteelmanExact.agda` and independent `scripts/check_ym_five_sector_bidi_steelman.py` on #1460. The key **constructed finite** theorem is `P_d=P_(d-1)+cross_d` plus `P_d=P_(d-1) => cross_d=0` on nonnegative (Nat) curvature-weight sums, including an explicit nonzero 5D fibre which 4D projection misses. Its observable-tower theorem transports only **selected matched** observables, not arbitrary different-dimensional theories. `selectedLorentzian31FromSameMetric` reuses the existing TSFV/KK physical conditional theorem. No arbitrary 5D Euclidean SU2 phase dynamics is identified with KK gravity.

**Exotic gravity archaeology:** #1120 Local-C/Wightman native typed physical stress to single normalized metric, four-channel same-state weight/free-fall/clock/optics; #1132 quantum birthmark/history/entropy (Eq2.23 source signs required, no direct entropy->curvature); #1045 counterfactual negative-G versus positive-G fingerprints and explicit material-effective/universal scope separation; #1284 TOE nonpromotion for negative trace, missing active stress, incomplete metric source, and absent empirical result; #1241 KK selected action/radion source. The strongest joint candidate keeps `G_N>0` and derives any repulsive geometry from selected stress/energy conditions and conservation on one metric, not an unverified universal `G<0` law. No imported unmerged branch is represented as merged code.

**Additional exact finite obstruction:** `globalStrictReversalRankImpossible` in the same Golden module proves that no Nat-valued rank can strictly decrease under **the original history-reversal involution on every history**: the explicit `(stateZero,stateZero)` history is fixed by reversal, making strict descent irreflexive. This is a useful no-go for conflating reversal with collapse evolution; it does **not** prohibit coarse-grained, filtered or boundary-selected directional dynamics. Agda exact-head check remains pending.

## 2026-11-03 — actual same-metric TSFV → KK/YM transport (source-written)

New Golden Agda adapter: `DASHI/Physics/Foundations/TSFVKKSameMetricTransportExact.agda`.
It **reuses** `TSFVFiltrationArrowLorentzBridgeExact.SelectedTSFVToLorentzPhysicalSource` and `YMClayLorentz31DirectionalKKHodgeExact.SameSourceKKYMContinuation`, rather than defining another signature model.

The key `SameMetricTSFVKK` weld requires:
1. An explicit map from the **selected reduced KK 4D metric** to the **physical state used by the original two-boundary filtration**.
2. Equality of that mapped selected metric-state with the **selected TSFV physical state**.
3. For each of the **four** actual axes, equality of **KK/YM metric signs** with the **TSFV-selected physical quadratic signs** evaluated at that mapped metric-state.

From those requirements and the previously proved TSFV finite conditional sign certificate, `sameMetricKKSignatureFromTSFV` proves that the **KK/YM selected metric** has the *same* `signature 3 1`. `sameMetricKKReversedCountExcluded` then proves that the same selected orientation does not have the 1+3 count. This is a nontrivial **same-metric commuting-sign transport**, **not** evidence that the physical weld record is presently inhabited. The Agda source is written; exact-head kernel acceptance is **not verified**.

### Existing UV and Clay max-cut — no loss of ownership

- `BalabanClayGate4CombinedRGUVIterationExact` owns conditional physical one-step RG norm inequalities, all-scale admissibility and UV stability induction. Its `combinedOneStepAnalyticInputsLevel` and `initialUVStabilityInputsLevel` explicitly remain `conditional`. The verified algebraic induction must not be confused with constructing physical ultraviolet measure limits.
- `BalabanClayConcreteUVToMassGapDependencyExact` owns the separate **UV → selected continuum OS axioms → reconstructed Hilbert theory → spectral gap → physical mass interlacing** dependency. Its `continuumFromAllScaleUV`, `clusteredOSReconstructionHasGap`, and `physicalInterlacingFromGap` fields are mathematical *inputs*, not instantiated conclusions.
- This TSFV/KK seam is placed **beside** the selected four-dimensional R443/R445/R320/R333 original YM physical chain. The Agda Golden-safe import does not import the separate older UV modules because their current modules lack `--safe`. Do not mark the UV pathway kernel-checked by inheritance.
- The current `#1444` stack supplies real finite SU(N) plaquette/Wilson/Gibbs/C3 constructions; actual compact continuous Haar, changing-cutoff R445 bounds, selected R320, same-`H_OS` R333, and the Clay compact-simple-group quantification remain explicit blockers. This adapter neither cures nor bypasses them.
- The finite `ShiftCollapseChainMDLCompatibility` carries genuine ordered descent **on its own shift carrier**, whereas `FiniteHistoryOrientationExact` carries original reversible-history/no-past-reconstruction. A physical identity between these two separate state/dynamics carriers is still required. Simply pairing their receipts would not prove that collapse potential, coarse history MDL, and YM RG running refer to the same energy, entropy or physical time.

### Exact next lemmas

1. `tsfvShiftSameState`: construct an actual dynamics/observation map from the shift pressure-chain state to the original finite microhistory, preserving transitions, filtered observations and monotone-depth/MDL witnesses. Reject unmatched carriers.
2. `tsfvObserverToMetric`: construct `SameMetricTSFVKK` from actual measured history/physical quadratic and the KK-reduced metric; establish each of its state and four sign equalities without a preselected mask.
3. `kkReducedMetricFromSelectedAction`: source native #1241 compactified action/metric, prove dimensional reduction and physical stress agreement, and provide a **physical inhabitant** of the existing KK continuation.
4. `ymSelectedUVToOSSameMetric`: establish actual selected 4D Wilson/Gibbs/Haar/continuum Schwinger family with R443/R445 changing-cutoff estimates, a compatible OS reconstruction, and that reconstructed Lorentz metric agrees with the same selected 4D KK/TSFV metric. This entails the independent selected R320 and same-`H_OS` R333 gap producers; importing the conditional UV dependency alone does not discharge them.

Attribution: Original TSVF (Aharonov–Bergmann–Lebowitz, Aharonov–Vaidman), original DASHI history/shift and Lorentz proof owners, Bałaban's RG work, Osterwalder–Schrader reconstruction, and historical Lorentz/Hodge/KK geometry remain separately credited. New DASHI content is only the selected same-metric transport and audit.

---

# Lorentz (3,1): directional certification, Yang–Mills and KK — 3 November 2026

## Result and scope

The original multi-repository DASHI programme is substantially more than the unsigned orbit-shell profile. It includes finite oriented-signature proofs, numerical cone/arrow tests, robust signature screens, contraction-to-quadratic interfaces, causal geometry, B4/Weyl comparisons, and a selected GR-QFT/KK physical recovery programme.

This PR adds two *safe source-written finite theorem modules*. It does not claim independently derived real-world 3+1 spacetime or a physical quantum/gravity theory.

## Explicit source archaeology and attribution

Search terms checked against current Agda master and active PRs include: Lorentz, signature, sig13, oneMinus, arrow, orientationTag, 3+1, 3,1, timelike, causal, ConeArrow, OrbitProfile, B4, dimension, Hodge, Wick, OS, KK, Kaluza, radion, R443, R445, Voyager, YM video, Clifford and GRQFT. Sibling dashifine, dashitest, DASHIg and dashiQ documents and relevant code were inspected.

- Original empirical and computational owner: dashifine, especially 26_dashi_signature_elim.py, 26_dimension_bound_search.py, 30_delta_cone_signature_diagnose.py, 31_try_both_delta_cone.py, 33_scale_robustness.py, 38_signature_stability.py, 40_generate_orbit_profiles.py, COMPACTIFIED_CONTEXT.md and HEPData dossier. Its best three-coordinate HEPData mask passes 59/60 selected forward cone steps; that is not an independently measured four-dimensional physical metric.
- DASHIg/FORMALISM_OUTLINE.md explicitly proposes contraction -> quadratic -> causal cone -> arrow/isotropy -> Lorentz uniqueness.
- dashiQ/PHYSICS_TARGETS.md proposes emergent 3+1 as a testable physical hypothesis, while QUANTUM_BRIDGE_INTERFACE.md and computer_v2.py define quantum state/evolution/measurement carriers. dashitest retains related testing/quantum-simulation surfaces; no independently complete signature theorem was found in the searched default branch.
- Existing Agda proof owner from merged PR #70: DASHI.Algebra.Quantum.LorentzSignatureUniqueness, which proves uniqueness of a (d,1) sign assignment **given** distinguished time arrow and spatial isotropy. Reuse it: do not reattribute.
- Existing Agda PR #167: quadratic/polarisation, projection defect and Delta-to-quadratic bridge. Existing orbit owners: OrbitProfileComputedSignedPerm, Signature31ShiftProfileWitness, ConeArrowIsotropyShiftOrbitEnumeration, OrbitSignatureDiscriminant. Existing Weyl comparison owners: RootSystemB4OrbitQuotientTheorem and PhysicsClosureRealizationIndependenceTheorem.
- Actual earlier numerical work explicitly treats the reversal (3,1) versus (1,3) using an arrow/orientation requirement, not unsigned orbit counts alone. The **specific** master Agda OrbitSignatureDiscriminant nevertheless puts the signature-derived label 31 in the profile, and Signature31InstanceShiftZ fixes dimension four and returns 31 in its orientation bridge. These implementations do not themselves independently derive physical 3+1 from signature-neutral dynamics.
- GlobalDimensionUniqueness.targetUniqueDimension remains a required proof field. Quadric Q-hat-core is a positive sum of squares; an independent theorem is required to derive/identify the genuine physical indefinite form.
- YM PR #1444 owns the Voyager chapter audit, real selected C3/Wilson source proofs, YMClayVoyagerDimensionSignatureForkExact and YMClayVoyagerR4HodgeBasisExact. KK PR #1241 owns the competing smooth-circle versus chiral-orbifold source actions, 5D metric, radion, matter, anomaly and physical source constraints. TOE PR #1217 owns the proposed canonical 369/GR-QFT assembly. PRs #1241, #1444 and #1217 are distinct unmerged source heads.

## New exact Golden Agda surfaces

1. DASHI.Physics.Foundations.Lorentz31DirectionalProbeExact: a **label-free** four-axis Boolean cone/arrow probe with four possible distinguished axes; explicit calibration to actual quadratic principal-axis signs; exact proof that any such calibrated case has 3 spatial and 1 temporal principal axes; exact incompatibility with the reversed 1 spatial and 3 temporal counts. This does not rely on the old signature-coded profile or preselect a particular axis. RealizedDynamics is a **non-inhabited input record** requiring a genuine selected physical state and its observation/sign calibration. The theorem is conditional; the input is not yet supplied by the historical experiments.
2. DASHI.Physics.YangMills.YMClayLorentz31DirectionalKKHodgeExact: uses the *actual existing* Voyager Euclidean signed two-form basis. It proves a parallel finite Lorentzian Hodge star square equals minus identity for all signed basis cases and distinguishes it from the established Euclidean plus-identity square. Reuses Voyager's 5D Creutz-versus-KK separation. A typed SameSourceKKYMContinuation requires the same KK-reduced 4D physical metric, directional calibration, actual OS continuation, source stresses and equal physical metric variation. No inhabitant is fabricated.
3. DASHI.Unified.BalabanRGTOERegression imports/re-exports the new finite theorem names. This connects the result to the live YM #1444 regression spine without pretending that the distinct open KK #1241 is already merged.

## Exact next proof obligations (max-cut)

SIG-0: From the actual original dynamics, prove an independent cone/arrow probe on four physical principal directions, with one distinguished temporal direction. Transport empirical evidence, uncertainty and gauge/coordinate robustness. Do not assume a single arrow by merely constructing a DirectionalProbe record.

SIG-1: Derive a **nondegenerate indefinite physical quadratic** from the selected actual operator/Delta dynamics. Prove it is the one used by the cone and the principal-axis observation, rather than identifying it with positive Q-hat-core via nomenclature. Reuse #167 and the explicit actual-shift/projection-defect comparison seam.

SIG-2: Prove dimension four from intrinsic constraints independently of the chosen finite 4-vector, and close GlobalDimensionUniqueness.targetUniqueDimension over arbitrary dimensions and competing realizations.

SIG-3: Weld actual physical arrow data to the new label-free discriminator; exclude alternative signatures on the **same** observable source without importing a 31-coded tag. This formalises the distinction claimed by the historical orientation experiments, while preserving physical calibration requirements.

SIG-4: Recover Lorentzian 3+1 fields from the **same selected Euclidean 4D YM** continuum OS measure, not from mere equality of lattice dimensions. The Euclidean versus Lorentz Hodge-square difference blocks treating the two geometries as definitionally identical. Retain R443 compact continuous Haar and R445 physical continuum expectations, R320 decay, R333 same H_OS and positive gap as distinct analytical requirements.

SIG-5: Reuse **KK #1241** selected action: prove 5D to 4D reduction with the same metric, stress variation, radion, gauge and anomaly-correct matter; identify its 4D target with SIG-3 and SIG-4 rather than gluing unrelated smooth-S1 and orbifold models. Actual full quantised GS/WZ/CS, selected physical source and experiment remain open.

SIG-6: Exact-head Agda kernel acceptance under --safe, zero postulates, zero holes, no TERMINATING pragmas; redo orbitSizes structural termination in OrbitProfileComputedSignedPerm before promoting it as a Golden dependency. Preserve existing owner attribution, do not infer that source-written means compiled.

## Attribution / publication firewall

Classical prior authors retain credit: Lorentz and Minkowski, Sylvester's law of inertia, Hodge, Malament and causal reconstruction, Kaluza and Klein, Wilson, Osterwalder-Schrader, Bałaban, and the original YM/video sources named in PR #1444. Prior DASHI/dashifine developers retain authorship for existing proof/code. This tranche independently owns only the bounded finite directional/Hodge proofs and typed source bridges.

An external published theorem, a numerical scan, an independent finite model, source-written Agda, kernel acceptance, and a physically selected continuum unification theorem have separate evidentiary statuses.


## Recovered TSFV/TSVF arrow-of-time donor (3 November source audit)

The original user's direction was correct: the previous 3+1 review missed the mature two-boundary and history-filtration work. Explicit term searches included TSVF, TSFV, TwoStateVector, postselection, temporal arrow, bidirectional admissibility, HistoryWeightFiltration, reversal and future-conditioned smoothing. Core sources:

- **Original science attribution:** Yakir Aharonov, Peter Bergmann and Joel Lebowitz, *Time Symmetry in the Quantum Process of Measurement*, Phys. Rev. 134 (1964), B1410, DOI 10.1103/PhysRev.134.B1410; later Aharonov and Vaidman TSVF. These are NOT original DASHI mathematical findings.
- **DASHI PR #84 merged:** DASHI/Quantum/TSVF.agda; DASHI/Foundations/TwoBoundarySystem.agda; DASHI/Foundations/DiachronicTwoBoundaryBridge.agda; TSVFTests. Both forward ket and backward bra plus involutive reversal are formalized as abstract parameterised surfaces. The toy test is explicitly not a physical Hilbert model.
- **DASHI PR #621 merged:** DASHI/Physics/Foundations/BidirectionallyAdmissibleHistoryFibreExact.agda; FiniteHistoryFunctionalExact.agda; HistoryWeightFiltrationExact.agda; TSFVNonseparableTransitionKernelExact.agda; TSFVBidirectionalCausticBridgeExact.agda; TSFVActionPhaseWeightSeparationExact.agda; TSFVFeynmanDerivationObligationsExact.agda; TSFVBidirectionalActionRealizationObligationExact.agda. Exact finite bidirectional histories, nonseparable structural kernel, T-invariance and nonfactorability exist. The physical action, calibrated Feynman phase and justified same-history-carrier realization do NOT.
- **Original operational asymmetry in HistoryWeightFiltrationExact:** early filtration cannot access terminal event, final filtration can access terminal event; future boundary changes a smoothing estimate but not a past intervention; a finite synthetic witness increases both entropy and description length, disproving automatic identification of entropy increase with MDL decrease.
- **Added source-written consumer:** DASHI/Physics/Foundations/TSFVFiltrationArrowLorentzBridgeExact.agda imports that exact original filtration owner. It derives the early/late information-access inequality by finite contradiction, preserves the future-conditioned smoothing distinction, and uses a *separate uninhabited record* SelectedTSFVToLorentzPhysicalSource requiring the actual selected physical state, measured unique axis, observer information source-to-metric-axis relation and physical quadratic calibration. The conditional (3,1) conclusion consumes the existing tag-free direction theorem, not a manually manufactured profile label.

**Central distinction:** The pre/post-selected two-boundary formalism is microscopically time-symmetric. The existing history-filtration theorem produces a genuine *observer/operational information asymmetry*, which is promising input to the earlier physical-arrow programme. Neither on its own proves that this asymmetry uniquely identifies a timelike eigen-direction of an independently derived metric; identifying those objects on the same physical state and with actual dynamical source evidence is the exact remaining TSFV→Lorentz lemma.

**Trust boundary:** The new Agda surface is SOURCE-WRITTEN, uncompiled. Its transitive --safe dependencies have not been independently audited. Do not count an Agda module header as an exact-head compiler receipt. No backwards-in-time signalling, universal Lorentz selection, physical KK metric or Yang–Mills mass gap is claimed.


## 3 November 2026 deeper full-concept time-arrow archaeology

Search deliberately expanded **beyond TSVF/TSFV filenames** to reversible microscopic action, history reversal, entropy, filtration, future boundary, postselection, causal order, observation-quotient, MDL, Lyapunov, collapse depth, signed cone and coarse-graining. The strongest relevant original in-repo owners, not new imports:

1. **FiniteHistoryOrientationExact** (origin Round Five PR #401 source; closed, *unmerged* PR history but file present on master): `internalConjugationInvolutive`, `reverseHistoryInvolutive`, `actionTimeReversalInvariant`, `finiteNoBackwardSignalling`, `futureBoundaryCanChangeHiddenHistory`. This is a source-owned **same-carrier** finite model of time-reversal-invariant action and future-conditioned hidden-history distinction. Repeated action counts do not select the hidden history.
2. **HistoryWeightFiltrationExact** (PR #621 TSFV tranche): initial filtration excludes terminal event while terminal filtration includes it; smoothing can depend on future boundary; a synthetic two-step entropy witness increases entropy **and** MDL, deliberately blocking their unearned identification.
3. **ShiftCollapseChainMDLCompatibility** (merged PR #47): on the actual selected finite shift, depth/potential decrease 2→1→0; Lyapunov and MDL receipts exist on the separately defined execution-side carrier. The source states explicitly that no global depth=potential=MDL identification, thermodynamic entropy or physical arrow-of-time law follows.
4. **DynamicsCollapseDepthMonotone**: generic monotonicity and strict-off-held witnesses are fields of a record; the finite shift instance supplies an example, but no independent physical thermodynamic law.
5. **DeltaConeMDLContract**: source-target step relation with arrow-monotone, cone membership, MDL descent and basin preservation; arrow is an **input function**, not produced by entropy.
6. **CPTContract**: distinction between reversible and dissipative sectors; `CPTObstructionByMDL` presently returns the trivially inhabited type `⊤`, so must NOT be promoted as a rigorous global CPT impossibility theorem.
7. **FiniteHistoryFunctionalExact**, **BidirectionallyAdmissibleHistoryFibreExact**, **TSFVBidirectionalCausticBridgeExact**, **TSFVNonseparableTransitionKernelExact** and **TSFVFeynmanDerivationObligationsExact**: exact finite history/action/projection/transition invariants; no physical history-to-action identification or calibrated S/ℏ, continuum propagator or physical signature.
8. **CausalRelationalMetricSelector**: has an explicitly supplied `canonicalAxisRole` with a timelike axis; this is a *selected* metric model, not an independent generation of time from an observer asymmetry. **CausalOrderLorentzClosure** likewise declares dimension-three/one witnesses in a required record.
9. **PostEntropyUniversalityTheorem**: the theorem is packaging of a supplied `attractorWitness`, not a physical entropy-driven universe theorem.
10. **QuantumClockSuperpositionReceipt**: branches carry proper-time observable labels; no literal splitting of time or Lorentzian spacetime theorem.

**Strengthening in this branch:** `TSFVFiltrationArrowLorentzBridgeExact` now **directly imports** original `FiniteHistoryOrientationExact` rather than just the generic TSVF type. Reuses the actual source proofs of full microscopic history reversal and action invariance, two later conditions with the same recorded past but distinct hidden histories; proves additionally `futureChoicesHaveSameMicroscopicAction` and `historyNotRecoverableFromActionAlone`. This is a finite information-theoretic no-decoder statement on the same history carrier and no new physics. The original module is changed only by a `--safe` header, with original source attribution retained. `BalabanRGTOERegression` reexports these selected finite results.

**Remaining SAME-OBJECT seam:** The physical state underlying the selected TSFV two-boundary history, observational filtration and physical quadratic must be *one actual physical carrier* with a proof that the measured irreversible/distinguished arrow is the unique timelike eigendirection of that physical metric. This requires a dynamics/source theorem; selecting a history ordering or writing a `(3,1)` tag does not prove that implication. The history-action symmetry and observer filtration counterexample do not themselves produce the arrow from symmetric laws: directional boundary conditions and accessible-observable filtration are still part of the selected finite setup.

## Yang–Mills dimension firewall and primary source distinctions

- **2D pure SU(N)** continuum YM admits rigorous exact Wilson-loop constructions (e.g. Ashtekar–Lewandowski–Marolf–Mourão–Thiemann 1997, *J. Math. Phys.* 38, 5453); does not imply 4D YM.
- **3D** stochastic Yang–Mills–Higgs local-time dynamics has rigorous results (Chandra–Chevyrev–Hairer–Shen); global invariant measure / complete nontrivial quantum 3D reconstruction remains distinct.
- **4D Euclidean pure nonabelian YM** is the Clay problem, corresponding *after OS reconstruction* to a 3+1 Lorentzian quantum theory. Known 4D Euclidean finite lattice, classical instanton/ASD sectors and numerical evidence do **not** prove the required continuum OS/Wightman theory and spectral gap. See Clay and Douglas, *Nature Reviews Physics* (2026).
- **5D Euclidean pure SU2 lattice** has the Creutz 1979 Monte Carlo phase-transition study (DOI 10.1103/PhysRevLett.43.553); no general 5D continuum existence+gap result follows. **KK 4+S1** has an additional dynamical compact coordinate and metric, and is not Creutz's five equivalent Euclidean lattice axes.
- Standard dimensional engineering: [g_d]=(4-d)/2; d=2 has +1, d=3 +1/2, d=4 0, d=5 -1/2. Thus 5D has a worse naive ultraviolet nonrenormalizability problem; its lattice phase transition is not proof of a UV completion.
- Proof of 3+1 physical signature is mathematically independent of (and not sufficient for) full quantum YM 4D mass gap. The conventional Clay construction may reconstruct Lorentzian time from a suitable Euclidean OS theory without a *new derivation of spacetime dimension* from an independent foundational dynamical operator.

**Validation boundary:** Newly modified sources are GitHub source-written, not typechecked by Agda in this session. Independent Python enumeration checked the nine two-step microhistories, symmetry and the equal-action/different-history witness; it is not a compiler receipt. No CI claim.


## Direct sibling-repo conceptual origin: lossy inference arrow and independent cone screen

A final term-specific search against dashifine, dashitest, dashiQ and DASHIg checked "arrow of time", "time reversal", "entropy", "coarse-graining", "postselection" and "boundary". The strongest source is **dashiQ/PHYSICS_TARGETS.md, section "What is time, really?"**: it explicitly hypothesizes reversible microscopic dynamics plus lossy projection/coarse observation and MDL-selected narratives as the mechanism for an *operational* arrow. It proposes testing causal asymmetry versus valuation depth. This is a **prior user research hypothesis**, not a theorem proved by dashiQ, and should be cited as its origin rather than reattributed to the present branch. DASHIg/FORMALISM_OUTLINE.md gives the complementary contraction/project/canonicalization programme.

The strongest empirical bridge is **dashifine/29_delta_cone_signature_test.py** and **31_try_both_delta_cone.py**, which intentionally use an *arrow column only to select forward steps* and exclude it from the quadratic `Q(Δx)` calculation, avoiding a trivial same-coordinate quadratic fit. `33_scale_robustness.py` explicitly tests alternative forward-selection modes, including strict ranking and MDL-direction selection. dashifine/COMPACTIFIED_CONTEXT.md reports arrow/shape Pearson r ≈ -9.76e-4 and Spearman r ≈ -0.1008, plus complement/reversed-edge/bidirectional trials; these are **stored experimental observations**, not a statistical proof of independence nor a physical metric. The 3D cone tests and cone scale interval still require a physically justified four-dimensional carrier and observer calibration to establish physical 3+1. Many scripts already test the exact direction dependence; do not rebuild a duplicate scanner before reuse.

The nested path `dashitest/dashifine/TODO.md` referred to in a user's local checkout is **not present at that path on the fetched default GitHub branch** of the separate dashitest repository. Do not infer that the user's local checkout lacks it; the sibling material may be a local directory copy/submodule/working tree not represented by the default remote index.

**Further new proof expression, source-written in this PR:** `pastRecordCannotRecoverSelectedMicroHistory` rules out a deterministic reconstruction of the selected hidden history from the *same coarse past record*, because both future-boundary choices yield the same past observation yet unequal hidden histories. This is a mathematically direct finite realization of the original dashiQ lossy-projection conjecture. Together with original source time-reversal invariance and no-backwards signalling, it supplies the strongest single-carrier bounded arrow package presently identified. It does not supply an entropy-production theorem, universal low-entropy boundary selection, 4D physical metric, or new experiment validation.
