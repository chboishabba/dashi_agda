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
