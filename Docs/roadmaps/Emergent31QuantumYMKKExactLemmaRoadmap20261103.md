# Emergent (3,1) → quantum mechanics → Yang–Mills → KK: exact-lemma roadmap

**Canonical 3 November 2026 cross-lane roadmap. Status: ACTIVE and predominantly OPEN.** This is the proof plan for the deliberately speculative [actual steelman](../physics/Emergent31HistoryQuantumYMKKSpeculativeSteelman20261103.md), not a claim that the theory is true. Preserve the original [Clay YM roadmap](ClayYMProofRoadmap.md), [core physics theorem roadmap](CorePhysicsTheoremRoadmap.md) and [complete physics unification roadmap](CompleteVerifiedPhysicsUnificationRoadmap.md) as distinct owner inventories.

## 1. Completion target and correct proof semantics

**Proposed terminal theorem:** a single selected microscopic history/observer system yields (a) a measured causal continuum with independently derived four dimensions and one time orientation; (b) a positive complex Hilbert quantum representation with one strongly continuous unitary time evolution; (c) the selected local gauge source and independently complete pure four-dimensional non-Abelian YM theory; (d) a reflection-positive Euclidean YM continuum whose OS physical Hilbert space and self-adjoint Hamiltonian are **unitarily identified** with the observed Lorentzian (3,1) quantum clock; (e) a strictly positive gauge-invariant spectral gap in the continuum and infinite-volume pure YM theory; and (f) optional but, for the five-sector steelman, mandatory consistent physical 5D spacelike KK extension, rigorous selected 2D/3D backward observable comparisons and single-source gravity/stress.

**Central same-object requirement:** physical clock state, causal metric, selected gauge field and Wilson source, Schwinger/OS state, Hamiltonian and KK-reduced metric must agree under explicit source-indexed maps. Model equality means unitary/observable/metric equivalence at **matched couplings, fields, boundary conditions, gauge group, units, limit order and physical sector**, not identical dynamics in different dimensions. Else provide a proved approximation bound or an explicit incompatibility.

**Evidence codes:** OWNED = actual existing theorem owner; SOURCE = Agda proof term written but not exact-head compiled; COND = theorem accepts missing physical certificates; TEST = independent finite numerical check; OPEN = selected physical premise unproved; KERNEL = exact-head Golden Agda acceptance including transitive no-postulate audit; PHYSICAL = same-source limit genuinely constructed and the required physical hypotheses inhabited; EXTERNAL = appropriately attributed scientific result at its original scope.

**Golden rule:** safe Agda, 0 postulates, 0 unsolved metas, 0 termination bypasses in the full proof cone; Lean downstream. No fake Bool gate, synthetic numerical fixture, uninhabited Set, assumed source equality or conditional theorem may be promoted as full physics. Record every exact lemma with its actual owner, source SHA, type signature, assumptions, numerical/negative controls, kernel acceptance and selected physical population. The inventory below is exhaustive **relative to the proposed theorem specification**; new hard-analytic sublemmas discovered during proof must be added explicitly rather than pretended away.

**Verified branch blocker:** latest #1444 at head 5bb34d44bac92dfe16544fcde07c65e37d875172 has YMClaySUNVariablePeriodicProductHaarExact.agda and YMClaySUNVariablePeriodicGaugeHaarExact.agda. Both were found on its research/ym-voyager2026-completeness-crosswalk-20261101 branch but NOT on #1460 research/lorentz31-directional-kk-ym-20261103. A reviewed integration/rebase is required before importing them into #1460. Route-S #1440 is upstream; KK #1241, exotic gravity #1120/#1132/#1045/#1284 are separate donor branches unless merged with receipts.

## 2. Dependency graph, deliverables and proof cuts

Phase DAG:

- **P00** owner/branch reconciliation → P01 history and P02 causal geometry + P03 quantum representation.
- P03 → **P04** actual quantum gauge source → **P05** physical finite R443 Haar/Wilson → **P06** R445/R320/R333 full constructive YM.
- P01 + P02 + P03 + P06 → **P07** same-clock/same-metric OS–Lorentz theorem. This is the decisive (3,1) bridge.
- P02 + P04 → **P08** genuine 5D KK action/metric/holonomy/decoupling.
- P05 + P08 → **P09** independently checked 4D→3D→2D observables.
- P07 + P08 → **P10** same-effective-action quantum stress/GR/exotic discriminators.
- All → **P11** global BIDI limits, independent tests, referee receipt and terminal theorem.

**Shortest immediate Pareto max-cut:** P00 branch integration/compiler; P02 physical dimension/causal principal symbol; P03 physical selected one-clock Hilbert; P05 *real* SU(N) compact one-link Haar plus native bond codec; P06 selected changing-cutoff source analytic estimates; P07 actual clock↔OS intertwiner. KK/2D/3D/GR can progress as independent refutation consumers.

**Standalone Clay completion is independent:** physical P05/P06 alone may complete a literal Clay result if the full theorem conditions are satisfied. P01–P04 and P07–P10 are additional proposed unification statements; they may neither fabricate nor veto an independently rigorous Clay result.

## P00 — source authority, existing owners and branch integration

**Deliverable:** source-pinned proof graph, actual chosen physical source model, exact-head import compiler receipt. **Exit:** #1460 can actually see all intended #1444 modules and sources; all imported theorem owners have traceable proofs.

- [ ] **P00.L01** Pin exact SHA/base/imports and owners for PR #1440/#1444/#1460; keep #1241/#1120/#1132/#1045/#1284 separately labelled.
- [ ] **P00.L02** Integrate latest #1444 variable-periodic Haar and gauge modules into #1460 without discarding later work; verify real file readback and conflicts.
- [ ] **P00.L03** Search/import existing signed plaquette, Wilson trace, SU(N) matrix, Haar, BIDI, signature, Hilbert, Stone, Möbius and source-stress owners before creating aliases.
- [ ] **P00.L04** Check Golden focused Agda roots against a pinned Agda/stdlib revision, with 0 metas/postulates/unsafe imports/termination overrides including transitive dependencies.
- [ ] **P00.L05** Distinguish original analytic axioms/external sources from inhabited proof terms; no dummy proof object may supply the desired physical conclusion.
- [ ] **P00.L06** Create source-to-object map for microscopic state, accessible observer, clock, causal metric, Hilbert H, gauge G, selected Wilson measure, OS Hamiltonian and KK action.
- [ ] **P00.L07** Preserve original author citations for history/TSVF, Planck–Heisenberg–Schrödinger/Stone, Yang–Mills/Wilson/Balaban/OS, rigorous 2D YM, stochastic 3D YMH and KK.
- [ ] **P00.L08** Create independent TEST and KERNEL receipts for numerical sizes 2/3/5 gauge convention, five-plane omitted-fibre counterexample and any physical limit calculations.
- [ ] **P00.L09** Add same-source proof exports to BalabanRGTOERegression / TOE graph only after complete actual head imports work.
- [ ] **P00.L10** Freeze precise failure/success states: SOURCE ≠ KERNEL ≠ PHYSICAL; external results remain source-scoped.

**Owners:** ClayYMProofRoadmap, CorePhysicsTheoremRoadmap, CompleteVerifiedPhysicsUnificationRoadmap, BalabanRGTOERegression, #1444 and #1460. **Status:** branch integration OPEN.

## P01 — reversible histories and observed arrow

**Deliverable:** physically selected microscopic history/refinement and observer filtration with operational arrow but no backwards signal. **Exit:** real source/continuum state, not just a three-state toy.

- [ ] **P01.L01** Construct actual microscopic histories, involution Theta and reversible source transition with compatible refinement maps.
- [ ] **P01.L02** Prove Theta²=id, microscopic action-invariance and reversal/refinement naturality.
- [ ] **P01.L03** Give physically admissible initial density rho and terminal positive effect E with consistent normalization and strictly positive selected partition.
- [ ] **P01.L04** Build class operators and decoherence functional D(alpha,beta)=tr(E C_alpha rho C_beta†) with positivity and decoherence hypotheses for probabilities.
- [ ] **P01.L05** Prove normalized selected history probabilities, conditional-state positivity and correct operator/state domains.
- [ ] **P01.L06** Build the actual observer record algebra and filtration inclusion; show conditional expectations are positive/unital and compose on the selected states.
- [ ] **P01.L07** Prove earlier accessible measurements are unchanged under admissible later boundary smoothing although latent inferred history changes; distinguish inference from intervention.
- [ ] **P01.L08** Derive an effective directional, noninvertible observer-quotient semigroup and its order from the source, without hard-coding a metric direction.
- [ ] **P01.L09** Prove micro reversal has no globally strict Nat-rank descent when a fixed history exists; preserve globalStrictReversalRankImpossible, and do not identify MDL with entropy.
- [ ] **P01.L10** Source-weld history, filtration, collapse and shift/MDL carriers or exhibit precise non-equivalence of these different dynamics.
- [ ] **P01.L11** Prove observer probability/refinement convergence (tightness or appropriate projective/infinite source construction) and normalized physical limit.
- [ ] **P01.L12** Construct one physically continuous clock from the actual selected observer process, with operational acyclicity and state identity preserved downstream.

**Owners:** FiniteHistoryOrientationExact, HistoryWeightFiltrationExact, TSFVFiltrationArrowLorentzBridgeExact, TSVF/TSFVFeynman sources; original Aharonov–Bergmann–Lebowitz and Aharonov–Vaidman. **Status:** finite OWNED / physical continuum OPEN.

## P02 — independently derived physical (3,1) cone, metric and orientation

**Deliverable:** nondegenerate 4D causal manifold, three stable transverse spatial modes, exactly one clock and selected metric principal symbol. **Exit:** signature not assumed and physically calibrated.

- [ ] **P02.L01** Define operational causal order from interventions and accessible records; prove transitivity/locality/no backwards signalling.
- [ ] **P02.L02** Construct locally finite causal refinement/continuum maps preserving and reflecting order.
- [ ] **P02.L03** Construct interval counting N(I(p,q)), calibrated physical volumes and independent causal dimension estimator under refinement.
- [ ] **P02.L04** Prove dimensional scaling N(I)~C_D tau^D selects D=4 **from source**, not from storing the number four in an input record.
- [ ] **P02.L05** Prove continuum is an appropriate Hausdorff smooth four-manifold with enough differentiability for physical metric/propagation operators.
- [ ] **P02.L06** Construct finite-speed causal cone field and prove actual operational signal bounds.
- [ ] **P02.L07** Construct positive spatial quadratic h with rank exactly three on a physical stable transverse subspace.
- [ ] **P02.L08** Construct nonzero clock covector theta, one-dimensional clock complement and theta annihilation on spatial modes.
- [ ] **P02.L09** Prove Q(v)=h(v_perp,v_perp)-c²theta(v)² is the **physical propagation principal symbol**, not a hand-selected diagonal signature fixture.
- [ ] **P02.L10** Prove Q nondegenerate and has one timelike and three spacelike directions; its null cone equals the independently derived operational cone, with proper metric scale.
- [ ] **P02.L11** Select a global future half-cone from P01 filtration; prove time orientability and compatibility with physical Cauchy evolution.
- [ ] **P02.L12** Prove hyperbolic well-posedness and energy positivity for the actual physical operator, including calibration of c.
- [ ] **P02.L13** Show IntrinsicSignatureCoreAxioms, contraction and cone/isotropy axioms have actual source inhabitants rather than being supplied as assumptions.
- [ ] **P02.L14** Reconcile LargePosetContinuumLorentz31, Signature31Canonical, Signature31FromIntrinsicShellForcing, CausalForcesLorentz31 and finite orbit B4 witnesses on the same event/metric source.
- [ ] **P02.L15** Prove uniqueness among physically admissible signatures up to justified convention/physical equivalence, rejecting (2,2) or extra-time cases if hypotheses support it.
- [ ] **P02.L16** Preserve geometry negative control: H³×R+ product metric does not automatically identify with Poincaré warped H⁴; demand actual geometry transport.

**Owners:** Signature31Canonical, Signature31FromIntrinsicShellForcing, LargePosetContinuumLorentz31, CausalForcesLorentz31, LorentzEmergenceFromCausalAxioms, YMCarrierSpatialGeometryCheckReceipt. **Status:** conditional signature calculus OWNED, physical D=4/source metric OPEN.

## P03 — selected complex Hilbert structure, CCR, Planck/Heisenberg/Schrödinger

**Deliverable:** same physical clock on a positive Hilbert space with actual strongly continuous unitary one-parameter evolution. **Exit:** no invented unbounded canonical operators.

- [ ] **P03.L01** Derive conserved nondegenerate real symplectic omega from the same source fluctuation/action quotient.
- [ ] **P03.L02** Derive positive compatible real form h_q and a complete physical Hilbert quotient; establish symplectic Hilbert compatibility.
- [ ] **P03.L03** Construct A=h_q⁻¹ omega with correct operator domains and positive -A² for polar square root.
- [ ] **P03.L04** Prove selected J=A(-A²)^(-1/2) exists, J²=-1, is compatible with phase dynamics and gives the physical quantum imaginary unit, not another spacetime axis.
- [ ] **P03.L05** Prove the compatible Hermitian product is positive, conjugate symmetric, complete and admits correctly normalized Born states.
- [ ] **P03.L06** Reuse original finite C3/Heisenberg/Weyl operators, central cocycle and finite representation laws without treating finite qutrit matrices as unbounded CCR.
- [ ] **P03.L07** Prove isometric finite-to-Hilbert embeddings and operator convergence on a common dense invariant core.
- [ ] **P03.L08** Prove limiting Weyl relations and self-adjoint X,P with [X,P]=i*hbar on that core; establish correct nonzero central normalization.
- [ ] **P03.L09** Prove selected clock transfer is a strongly continuous unitary one-parameter group on **the same** H; no arbitrary reparametrisation of time.
- [ ] **P03.L10** Apply/source-verify Stone theorem and self-adjoint energy-bounded-below H_clock; prove generator domains and spectral measure.
- [ ] **P03.L11** Prove Schrödinger equation i*hbar dpsi/dt=H_clock psi and norm preservation on the actual differentiable core.
- [ ] **P03.L12** Prove quantum antiunitary time reversal and operational arrow are compatible; source dynamics may be reversible while filtering is not.
- [ ] **P03.L13** Derive Heisenberg uncertainty and Planck E=hbar omega on the same states/operators, including real metrological hbar units.
- [ ] **P03.L14** Reconcile CCRFromAdmissibleFlow, TreeHeisenbergScalingLimit, SchrodingerQuotientDescentReceipt, SchrodingerSelfAdjointEvolutionReceipt and Quantum.Stone as one actual Hilbert source.

**Owners:** FiniteTreeWeyl, CCRFromAdmissibleFlow (requires ProjectionWeylAxioms), TreeHeisenbergScalingLimit (requires domain/limiting proofs), SchrodingerSelfAdjointEvolutionReceipt (explicitly an OPEN obligation surface), PlanckHbarSIPayloadRequest. **Status:** finite algebra OWNED; continuum source, J, CCR/Stone OPEN.

## P04 — local quantum-frame symmetry to physical gauge theory and SM boundaries

**Deliverable:** independent actual U(1) and selected compact simple G non-Abelian gauge source. **Exit:** pure YM target is separate from matter/KK/gravity.

- [ ] **P04.L01** Construct local physical observable net on P02 geometry/P03 quantum Hilbert, with causal locality and positive state.
- [ ] **P04.L02** Prove local U(1) phase-frame transformation action on a real physical bundle, not only an analogy.
- [ ] **P04.L03** Construct U(1) connection, covariant derivative, Maxwell curvature, action and charged-current conservation.
- [ ] **P04.L04** Construct an actual selected compact simple G=SU(N) physical bundle/representation with local non-Abelian connection, curvature F and Wilson holonomy.
- [ ] **P04.L05** Prove selected non-Abelian gauge transformation/covariance, curvature and Wilson trace invariance, including action/source normalization.
- [ ] **P04.L06** Prove gauge action compatible with the selected H_clock and physical local observable algebra; distinguish photon, color and purely geometric phase.
- [ ] **P04.L07** Construct a rigorous decoupled **pure G** gauge sector to which Clay applies; do not use coupled Einstein–YM or SM matter as a substitute.
- [ ] **P04.L08** If full SM asserted: construct SU(2)_L, correct global SU3×SU2×U1 quotient, chiral fermion reps, charges and physical mass/CKM/PMNS sources.
- [ ] **P04.L09** If full SM asserted: prove local/global gauge anomalies and spin/global bundle compatibility, including actual E6/KK quotient if invoked.
- [ ] **P04.L10** If physical QCD asserted: prove correct beta coefficients/running, Lambda_QCD calibration, threshold/scheme matching from physical measured authority; carrier scale alone is insufficient.
- [ ] **P04.L11** Preserve negative controls: massless QED photon is not pure non-Abelian YM mass gap, and a finite ternary count does not derive real SU(3) color.
- [ ] **P04.L12** Provide direct physical U(1)/G charge and gauge observational consumers, and source-to-source comparison with existing Standard Model owners.

**Owners:** SU(N) gauge/Wilson owners, StandardModelGaugeCouplingAuthorityFrontier, QCDRunningFromCarrierScaleReceipt, #1241 KK/E6 quotient. **Status:** classical/finite conditional; full physical SM OPEN and optional for Clay.

## P05 — R443 finite variable-periodic compact SU(N) Wilson/Haar source

**Deliverable:** genuine physical one-link Haar, native bond codec, normalized Wilson–Gibbs measure and selected R124/CMP119 metric density at every cutoff. **Exit:** actual finite physical measure, not merely a parameterized Haar interface.

- [ ] **P05.L01** Construct compact matrix SU(N) over actual physical complex/real backend: determinant-one, adjoint inverse, group operations, compactness.
- [ ] **P05.L02** Prove selected real normalized ReTr/N, adjoint/inverse and cyclic trace with Bishop/legacy real transport, no unjustified equality.
- [ ] **P05.L03** Construct arbitrary-side original 4-torus **positive-link enumeration**, prove 4*side^4 bonds, all six positive plaquettes/site, signed inverse path laws.
- [ ] **P05.L04** Construct positive-bond function/Vec/setoid decoder and encoder with pointwise roundtrips, count/order and no unrestricted function extensionality.
- [ ] **P05.L05** Prove decoder gauge naturality, selected pointwise observable congruence and translation/C3 covariance.
- [ ] **P05.L06** Prove exact original signed Wilson six-plane action agrees with canonical generic SUNWilsonAction and original plaquette winding source.
- [ ] **P05.L07** Prove genuine compact normalized Borel SU(N) **one-link Haar**, positivity, integrability and bilateral invariance on selected test algebra.
- [ ] **P05.L08** Derive actual native finite product Haar/Fubini and gauge-invariant change-of-variables via one-link Haar and native decoder.
- [ ] **P05.L09** Inhabit #1444 YMClaySUNVariablePeriodicProductHaarExact using the **actual** P05.L07 oneLink and P05.L04 bond vector.
- [ ] **P05.L10** Inhabit #1444 YMClaySUNVariablePeriodicGaugeHaarExact using the **actual** bilateral Haar and OriginalPeriodicGaugeVectorNaturality.
- [ ] **P05.L11** Construct selected physical exp(-S) density, strict partition positivity and normalized gauge-invariant Gibbs/Wilson expectations, including physical real scalars.
- [ ] **P05.L12** Prove all finite integration/measure laws on the actual physical test algebra, with correct division/normalization.
- [ ] **P05.L13** Inhabit selected **CMP119/R124 E/R/B/V density**, metric source variation, counterterms and the literal beta; retain selected source identity.
- [ ] **P05.L14** Prove same-object R443 finite Wilson source equals R124/CMP119 selected density/gauge observable and R445 marked cylinder; not labels alone.
- [ ] **P05.L15** Provide physical cutoff/coupling/SI units and actual finite-positive-time reflection algebra for P06.
- [ ] **P05.L16** Execute deterministic sides 2,3,4,5 gauge regression plus deliberately wrong inverse-gauge orientation and lost-link negative controls, separately from kernel proof.

**Owners:** latest #1444 YMClaySUNVariablePeriodicProductHaarExact, YMClaySUNVariablePeriodicGaugeHaarExact, YMClaySUNConstructedPeriodicGaugeCodecExact, YMClaySUNVariablePeriodicBondPointwiseExact, YMClayNativeSixPlaquetteSUNWilsonActionWeldExact, selected CMP119 and original Wilson/Haar. **Status:** new all-size finite algebra SOURCE; actual Haar, decoder, R124 OPEN.
