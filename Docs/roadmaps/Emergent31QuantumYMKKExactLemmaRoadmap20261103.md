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

## P06 — actual 4D Euclidean Yang–Mills continuum and mass-gap analytic core (R445/R320/R333)

**Deliverable:** one genuinely physical 4D pure compact-simple-G gauge quantum theory, changing-cutoff continuum, reflection-positive OS reconstruction, strictly positive spectral gap and H6 nontriviality. **Exit:** every literal Clay source requirement is proved; fixed-lattice positivity does not suffice.

- [ ] **P06.L01** Construct directed native physical Wilson cylinder family at all scales and finite volumes, including valid observable restriction/refinement maps.
- [ ] **P06.L02** Prove actual chosen cutoff compatibility or quantified blocking/RG residuals; do not falsely equate unequal finite lattice measures.
- [ ] **P06.L03** Inhabit selected Bałaban *one-step* RG physical source bounds with true constants, analytic norms and gauge/matrix content.
- [ ] **P06.L04** Prove multiscale RG induction uniformly in regulator and volume from those true one-step estimates; no conditional one-step axiom.
- [ ] **P06.L05** Prove physical R445 uniform marked-source moments, regularity and scaling with constants independent of cutoff.
- [ ] **P06.L06** Prove R445 uniform tails/large-field control, tightness and nontrivial quantum state candidates on the actual physical measure.
- [ ] **P06.L07** Construct continuum gauge-invariant Schwinger expectation distributions as cutoff→0 with correct metric/counterterm and observable meaning.
- [ ] **P06.L08** Prove infinite-volume construction (volume→∞), valid ordering/diagonal limit, vacuum normalization and independence of approximation choice.
- [ ] **P06.L09** Prove full required Euclidean rotations/translations, symmetry and clustering where used; finite C3 invariance alone is insufficient.
- [ ] **P06.L10** Prove OS reflection positivity for selected real physical measure/cylinder algebra, preserved through continuum and infinite-volume limits.
- [ ] **P06.L11** Prove remaining necessary OS axioms, distributional/temperedness regularity and correct gauge-invariant reconstruction hypotheses on that state.
- [ ] **P06.L12** Build actual OS Hilbert quotient, vacuum, positive semigroup and self-adjoint **H_OS** from exactly those limit Schwinger functions.
- [ ] **P06.L13** Identify literal selected CMP116 **mixed-J differentiated-source** expectation, source differentiation and rooted-shell coordinates on exactly the R445 family.
- [ ] **P06.L14** Prove selected R320 uniform rooted-shell decay in cutoff, volume, sources and shell distances with physically controlled constants.
- [ ] **P06.L15** Derive Route-S R320→R333 spectral consequence for **the identical H_OS** and gauge-invariant spectrum, including validity of all analytic limit interchanges.
- [ ] **P06.L16** Prove a physical energy-unit Δ>0 independent of cutoff/volume with spec(H_OS) ⊆ {0}∪[Δ,∞), preserving actual ground-state/vacuum identification.
- [ ] **P06.L17** Prove H6 nontriviality: interacting limit theory with nonzero gauge-invariant observables/Hilbert content; rule out a trivial Hilbert/empty operator trick.
- [ ] **P06.L18** Prove all literal Clay scope: four-dimensional R^4 (not only periodic T^4), every required compact simple group or precisely scoped G, continuum axiom status and nontrivial quantum theory.
- [ ] **P06.L19** Discharge transitive Bishop/constructive-real and external analytic assumptions and quantify regularity, source group, cutoff and volume hypotheses explicitly.
- [ ] **P06.L20** Publish exact-head source/lemma/constant/dependency/referee receipts, and compare genuinely same physical OS Hamiltonian with independent proof methods.

**Owners:** #1440 Route-S, #1444 R443–R445, BalabanClayGate4CombinedRGUVIterationExact and BalabanClayConcreteUVToMassGapDependencyExact; original Bałaban, Wilson, Osterwalder–Schrader. **Status:** significant finite and conditional sources OWNED/SOURCE; actual P06 source/limits/Δ OPEN. **This is the independent standalone Clay finish.**

## P07 — central unification theorem: observed clock = actual OS Hamiltonian/metric

**Deliverable:** a source-selected physically meaningful unitary equivalence of the same observed time and OS reconstruction, same metric/gauge observables and spectrum. **Exit:** no equality based only on two independent signature-(3,1) labels.

- [ ] **P07.L01** Select independent P01/P02/P03 clock, accessible-record state and causal metric before importing the target OS continuation.
- [ ] **P07.L02** Construct Euclidean involution/reflection theta from **that exact clock/physical source** with correct positive-time observable sector.
- [ ] **P07.L03** Prove P06 physical Wilson/Schwinger OS reflection is the same theta on selected observables, not a second invented reflection.
- [ ] **P07.L04** Prove physical Lorentzian metric/causal cone from P02 agrees with OS reconstructed geometry under actual continuation and scale/units.
- [ ] **P07.L05** Construct a unitary surjective isometry U: H_clock → H_OS with actual domains, null quotients, chosen state/vacuum and observable algebra compatibility.
- [ ] **P07.L06** Prove U U_clock(t) = U_OS(t) U for every real t, with correct source time normalization and domain continuity.
- [ ] **P07.L07** Derive U H_clock = H_OS U and spectral-projection intertwinement on the self-adjoint generator domains; transport one physical Δ.
- [ ] **P07.L08** Prove equality of selected time-correlations and Wilson/gauge-invariant observables at *matched couplings/boundaries* under the chosen U.
- [ ] **P07.L09** Construct actual physical inhabitants of SameMetricTSFVKK: arrowSource, kkSource, physicalStateOfMetric, same metric/operational orientation—not just its conditional proof term.
- [ ] **P07.L10** Prove Lorentzian/Euclidean stress/Wightman continuation refers to the same physical state when used; do not equate formal Hodge-star signatures with OS.
- [ ] **P07.L11** Prove uniqueness of selected OS analytic continuation in the relevant class, and a negative-control scenario with mismatched clock/metric or failed reflection positivity.
- [ ] **P07.L12** Prove full central commuting square with canonical sector-indexed observable keys, including independent physical interpretation of both forward and backward maps.
- [ ] **P07.L13** Verify *typed* classical finite Hodge (*²=-1 Lorentz two-forms, *²=+1 Euclidean two-forms) as convention check, not substitute for actual U.
- [ ] **P07.L14** Prove genuine same-physical-source identification with the P08 reduced KK 4-metric, if claiming the full five-sector theorem.

**Owners:** TSFVKKSameMetricTransportExact, TSFVFiltrationArrowLorentzBridgeExact, YMClayLorentz31DirectionalKKHodgeExact, OS reconstruction owners and SchrodingerSelfAdjointEvolutionReceipt. **Status:** conditional same-metric SOURCE, actual U/generator equivalence OPEN. **Highest-value cross-domain lemma: P07.L05–L07.**

## P08 — spacelike fifth-circle KK effective theory and Möbius/internal holonomy

**Deliverable:** one actual Lorentzian five-dimensional EFT with correctly reduced 4D metric/action, radion, graviphoton, gauge scalar, thresholds and pure-YM decoupling. **Exit:** low-energy 4D physics matches P07 in stated sectors.

- [ ] **P08.L01** Select an actual spacelike circle principal bundle S¹ over P02 physical time-orientable 3+1 base with correct global spin/orientation.
- [ ] **P08.L02** Derive source-selected Lorentzian 5D metric ansatz and unique declared Jordan/Einstein-frame normalization, preserving one timelike axis.
- [ ] **P08.L03** Construct 5D Einstein–YM–matter **effective** action with boundary, cutoff, physical couplings, group action and counterterms, not a claimed 5D UV completion.
- [ ] **P08.L04** Compute full scalar/vector/gravity curvature action reduction including radion, graviphoton and non-vanishing cross/boundary terms.
- [ ] **P08.L05** Decompose gauge A_A = (A_mu,Phi=A_y) on the same bundle and prove F_AB reductions into 4D YM curvature, covariant scalar derivative and scalar interactions.
- [ ] **P08.L06** Prove 5D and 4D gauge transformations, source variation/stress and field equations commute with zero-mode reduction when admissible.
- [ ] **P08.L07** Prove tree-level g4²=g5²/ell and kappa4^-2=ell*kappa5^-2 only under stated unwarped/constant-circle conventions, with units.
- [ ] **P08.L08** Derive orthonormal KK modes and untwisted flat-circle m_n²=m_0²+(2πn/ell)², identifying the spectrum in the actual effective field source.
- [ ] **P08.L09** Prove physical low-energy KK truncation or integrate out massive modes with explicit E*ell-dependent Wilson/metric/stress bounds and threshold terms.
- [ ] **P08.L10** Prove stabilization or justified decoupling of radion/adjoint scalar/graviphoton, or retain their full physical observable contributions.
- [ ] **P08.L11** Construct and prove controlled *pure 4D YM* decoupling limit of the gravity/matter/KK theory, matching P06 chosen Wilson/Schwinger source.
- [ ] **P08.L12** Prove the same KK-reduced metric/time/observable algebra as P07, with controlled EFT epsilon, not merely equal signature counts.
- [ ] **P08.L13** If claiming E6/trinification, prove actual global group, chirality, nonliftable quotient bundles, anomalies, CS/WZ/eta/spin regulator and gravity-consistent source on the same field theory.
- [ ] **P08.L14** If claiming Möbius/internal twist, construct genuine associated bundle and Z₂ monodromy, one-loop flip and two-loop return with source-compatible boundary fields.
- [ ] **P08.L15** Prove internal Möbius twist leaves physical base global time orientable or supplies lawful orientable double-cover descent without contradictory operational clocks.
- [ ] **P08.L16** Preserve strict **5D Euclidean lattice ≠ Lorentzian KK ≠ stochastic auxiliary time ≠ complex i** type distinction; require typed maps to compare any two.
- [ ] **P08.L17** Transport #1460 finite ten-plane (five-axis) action/omitted-fibre no-go into the physical 5D curvature source with actual nonnegative norm and retained scalar cross-fibre terms.

**Owners:** #1241 KKSteelmanBidirectionalConsumerExact/E6 global quotient, #1460 YMClayLorentz31DirectionalKKHodgeExact/YMClayFiveSectorBidiSteelmanExact, MobiusOrientationGate (target-only). **Status:** physical 5D action/weld OPEN, finite geometry SOURCE.

## P09 — rigorous selected lower-dimensional backward checks: 4→3→2

**Deliverable:** controlled reductions and *independent* observables corresponding to the actual 2D known YM theorem and precisely scoped local 3D stochastic YM–Higgs construction. **Exit:** comparison with correct scalar/gauge/limit/coupling scope.

- [ ] **P09.L01** Construct a selected compactification and observable reduction R_(d→d-1) at d=4,3 (and 5 as P08) with selected boundary and source conditions.
- [ ] **P09.L02** Derive physical decomposition of F_d into F_(d-1), covariant adjoint-scalar Phi and scalar interactions with all gauge transformation laws.
- [ ] **P09.L03** Prove tree-level coupling g_(d-1)²=g_d²/ell plus correct loop thresholds and physical scheme/scale matching.
- [ ] **P09.L04** Prove selected Wilson-loop holonomy/cylinder source naturality under actual dimensional reduction for loops retained in the base.
- [ ] **P09.L05** Prove 4D→3D gauge+scalar low-energy effective measure/observable agreement with a quantified mode/truncation residual.
- [ ] **P09.L06** Match the *actual locally renormalized* 3D stochastic YM–Higgs gauge-covariant dynamics and mass-renormalization counterterms in the published local scope; do not infer global stationary distribution.
- [ ] **P09.L07** Prove 3D→2D gauge+scalar reduction and valid scalar decoupling to standalone pure 2D YM if claiming that comparator.
- [ ] **P09.L08** Reproduce rigorously the normalized planar simple-loop 2D Wilson expectation exp[-(g2²*C2(R)/2)*Area], in the proper representation/topological scope.
- [ ] **P09.L09** Prove correspondence of the selected 2D Euclidean/Hamiltonian Wilson observable to the external rigorous construction, not only formula resemblance.
- [ ] **P09.L10** Establish quantitative finite-circle/finite-cutoff error and legitimate order of limits for every lower-D comparison.
- [ ] **P09.L11** Retain extra d→d-1 adjoint scalar mode and gauge polarizations; mere numerical polarization accounting cannot replace field/action comparison.
- [ ] **P09.L12** Construct negative controls: wrong loop topology/representation, wrong scalar truncation, wrong coupling, noncommuting limits and invalid gauge state.
- [ ] **P09.L13** Inhabit each adjacent MatchedEuclideanGaugeTower physical observation equality before claiming automatic 5→2 transitive agreement.

**Original external owners:** Ashtekar–Lewandowski–Marolf–Mourão–Thiemann rigorous 2D YM and Chandra–Chevyrev–Hairer–Shen / Chevyrev–Shen stochastic 3D YM–Higgs results; their actual scope controls the bridge. **Status:** published 2D and scoped 3D EXTERNAL; physical DASHI same-sector maps OPEN.

## P10 — same-effective-action stress/GR and exotic-gravity consumers

**Deliverable:** physical metric-dependent effective action, conserved source stress, one positive-G metric and independent multi-channel predictions. **Exit:** source-native physics, not exotic-label promotion.

- [ ] **P10.L01** Construct selected renormalized W[g,A,Psi;B_±] on P07 physical state, including actual metric-dependent counterterms and global boundary conditions.
- [ ] **P10.L02** Prove source metric variation exists and yields T_mu nu=-(2/sqrt(-g))*δW/δg^mu nu with the declared convention and actual tensor domain.
- [ ] **P10.L03** Prove covariant Ward identity/nabla^mu T_mu nu=0 with gauge/matter anomalies, conservation and boundary flux accounted for.
- [ ] **P10.L04** Identify physical R124/CMP119 native metric/stress first variation and all ten independent symmetric stress readouts with the same selected Wilson measure.
- [ ] **P10.L05** Prove Einstein equation with the *same* P07 metric, actual normalized G_N>0 and selected QFT stress, not an independently assumed gravitational state.
- [ ] **P10.L06** Inhabit #1120 Local-C/Wightman source-first P1 Q1 (one-path first variation + reflection) and A2 (source-native stress cylinder identity).
- [ ] **P10.L07** Inhabit #1120 P2 same cosmological renormalization convention, stress×length²/apparatus physical scale, native metric perturbation and controls.
- [ ] **P10.L08** If history/birthmark gravity claimed, prove actual history-sensitive W source and Eq.(2.23) N_V>0, N_ERB≥0 signs, not entropy-memory⇒curvature.
- [ ] **P10.L09** Prove physically allowed defocusing/repulsive geometry from relevant active stress and energy constraints; negative trace alone is insufficient and scalar Kottler shift is not TT wave.
- [ ] **P10.L10** Prove one selected source→stress→metric produces coherent weight/support, geodesic free fall, clock and optical channel predictions.
- [ ] **P10.L11** Close ordinary momentum, electromagnetic, thermal and mechanical nuisance channels, match controls and replicate before observational anomaly promotion.
- [ ] **P10.L12** Preserve material-effective negative G versus universal sign-flipped G and their differing positive-density weak-field fingerprints; no universal negative-G inference.
- [ ] **P10.L13** Prove evidence promotion firewall: an antigravity report, GW signal, history label or stress fixture does not solve Clay YM or imply TOE.
- [ ] **P10.L14** Verify physical same-stress/same-metric continuation through P07 OS and P08 KK when asserted, with actual normalization, or produce discrepancy/error.

**Owners:** #1120 Local-C/Wightman and four-channel, #1132 birthmark Eq.(2.23), #1045 negative-G strongest conditional theorem, #1284 nonpromotion, #1050 source D1, #1241 KK metric/stress. **Status:** many conditional/local fixtures, physical source OPEN.

## P11 — global BIDI, exact-head Golden receipts and final proof

**Deliverable:** one fully inhabited Emergent31YangMillsKKPhysicalClosure theorem (or smallest surviving blocker certificates). **Exit:** all mandatory phases checked, with no hidden circular assumption.

- [ ] **P11.L01** Define canonical physical comparison key (selected source, state, gauge group, coupling, regulator, boundary, observable, limit) for every claimed equality.
- [ ] **P11.L02** Construct physically source-first forward construction from microscopic history → operational causal (3,1) → J/H/Stone → gauge → Wilson → OS.
- [ ] **P11.L03** Construct independent backward steelman from rigorous 2D + scoped 3D sources, independent constructive 4D YM/OS and observed 3+1 physical tests, without importing the desired source identity.
- [ ] **P11.L04** Prove Os(4D Euclidean)→3+1 is a reconstruction and 5D KK→4D is a reduction; stochastic flow auxiliary time and Euclidean five-axis YM are different typed sources.
- [ ] **P11.L05** Prove all selected Wilson/state/hilbert/spectral/time/metric same-observable commuting squares; otherwise retain explicit approximation epsilon or no-go.
- [ ] **P11.L06** Give explicit error bounds ε_O(a,L,ell,mu) for every effective comparison and exact-zero proofs only for genuinely identical sectors.
- [ ] **P11.L07** Prove spectral projection equivalence and Δ>0 on the one physical H clock/H_OS and pure G state, not a different gapped theory.
- [ ] **P11.L08** Prove stress and geometry are the same physical source across Lorentz, Euclidean OS and KK whenever a stress comparison is asserted.
- [ ] **P11.L09** Establish justified limit ordering and permitted interchanges (cutoff→0, volume→∞, KK-radius→0, stochastic time→∞, history-refinement, OS).
- [ ] **P11.L10** Pass independent selected 2D/3D observables and at least one 5D→4D coupling/action same-source comparison at known, defined scales.
- [ ] **P11.L11** Run negative controls: wrong Lorentz clock/signature, wrong Haar inverse orientation, failed OS positivity, mismatched KK scalar, curved geometry mismatch, fake finite gap and universal negative-G fingerprint.
- [ ] **P11.L12** Establish SI metrology, original publication authority, actual global gauge group, measured-coupling and empirical distinctions.
- [ ] **P11.L13** Kernel-check final source graph under Golden Agda safe/zero-postulate/zero-meta/zero-termination-bypass and provide complete exact source HEAD/stdlib logs.
- [ ] **P11.L14** If Lean mirror used, audit exact corresponding theorem and actual source content separately; no automatic Agda↔Lean proof transfer.
- [ ] **P11.L15** Produce distinct standalone Clay YM theorem/receipt and stronger 3+1/KK/GR unification theorem; optional SM and exotic experimental claims remain optional.
- [ ] **P11.L16** Independent mathematics referee audit: domains, genuine source inequalities, nontriviality, volume, spectral theory and all source preconditions; preserve failed no-go.
- [ ] **P11.L17** Independent physical falsification and instrumentation audit for measured causal dimension, lower-D observables, KK thresholds and four-channel gravity if claimed.
- [ ] **P11.L18** Prove terminal theorem only after all actually required physical fields are inhabited; else publish exact smallest unsatisfied primitive-leaf cut.

**Owners:** BalabanRGTOERegression and TOE imports plus all owners above. **Status:** OPEN.
