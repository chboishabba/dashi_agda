# KSW 668 — plasma × 369 atomic/quantum × entropy/space causal maximum cut
**Source:** Ed Weatherall, "Universal Plasma Dynamics KSW 668", user-supplied 00:14–10:04 transcript, 14 November 2026. The video's Keshe claims are attributed source propositions, not accepted physical axioms.

**Method:** Original source first; Agda is golden; same physical carrier when making a physical inference; distinguished finite proof vs numerical/model receipt vs measurement vs conjecture. **No Clay, FTL, lifespan, isotope-control or quantum-gravity result is promoted.**

## Direct implementation receipts on this branch

| Cut | Module / declaration | Paid statement | Not claimed |
| --- | --- | --- | --- |
| A | \`KSW668FiniteDiscriminatorsExact.universalStrongToWeakFromPairCancellationNoGo\` | Proof by countermodel: same (2,1) magnitude labels and reversed pair flow, opposite forward directions | Realistic MHD fields realizing this finite witness; physical flux-rate sign calibration |
| A-source | `KSW668SourceCrosswalkExact.originalPairCancellation` | Exact reuse of **original** `MHDFullTransferFromExchangeCompatiblePayloadExact.pairTransferCancels` | Magnetic-strength order automatically determining exchange coefficient sign |
| A-rational | `KSW668OriginalRationalTransferCountermodelExact.positiveForwardIsUnit`, `negativeForwardIsNegativeUnit`, `positivePairCancels`, `negativePairCancels` | Source-written positive/negative rational transfer values on the **actual** `NSTriadKNRationalOrderedFiniteL2.rationalRealField` + original `ExchangeCompatibleTransfer` | Original physical magnetic-strength ordering and measurable MHD triad instantiation |
| B | \`KSW668FiniteDiscriminatorsExact.zeroFluxImpliesSignedWork\` | If an integrated Poynting balance is supplied and boundary flux vanishes, energy-change-plus-work is zero | Maxwell PDE derivation, functional regularity, boundary flux evaluation |
| B-model | \`scripts/check_ksw668_maxcut.py\` | Unit-normalized local Maxwell solution, exact rational checks for both J signs | Finite-energy global domain/device, Maxwell–MHD original-carrier weld, measured field |
| C | \`tripleAlphaCharge\`, \`tripleAlphaNeutrons\`, \`nitrogenCarbon14Charge\`, \`nitrogenCarbon14Neutrons\`, \`sixHydrogenNucleiCannotDirectlySupplyCarbon12Neutrons\` | Conserved proton/neutron counts in selected reaction sketches; six ^1H nuclei alone do not match ^12C neutron inventory | Q-values, intermediates, rates, stellar vs atmospheric environments, isotope production in people |
| D | \`conditionedFieldNoSignalInConstantMarginal\` | A constant local marginal cannot carry a controllable binary signal | General quantum no-signalling theorem, interacting KK spacetime or proposed new travel dynamics |
| E | \`emotionIsotopeCausalIdentificationNoGo\` | One identical observation cannot uniquely classify two structurally different mechanisms | Biological possibility of both mechanisms; clinical or isotope measurements; identification in a real cohort |
| Crosswalk | \`KSW668SourceCrosswalkExact\` | Typed reuse of MHD triad boundary, U(1), 369 oriented Poynting, 369 hydrogen reduced-mass receipt, quantum spacetime promotion boundary | Merger of any unmerged donor PR, universal physical law |

Local Python acceptance ran with **11/11 tests passing** on 14 November 2026 (CPython, \`fractions.Fraction\`); no Agda/Nix executable was installed in the execution environment. All new Agda theorems are **source-written / Agda 2.9 kernel acceptance pending**. The source is not labelled kernel-verified.

## Why the A/B maximum cut is decisive

Original owner:
\`DASHI/Physics/Plasma/MHDFullTransferFromExchangeCompatiblePayloadExact.agda\`

Its actual \`ExchangeCompatibleTransfer F\` carries an antisymmetric coupling and exchange-invariant payload and proves
\`forwardTransfer + reverseTransfer = 0\` (on the original \`C3.RealField\`).

That identity does not order the forward transfer from \`|B_A|>|B_B|\`. The finite A witness models both possible signs under an unchanged magnitude ordering. The new `KSW668OriginalRationalTransferCountermodelExact` strengthens this by constructing two exact signed `ExchangeCompatibleTransfer` records on the **original rational `C3.RealField`**. It proves forward transfer is `+1` or `-1` (as the field's unit/negative unit) and invokes the actual source's pair cancellation in each case. This is original-carrier algebra, but it does **not** supply a selected physical MHD state or establish `|B_A|>|B_B|` for it. The next stronger test must instantiate the selected *original* helical-Elsasser state, projector and current with an admissible field comparison and signed nonzero \`J·E\`.

Poynting's identity (SI):
\`∂_t(ε0 |E|² / 2 + |B|² / (2μ0)) + ∇·(E×B/μ0) = -J·E.\`

**Exact local diagnostic** (dimensionless normalized ε0=μ0=1):
\`E(t,x)=(1-Jt,0,0)\`, \`B(t,x)=(0,2,0)\`, \`J(t,x)=(J,0,0)\`, \`ρ=0\`, J=+1 or -1. Thus ∇×E=∇×B=0, ∂t B=0, ∂t E=-J, ∇·J=0; Faraday and Ampère hold, as do Gauss's laws. The Poynting flux \`E×B\` is uniform in space, divergence zero. At t=0 the local electromagnetic energy density is \`5/2\` in both cases; \`J·E=+1\` versus \`-1\`, while \`∂_t u=-1\` versus \`+1\`. The program checks these identities exactly with rational arithmetic and multiple sample times.

**Interpretation limit:** prescribed homogeneous current in an unbounded domain is a *local PDE solution*, not a finite-energy global plasma source or self-consistent microscopic matter model. This illustrates directional work ambiguity even with the same initial electromagnetic magnitudes. It is not a globally demonstrated physical implementation of the video's undefined two-field hierarchy.

## Same-object donor dependency graph

- **Actual original MHD:** \`MHDLiteralIdealInvariantTriadCompilerExact\` compiles literal finite energy/cross/magnetic helicity for a selected nonzero physical triad. No global continuum conservation follows from a finite triad.
- **Electromagnetism:** \`U1ElectromagneticApplicationExact\` provides typed SI quantity sockets. \`RightHandRule369Exact\` owns \`E×H\` orientation, not \`J·E\` amplitude or the PDE.
- **369 atomic:** \`AtomicPeriodicTable369HydrogenReducedMassExact\`, \`AtomicPeriodicTable369HydrogenNISTComparisonExact\` report finite one-electron/CODATA/NIST calibration. Reduced mass does not predict nuclear reactions or neutron counts.
- **Quantum, entropy and space:** \`QuantumMereologySpacetimePromotionExact\`, \`QuantumMereologyHamiltonianTransportAuthorityExact\`, \`EntanglementGeometryMereologyBridgeExact\` keep factor geometry, Hamiltonian, time evolution and Einstein dynamics distinct. Entanglement entropy / factor geometry alone does not provide physical causal propagation.
- **Direct entropy/geometry crosswalk:** `KSW668SourceCrosswalkExact` now also imports `EntanglementGeometryMereologyBridgeExact`, `FormalCompressionUniversalityBridge` (post-entropy/MDL), `PenroseGlobalCausalityAuthorityExact`, `AtomicPeriodicTable369MadelungPeriodPartitionExact` and `EpigeneticBodyMemoryBridge` and exposes their canonical non-promotion/source boundaries. This reuses the **existing** owners; it does not prove a universal entropy→spacetime law.
- **Physical gravity and transport:** PR [#1163](https://github.com/chboishabba/dashi_agda/pull/1163) physical conservation/causal-transport; [#1248](https://github.com/chboishabba/dashi_agda/pull/1248) three-plasma / curved-Dirac / Casimir; [#1460](https://github.com/chboishabba/dashi_agda/pull/1460) Lorentz (3,1), KK same-metric frontier. The PRs remain separate and are not automatically imported here.
- **Yang–Mills Clay:** PR [#1503](https://github.com/chboishabba/dashi_agda/pull/1503) F19/P0/Wilson/ghost/Haar/OS co-location. Ordinary U(1) Maxwell/biological magnetic response cannot be claimed to solve interacting SU(N) E1/D1/D2/N1/G1.
- **Plasma engineering:** PR [#1096](https://github.com/chboishabba/dashi_agda/pull/1096) confinement and [#1126](https://github.com/chboishabba/dashi_agda/pull/1126) FRC/nozzle/thrust budgets; no field-only or thrust-only inference.
- **Biology:** PR [#1461](https://github.com/chboishabba/dashi_agda/pull/1461) distinct magnetoreception evidence pathways; PR [#1471](https://github.com/chboishabba/dashi_agda/pull/1471) history-indexed phenotype with organism-specific kinetic calibration still unpaid. Existing \`PlasmaActivatedWaterIsotopeMassBalanceSnowballFrontierExact\` explains why an isotope-source/uptake/loss ledger needs same batch and label provenance, not mere nutrient-content measurements.

## Exact unpaid physical producers, separated from finite proofs

| Gate | Next decisive lemma/producer | Evidence needed for closure |
| --- | --- | --- |
| A1 | \`originalMHDExchangeStrengthOrderingSignedWitness\` | Original \`C3\` MHD physical triad + actual signed transfer and magnetic strength comparison on that same state |
| B1 | \`originalMaxwellDifferentialPoyntingFromU1\` | Maxwell's equations, vector calculus, constitutive unit mapping, real physical \(E,B,J\), source and domain |
| B2 | \`originalMHDMaxwellPoyntingSignedBudget\` | Divergence theorem, regularity, explicit boundary integral, MHD current to original U(1) reduction, both flux signs |
| C1 | \`hydrogenCarbonIsotopeNuclearLedger\` | Actual reaction objects with conservation of baryon number, charge, lepton numbers, 4-momentum, Q-values, intermediate species |
| C2 | \`selectedCarbon12Carbon14ReactionRateCalibration\` | Experimental nuclear cross-sections, distributions and actual astrophysical/atmospheric conditions; negative controls for physiological energies |
| D1 | \`conditionedFieldTransportCausalDiscriminator\` | Lorentz-cone operational signalling geometry; distinguished event/protocol/arrival and no-signalling proof on selected physical quantum carrier |
| D2 | \`sameMetricKKThreePlasmaTransportSolution\` | Same physical KK/Einstein stress solution, globally causal extension, energy conditions, source/receiver, perturbation stability |
| E1 | \`emotionIsotopeCausalIdentification\` | Same-person or randomized intervention with blinded isotope tracer design, mass spectroscopy, background, physiology, biological uptake and fractionation controls |
| E2 | \`originalBiologicalIsotopeReactionCausalExclusion\` | Same-object metabolic + nuclear model, measured rate upper bounds and causal mediation vs isotope redistribution |

No source presently provides an inhabited original E2, C2 or D2 theorem. A conditional theorem whose antecedent is an unmeasured physical producer is not closure.

## Phases / deliverables / acceptance

- **P0 — finite exact source controls:** new Agda A–E finite model, source-adapter and original-rational-field signed transfer pair, no invented physics. **Source-written, pending exact-head Agda typecheck.** Python exact controls **11/11 pass locally**.
- **P1 — A/B original PDE weld:** construct original C3/U(1) fields, dimensions, signed work and boundary flux. **Open.**
- **P2 — C nuclear + 369:** preserve proven charge/neutron arithmetic and add physical energy/rates plus same-object measured isotope data. **Open.**
- **P3 — D entropy/space/quantum:** operator locality, signalling event semantics, same-solution KK/Einstein transport; prove/refute explicit alternative predictions rather than assuming a conclusion. **Open.**
- **P4 — E biological tests:** source-indexed observations/interventions, isotope inventory, causal identification, controlled experiments. **Open.**
- **P5 — Clay and cross-programme acceptance:** after real source equality and separate analytical gates, reconcile only claims paid by their original YM/NS/BSD/quantum owners. **Open.**

### Repeatable commands

\`\`\`sh
python3 scripts/check_ksw668_maxcut.py
scripts/run_agda29_parallel_check.sh DASHI/Physics/Plasma/KSW668FiniteDiscriminatorsExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Physics/Plasma/KSW668OriginalRationalTransferCountermodelExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Physics/Plasma/KSW668SourceCrosswalkExact.agda
\`\`\`

For P0 acceptance require actual Agda 2.9 kernel log from the exact branch head and an import closure/axiom audit. Python success cannot replace kernel acceptance. A successful finite proof cannot replace a physical Maxwell, nuclear, space-travel, Clay or medical proof.
---

## 2026-11-14 A1–E2 second physical maximum cut — exact outcomes

This is the continuation after the initial 11-test finite A–E/369/QM source adapter.
**Reproducible numerical command:** \`python3 scripts/check_ksw668_physical_maxcut.py\`
**Local execution:** 16 / 16 SymPy/decimal/fraction tests passed (distinct from the earlier 11 / 11).
**Source-indexed exact diagnostic receipt:** `Artifacts/ksw668/physical_maxcut_exact_receipt.json` (independently reproduced local checks; canonical exact-head script replay pending). The checker prints its exact source-labelled JSON receipt. These tests were executed in the assistant's Python environment, **not** against an Agda/Nix checker. No test compares to an experiment that was not actually obtained.

### A1 — actual original-form helical-Elsasser finite state

Source owner: \`MHDPlusMinusProjectedPseudoEnergyExact.IdealElsasserFourierState\`; \`MHDLiteralIdealElsasserGalerkinDynamicsExact.plusInteractionIsProjectedElsasser\`; \`MHDElsasserProjectedNonlinearCoefficientExact.elsasserOrderedTransferNormalForm\`.

The selected Fourier triad is \(p=(1,0,0),q=(0,1,0),k=p+q=(1,1,0)\). With all other modes zero and the negative modes set by complex conjugation:

- \(z^-_p=(0,1,0)\)
- \(z^+_q=(1,0,0)\)
- \(z^+_k=(s\,i,-s\,i,0)\), \(s=\pm1\)
- \(b=(z^+-z^-)/2\) in Alfvén-normalized units

The checker verifies every supported mode's Fourier reality and divergence-free condition, actual triad resonance and exact Leray projection. It evaluates the **literal selected ordered plus-mode transfer**

\[
 T_{kpq}=\operatorname{Re}\langle z^+_k,-iP_k[(z^-_p\cdot q)z^+_q]\rangle
\]

as \(T=-1\) for \(s=+1\) and \(T=+1\) for \(s=-1\). In both states, \(\|b_k\|^2=1/2\) and \(\|b_q\|^2=1/4\); the full modal squared-magnetic spectrum is unchanged. Thus a magnetic-amplitude ordering does not fix the sign of this selected triad transfer. It is a **constructed ideal-MHD Fourier initial state**, not a time-integrated plasma device or a claim of universal pairwise field hierarchy.

New Agda source \`KSW668MHDSelectedStateTransferExact.agda\` defines \`doubleMagneticSquaredStrength\`, \`selectedPlusTransfer\`, \`originalMHDSelectedStateNormalForm\` and \`originalMHDGalerkinProjectedSameState\` directly on the original \`IdealElsasserFourierState\`. **Open:** instantiate the *selected rational coefficients* and \`IntegerEmbedding\`/\`ModeInverseSquare\` in Agda, prove strength inequalities and \(\pm1\) there, then exact-head kernel check. Numerical source-form replay does not equal kernel closure.

### B1–B2 — Maxwell law to signed work and actual slab boundary

New Agda owner \`KSW668MaxwellLocalPoyntingExact.TransverseMaxwellJet\` declares derivative coordinates for \(E_y,B_z,J_y\) and exact transverse Ampère/Faraday equations. \`transverseMaxwellJetPoyntingIdentity\` proves the **local algebraic identity** (given those derivative equations)

\[
E\,\partial_tE+B\,\partial_tB+
(\partial_xE)B+E(\partial_xB)+JE=0.
\]

The general original U(1) field/socket → differentiable Maxwell PDE → arbitrary-region divergence theorem remains OPEN. The theorem name deliberately does not claim this broader weld.

The executable exact three-dimensional slab with periodic unit cross-section uses \(\epsilon_0=\mu_0=c=1\),
\(E_y=x-t+1-Jt,\ B_z=x-t,\ J_y=J=\pm1\).
It satisfies local Ampère/Faraday plus Gauss constraints for transverse x-dependent fields. On \(0\le x\le L\),

\[
\frac{d}{dt}\int_0^L\frac{E_y^2+B_z^2}{2}dx
+[E_yB_z]_{0}^{L}+\int_0^L J E_y\,dx=0.
\]

This is checked by **symbolic integration** and all boundary faces (lateral flux cancels with periodic identifications). At \(L=1,t=0\), net outward flux is **2**, for both J signs. The electromagnetic fields and their energy are identical initially; the current can do positive or negative work. Sources and boundary conditions would have to sustain these prescribed fields; this is **not** finite-energy whole-space plasma dynamics or a measured current.

### C1–C2 — four-momentum seam, original NIST masses and one real measured cross section

\`KSW668IsotopeCausalResidualExact.SameReactionKinematics\` now names the **same reaction** four-momentum and rate-source obligation rather than treating stoichiometric proton/neutron equality as nuclear closure. It has no physical inhabitant.

Tabulated NIST isotope atomic masses with electrons cancelling between sides and \(1\;\mathrm u=931.49410242\) MeV give:
- \(3\alpha\to{}^{12}\mathrm C:\ Q=7.2747476075865\) MeV.
- \(^{14}\mathrm N(n,p){}^{14}\mathrm C:\ Q=0.6258706545425\) MeV.

These are decimal calculations from evaluated masses, not measurements of reactions in a body and not uncertainty-propagated full state-of-the-art mass evaluations.

The independently measured 2026 thermal \(^{14}\mathrm N(n,p){}^{14}\mathrm C\) cross section is \(\sigma=1.828\pm0.053\) barn at \(E_n=0.0253\) eV, DOI [10.1080/00223131.2026.2750299](https://doi.org/10.1080/00223131.2026.2750299). Under *hypothetical* thin-target thermal flux \(\phi=10^6\) neutrons/cm²/s and \(N_{14}=10^{20}\) target atoms, \(R=\phi N_{14}\sigma=182.8\pm5.3\) reactions/s (cross-section uncertainty only). This **is not** an ambient human neutron flux or an observed biological carbon-14-production rate. Energy-dependent spectral folding, attenuation, true neutron-flux distributions, chemical uptake, background and uncertainty covariance remain OPEN. Triple-alpha needs a completely different multi-particle stellar temperature/density rate source, which has not been calibrated.

Primary atomic masses: [NIST Isotopic Compositions](https://physics.nist.gov/cgi-bin/Compositions/stand_alone.pl?ascii=ascii). Primary reaction measurement: DOI above. Reaction data authority: [IAEA EXFOR](https://nds3.westeurope.cloudapp.azure.com/exfor/). Retain source and datum versions with every promotion.

### D1–D2 — flat Lorentz + finite quantum no-signalling versus KK

The checker uses a flat 1+1 Lorentz interval for \((\Delta x,\Delta t)=(10,0)\), \(c=1\), proving this illustrative event separation spacelike. On a separate two-qubit Bell state it evaluates Alice's reduced density matrix after Bob's local \(I,X,Z,H\) unitaries **and four nonunitary amplitude-damping CPTP maps** and finds \(I/2\) for all. These are actual finite tests, **not** the general CPTP no-signalling theorem or an Einstein/KK physical solution.

\`KSW668IsotopeCausalResidualExact.SelectedPhysicalTransportTest\` is the joint physical gate requiring a selected common metric, Lorentz cone, matter/field evolution, conservation law, globally consistent causal route, synchronized arrival observations and actual KK/Einstein stress. No inhabited same-solution physical travel has been produced. PRs #1163/#1248/#1460 and quantum-mereology remain distinct owners.

### E1–E2 — measured 14C biology exists; emotional nuclear production untested

An external **primary human observation**, [Spalding, Bhardwaj, Buchholz, Druid & Frisén, *Cell* (2005), DOI 10.1016/j.cell.2005.04.028](https://pubmed.ncbi.nlm.nih.gov/16009139/), used atmosphere-origin bomb-pulse \(^{14}\mathrm C\) incorporated into genomic DNA to retrospectively date human cells. This demonstrates a concrete environmental tracer + biological incorporation mechanism; it did **not** manipulate emotions or measure emotion-driven nuclear transformation.

The exact C3 field lemma \`originalBiologicalIsotopeReactionCausalResidual\` proves the algebraic source recovery:
\[
C_{\rm nuclear}=C_{\rm final}-C_{\rm initial}-C_{\rm uptake}+C_{\rm clearance},
\]
for a SAME-window complete carbon-14 inventory. The checker exhibits identical final isotope amounts from distinct uptake/nuclear-source choices, and source recovery when the other channels are supplied. *Measured* paired uptake/clearance/background/neutron flux and intervention data are not provided. Thus neither positive nor comprehensive exclusionary emotion→nuclear-production causality has been established by this programme.

### Gate ledger after second cut

| Gate | Exact delivered | Still unpaid / closure condition |
| --- | --- | --- |
| A1 | Real divergence-free, conjugate-paired 3-mode original-form MHD signed-transfer model + actual Agda source-state observer/normal-form | Kernel inhabitant with explicit rational wave coefficients and magnetic-order proof; global measured plasma no-go is NOT claimed |
| B1 | Agda transverse Maxwell-jet Poynting algebra proof + exact Maxw. polynomial solution | General original U(1)/MHD field/source/constitutive PDE and kernel check |
| B2 | Exact nonzero 2-unit slab surface flux and integrated Poynting equality | Arbitrary physically calibrated domain/boundary theorem and measured current |
| C1 | Original nuclide count + NIST mass Q-values, typed same-reaction 4-momentum gate | Full 4-vector physical kinematics / decay channels / all rate source objects |
| C2 | Primary 2026 thermal neutron cross section + conditional \(R=182.8\pm5.3\)/s hypothetical example | Actual neutron environment, sigma(E) folding, triple-alpha stellar reaction-rate model |
| D1 | Spacelike flat event + finite Bell-unitary no-signalling diagnostic | General selected quantum CPTP theorem and original physical cone source |
| D2 | Explicit original-KK/Einstein/observer operational test contract | Common solved metric, stability, signal/arrival evidence |
| E1 | Identified original human bomb-pulse \(^{14}C\) tracer source and exact balance residual | Exact sample datasets, metabolic/uptake and neutron flux measurement, randomized confounder control |
| E2 | Exact C3 algebraic source identification conditional on full inventory | Experimental identification/exclusion, uncertainty-bounded nuclear rate and direct effect on carbon isotopes |

### Verification commands

\`\`\`sh
python3 scripts/check_ksw668_maxcut.py
python3 scripts/check_ksw668_physical_maxcut.py
scripts/run_agda29_parallel_check.sh DASHI/Physics/Plasma/KSW668FiniteDiscriminatorsExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Physics/Plasma/KSW668OriginalRationalTransferCountermodelExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Physics/Plasma/KSW668MHDSelectedStateTransferExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Physics/Plasma/KSW668MaxwellLocalPoyntingExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Physics/Plasma/KSW668IsotopeCausalResidualExact.agda
scripts/run_agda29_parallel_check.sh DASHI/Physics/Plasma/KSW668SourceCrosswalkExact.agda
\`\`\`

**Trust:** 16/16 Python symbolic/model tests passed locally for independently reproduced source-form tests. Agda 2.9/Nix kernel acceptance on exact new head not executed (no local Agda or Nix); no physical observer/calibration/cross-section spectrum/KK solution is manufactured. The original 369 atomic hydrogen, post-entropy space, quantum mereology, Lorentz/KK and Clay YM authority boundaries remain unchanged.
