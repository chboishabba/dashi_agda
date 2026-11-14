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
**Local execution:** 17 / 17 SymPy/decimal/fraction tests passed (distinct from the earlier 11 / 11).
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

The new source-form checker also solves **effective neutral-atom two-body CM kinematics** for
`N14 atom + neutron -> C14 atom + H1 atom`. Given those same masses and a zero-relative-initial-momentum idealization, it uses
(E_3=(W^2+m_3^2-m_4^2)/(2W)), (E_4=(W^2+m_4^2-m_3^2)/(2W)),
(p^2=E_3^2-m_3^2=E_4^2-m_4^2>0).
It proves the energy sum and both mass shells by exact symbolic rational arithmetic, with daughter opposite momenta (pm33.11398405) MeV/c, and kinetic releases about **0.58383832 MeV** (hydrogen atom) and **0.04203233 MeV** (carbon-14 atom), totaling the computed Q. This is **not** a corrected nuclear-ion final state: the electron bindings and ionization/recombination channels are omitted. It does pay an explicit representative four-momentum kinematic benchmark, not the complete nuclear reaction source.


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
| C1 | Original nuclide count + NIST mass Q-values, exact neutral-atom effective two-body 4-vector kinematic benchmark, typed physical same-reaction gate | Corrected nuclear-ion/electron final-state four-vectors / decay channels / all rate source objects |
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

**Trust:** 17/17 Python symbolic/model tests passed locally for independently reproduced source-form tests. Agda 2.9/Nix kernel acceptance on exact new head not executed (no local Agda or Nix); no physical observer/calibration/cross-section spectrum/KK solution is manufactured. The original 369 atomic hydrogen, post-entropy space, quantum mereology, Lorentz/KK and Clay YM authority boundaries remain unchanged.

---

## 2026-11-14 primary empirical acquisition and biology-PR reconciliation

**New source-indexed receipt:** \`Artifacts/ksw668/empirical_primary_acquisition_20261114.json\`.

**Reproducible acquisition:** \`scripts/ksw668_empirical_acquisition.py\`.
The script fetches the public upstream 70-row annual radiocarbon curve or accepts it through \`--curve /path/to/unmodified/source\`, verifies Git blob \`22ef8d05b8ca09d71f5b1582206a4c92304674e6\`, parses the source rows and confirms all 13 committed source-derived checkpoints. The raw rintcal data package is GPL (>=2); the original complete third-party data file is not vendored into this Agda PR. Additional source-specific tests reproduce the correlated nuclear-rate fit, pigeon intervention hypergeometric summary and measured environmental-neutron conditional comparison. Exact-head execution of this *committed GitHub script* is still pending; local independent replay of the original raw curve and the fitted numerical data was successful.

\`\`\`bash
python3 scripts/ksw668_empirical_acquisition.py --curve /path/to/postbomb_SH1-2.14C --out /tmp/ksw668_empirical.json
# or online, to fetch the upstream public file and reject a changed blob:
python3 scripts/ksw668_empirical_acquisition.py --out /tmp/ksw668_empirical.json
\`\`\`

### Biology owners acknowledged and reused, not duplicated

- **#1021 (merged)**: original avian magnetic channel/source registry and hepatic macrophage material intervention.
- **#1461 (unmerged)**: author-attributed 2020 Thought Emporium candidate genome artifact, robin CRY4 in vitro, pigeon vestibular activation, Lisowski hepatic macrophages, human EEG — different source scopes; a plasmid sequence is not an induced human phenotype.
- **#1471 (unmerged)**: Kuo et al. original bacterial Shine–Dalgarno dmsC high-throughput measured-response corpus, 262,144 9-mers, 257,565 measured genotype means, 635,085 replicate observations, exact Git blob \`151cd87272cbdd6bcc2b1e70bdfd2a4ea2933d2c\`. Its measured holdout and uncertainty machinery can be reused for design, **not** as an isotope or magnetic human causal observation.
- **#1454 (unmerged)**: BH4 pathway and GO/Rhea/Reactome crosswalk with strong failed-identification/kinetic provenance guards. It does not supply isotope reaction kinetics.
- **#993 (unmerged)**: isotope-traced biological nitrogen fixation and source-transport boundaries; distinct \`15N\` uptake does not imply \`14C\` nuclear production.

**New in this PR:** \`DASHI/Biology/KSW668EmpiricalIsotopeMagnetoreceptionSourceExact.agda\`, exported through \`DASHI/Biology/Everything.agda\` and imported by the plasma source crosswalk. It consumes the *existing original* \`AvianMagnetoreceptionSourceRegistry.lisowskiEtAl2026\` and \`AvianHepaticMacrophageMagnetoreception.canonicalHepaticMacrophageMagnetoreceptionReceipt\`, records the source-bounded n=16 and n=18 overcast intervention counts and the archive metadata. It explicitly cannot turn those facts into a human emotion-to-isotope causal model.

### E1 — actual environmental radiocarbon curve acquired

Hua et al., *Radiocarbon* 64 (2022), 723–745, DOI **10.1017/RDC.2021.95**: original measurements compiled for atmospheric \`14C\` 1950–2019 from clean-air samples and tree rings. The publicly redistributed **Southern Hemisphere zones 1–2 yearly curve** was read directly from Maarten Blaauw's rintcal repository, 70 rows, SHA-1 Git blob \`22ef8d05b8ca09d71f5b1582206a4c92304674e6\`. The \`cal BP, 14C age BP, sigma-age BP\` triplets were converted to \(F^{14}C=\exp(-R/8033)\) with \(\sigma_F \simeq F\sigma_R/8033\) as **DASHI derived values**, not raw author columns.

Selected measured/derived checkpoints:
- 1950: age \(+179\pm41\) yr BP; derived \(F^{14}C=0.97796\pm0.00499\).
- **1966 peak in this annual curve**: age \(-3916\pm64\) yr BP; \(F^{14}C=1.62822\pm0.01297\).
- 2000: age \(-763\pm15\) yr BP; \(F^{14}C=1.09964\pm0.00205\).
- 2019: age \(-163\pm8\) yr BP; \(F^{14}C=1.02050\pm0.00102\).

This is an **observed external isotope input** to biological carbon uptake, not a measurement of a person's emotions or nuclear production. Zone identity and source revision must be preserved. Later-than-2019 biological input cannot be treated as directly observed by this dataset; extrapolation is model-dependent.

### C2 / E2 — measured reaction spectrum and terrestrial ambient thermal neutrons

**Li et al. 2026**, DOI **10.1080/00223131.2026.2750299**, ANNRI/J-PARC author-accepted article: neutron energy \(0.0036\)–\(1.8\) eV, \(^{14}\mathrm N(n,p)^{14}\mathrm C\), thermal \(\sigma(0.0253\,\mathrm{eV})=1.828\pm0.053\) barn. The paper also reports a measured-data-fitted function \(\sigma(E)=A E^B\) (E in eV), \(A=0.2706\pm0.0074\) barn, \(B=-0.5103\pm0.0050\), **correlation \(\rho_{AB}=0.993\)**. The receipt retains an eight-energy derived curve and propagates this parameter covariance.

**Exact diagnostic:** applying this published fit at 0.0253 eV gives \(\sim1.76691\) barn, **0.06109 barn below the separately reported thermal interpolation**. These are different published estimation procedures; the mismatch is recorded, not silently erased. The covariance-only fit standard error is not interchangeable with the thermal author's total 0.053-b uncertainty. **Original experimental energy-bin event counts and flux systematics were not acquired**, so the fit cannot be re-estimated from raw counts here.

**Independent environmental measurement:** Dirk, Nelson, Ziegler, Thompson, *Terrestrial Thermal Neutrons* (IEEE TNS, 2003; https://research.ibm.com/publications/terrestrial-thermal-neutrons) reports a representative NIST-traceable sea-level **thermal flux about 4 neutrons cm⁻² h⁻¹** at its US reference station. This is **nine orders of magnitude below** the prior example's deliberately hypothetical \(10^6\) cm⁻² s⁻¹. Using the **same** \(10^{20}\) nitrogen-14 targets, the **uniform-unshielded-thin-target conditional** \(R=\phi N\sigma\) gives \(2.03\times10^{-7}\,\mathrm{s}^{-1}\), about **6.41 events/year**. This **is not a human-body production measurement**: different geography, indoor shielding, angular spectrum, attenuation, target geometry and biologically relevant energy distribution remain unmeasured. It bounds how misleading the prior arbitrary high-flux numerical example was, but does not exclude every other nuclear process.

**UNSCEAR 2008 Annex B paragraph 70** records approximately 230 Bq per kg total carbon and ~2700 Bq of \`14C\` within the human body from environmental carbon uptake; this is activity **inventory**, not evidence of endogenous nuclear formation.

### E1 / A1 — actual measured pigeon and plasma results

**Lisowski et al. 2026, DOI 10.1126/science.ady2486**: randomized macrophage-depletion intervention over a 19-km pigeon homing route across six overcast experimental days in two years. In the published **summary counts**, 16/16 control birds reached home within 70 minutes, versus 0/18 macrophage-depleted birds returning the same day under persistent overcast. The one-sided hypergeometric probability conditional on 16 same-day successes among 34 birds is \(1/\binom{34}{16}=4.53728\times10^{-10}\) under independent, exchangeable assignments. **This p-value is a DASHI reconstruction, not a source author's pre-registered statistical inference**; day clustering and endpoint-time differences must be assessed using original GPS traces. Sunny-day control maintains flight ability. The same paper reports liver blocking temperature 12 K, saturation moment 0.024 A·m²/kg at 2 K, and ~7116 protein-coding gene annotations in the cell sample. Public pigeon MHC-II+ liver 3'-RNA BioProject **PRJEB98986** is verified by NCBI (one SRA experiment, reported ~395 MB sequence volume); the raw reads are **not downloaded**. Original GPS tracks remain a separate Movebank archive acquisition target.

**Nordmann et al., DOI 10.1126/science.aea6425**: pigeon neural vestibular magnetic response remains observed. **Kattnig 2026, DOI 10.1098/rsif.2026.0332** is a competing *idealized modelling and information-theory* counter-analysis constraining the **particular semicircular-canal Faraday-induction explanation**; this is not a new experiment, does not disprove the original neural observation, and does not falsify independent retinal or hepatic sensing.

**MMS primary observation**, DOI **10.1029/2022GL098445**, records negative electron-frame \(J\cdot E'\) in magnetic reconnection; independent DOI **10.1029/2022JA030514** describes positive and negative excursions on the order of \(0.1\) nW m⁻³. **Beware:** electron-frame \(J\cdot E'\) is not laboratory \(J\cdot E\). Source-event FGM/EDP/FPI CDF series from https://lasp.colorado.edu/mms/sdc/public/ remain **unacquired**, so an MMS model-to-measurement closure is not claimed.

### D1 — independent propagation constraint

**LIGO/Virgo/Fermi/INTEGRAL GW170817/GRB170817A**, original companion paper LIGO-P1700308 (https://dcc.ligo.org/LIGO-P1700308/public), reported gamma arrival \(1.74\pm0.05\) s after GW merger and conditional gravitational-versus-light relative speed bounds \([-3\times10^{-15}, +7\times10^{-16}]\). The open waveform archive is https://gwosc.org/events/GW170817/. This is a **real physics baseline**, not a test of the video's undefined conditioned-field travel. No same-metric KK worldline or observed instantaneous transport has been acquired or constructed.

### Remaining empirical maximum-cut, no synthetic substitution

| Gate | Acquired now | Specific missing empirical bytes / calibration |
| --- | --- | --- |
| A1 | Published MMS signed-energy-conversion observations + original helical-Elsasser finite model | Event-identical three-instrument burst FGM/EDP/FPI CDF and its uncertainty/frames |
| B1/B2 | Published Maxwell/confinement provenance and modeled nonzero boundary flux | Same actual lab/space E,B,J spatial fields, surface/volume and time samples |
| C1/C2 | Primary N14 energy-fit coefficients, covariance, measured thermal, empirical environmental neutrons | Original binned event/flux correction data, site-specific energy-dependent \(\phi(E)\), fully corrected nuclear Q/kinematics |
| D1/D2 | LIGO original measured lag and publicly archived strain metadata | An alternative model with same-space-time propagation map, calibrated timing experiment, KK physical solution |
| E1/E2 | **Actual 70-row SH atmospheric C14**, 2026 avian intervention summary, BioProject registration, Spalding human external incorporation | Human same-specimen C14 assay time series, measured dietary/ambient uptake, local neutron spectrum, controlled emotion interventions and confounders |

The **existing biology PR #1471 measured genotype corpus** remains a real quantitative success, but it is neither a source of nuclear reaction rates nor proof of cellular longevity. The empirical sources above are not merged across distinct organism, tissue, nuclear environment or measurement protocols.

---

## 2026-11-14 primary-source closeout tranche 3 — user-supplied direct archive leads

**Acquisition integrity:** This tranche separates (i) original source data read and transcribed, (ii) verified archive location and retrieval code, (iii) actual downloaded/hashed original bytes, and (iv) mathematically/source-verified same-object physical observations. Unresolved hosted datasets are not falsely upgraded to (iii).

### A1/B1/B2 — MMS raw burst event is now timestamped by the original authors

**Original event identity**, not a guessed burst:
- Xiong et al., DOI **10.1029/2022GL098445**: *Distribution of Negative J·E' in the Inflow Edge of the Inner Electron Diffusion Region During Tail Magnetic Reconnection: Simulations Vs. Observations*; uses MMS1 and its cited GSE–LMN basis, not an interchangeable spacecraft/reference basis.
- Lu et al. (2020), DOI **10.1029/2020GL088761**: explicit **17 June 2017 20:24:03–20:24:11 UTC** MMS magnetotail encounter. Another published MMS EDR analysis selects **20:24:06–20:24:09 UTC**.
- The SDC FGM and EDP Level-2 guide exposes exact \`*_fgm_b_gse_brst_l2\` (nT), \`*_edp_dce_gse_brst_l2\` (mV/m), and FPI Level-2 \`des-moms\` and \`dis-moms\` products.

**New \`scripts/ksw668_mms_burst_acquire.py\`:** exact event-probe \`mms_load_burst_intervals\` discovery (returning actual start/end pairs), four explicit original L2 products for MMS1, downloaded CDF-bytes SHA-256 manifest, replay verification. Dry-run by default; full acquisition requires \`--execute\` and PySPEDAS. It does not invent a UTC burst segment or CDF digest.

\`\`\`bash
python3 scripts/ksw668_mms_burst_acquire.py
python3 -m pip install pyspedas cdflib
python3 scripts/ksw668_mms_burst_acquire.py \
  --probe 1 --execute --cache data/mms_20170617 \
  --receipt /tmp/ksw668_mms1_rawsha.json
python3 scripts/ksw668_mms_burst_acquire.py \
  --cache data/mms_20170617 --verify /tmp/ksw668_mms1_rawsha.json
\`\`\`

\`eprime_and_work\` in the script supplies the **unit-correct** elementary transformation:
\[
E'[\mathrm{mV/m}]=E[\mathrm{mV/m}]+10^{-3}v_e[\mathrm{km/s}]\times B[\mathrm{nT}],
\quad J\cdot E'[\mathrm{nW/m^3}]=10^{-3}J[\mathrm{nA/m^2}]\cdot E'[\mathrm{mV/m}].
\]
The current producer \(J=e\,n_e(V_i-V_e)\) must use consistent quasi-neutral densities, the real calibrated FPI velocity coordinates and temporal matching before it is treated as a physical measurement. **Raw CDFs and original instrument flags have NOT been downloaded/executed in this environment.**

### C2 — PARMA/Gordon energy spectra, with covariance and non-extrapolation

**Gordon et al. (2004)**: original ground-level Bonner sphere neutron spectral measurements across environment/altitude; source is a publication, not a ready-to-use machine-readable location-specific file. **Sato et al. JAEA EXPACS/PARMA** supports site/date/elevation/solar condition spectrum generation but the official JAEA distribution carries conditions for use and may require package execution. **No PARMA- or Gordon-derived numerical spectral CSV was acquired in this tranche.**

New \`scripts/ksw668_neutron_spectrum_fold.py\` ingests a source-exported two-column \`energy_eV,differential_flux\` or \`energy_MeV,differential_flux\` CSV with measured/modelled provenance. It converts flux-density units correctly, integrates \(R=N_{14}10^{-24}\int_{\mathrm{validated}} \Phi(E) A E^B dE\) by trapezoids, propagates correlated \(A/B\) fit uncertainty using \(\rho=0.993\), and reports **partial-window** flux and rate separately from entire input spectrum.

The 2026 Li et al. fit only supports \(0.0036\le E\le1.8\) eV; a nominal PARMA lower limit \(10^{-8}\) MeV equals \(0.01\) eV and therefore even its lower edge omits part of the validated 0.0036–0.01 eV range. Above 1.8 eV **no rate can be inferred from this fit alone**. No extrapolation and no fabricated whole-body rate.

\`\`\`bash
python3 scripts/ksw668_neutron_spectrum_fold.py \
  --spectrum /path/to/original_PARMA_or_Gordon_spectrum.csv \
  --source 'author / release / site, altitude, date, solar and soil parameters' \
  --n14-atoms 1e20 --out /tmp/ksw668_rate_partial.json
\`\`\`

**Independent sanity check:** an explicitly synthetic, flat 1 cm⁻² s⁻¹ eV⁻¹ neutron differential flux on 0.01–1 eV, with \(10^{20}\) nitrogen-14 atoms, gives the analytical fit rate \(4.94640653\times10^{-5}\) s⁻¹; a 1000-step numerical trapezoid gives \(4.94652461\times10^{-5}\) s⁻¹ (relative error \(2.39\times10^{-5}\)), and fit-covariance-only standard deviation \(9.85\times10^{-7}\) s⁻¹. **Synthetic unit test, not an empirical site spectrum**.

### E1 — human tissue: *original individual assay data acquired*

**Heinemeier, Schjerling, Heinemeier, Magnusson and Kjaer (2013)**, *FASEB Journal*, DOI **10.1096/fj.12-225599**, original full accessible Table 1: **34 individual AMS assay observations**, from **28 donors** (30 tendon assays, 4 muscle assays), preserving sample identifiers, birth year, observed pMC, analytical \(\sigma\), calibration year, duplicate assays and the paper's original \`OL\` flags (5 outlier-labelled assay rows from donors 25, 28 and 30).

Committed extracted original data: \`Artifacts/ksw668/heinemeier2013_original_human_ams_table1.csv\`.

Two non-source-outlier matched-donor tissue contrasts:
- donor 24: tendon 135.71±0.35 pMC, muscle 109.96±0.34 pMC, difference +25.75 pMC (separate analytical uncertainty \(\sqrt{0.35^2+0.34^2}\approx0.488\) pMC);
- donor 26: tendon 148.48±0.41 pMC, muscle 109.79±0.34 pMC, difference +38.69 pMC (separate analytical uncertainty \(\approx0.533\) pMC).

Assays from the same donor are **not longitudinal measurements** of the same tissue, and the pMC published convention is not silently equated with earlier \`F14C\` atmospheric curves. Donors 25 and 28 are intentionally excluded from naive matched-background estimates because the original authors flag their tendon entries as calibration outliers. Correct atmospheric regional input for original Arkansas donors must be NH/source-aligned (not automatically the previously acquired SH1–2 curve). No within-person emotion perturbation was present.

New exact source modules:
- \`DASHI/Biology/KSW668HumanCarbon14ObservedExact.agda\` with actual original assay IDs and exact pMC×100 paired-donor equalities;
- \`DASHI/Physics/Plasma/KSW668EmpiricalBoundariesExact.agda\` with source status, type-checked sample-carrier witnesses, and uninhabited empirical-closure gates;
- linked from \`Biology/Everything.agda\`, \`Plasma/Everything.agda\` and \`KSW668SourceCrosswalkExact.agda\`.
- \`scripts/check_ksw668_human_ams_original.py\` validates 34 rows, 28 donors, original outliers and matched comparisons. **Exact checked-out script execution/kernel acceptance not verified here.**

### E1 — pigeon Movebank and ENA: raw URL access not independently completed

The user supplied Movebank candidate DOI \`10.5441/001/1.744_2\`, landing UUID \`2f38f106-42bf-4c4a-b7a4-17d758bdd9a9\`, and exact expected original filename \`Navigation with macrophage depletion in homing pigeons.csv\`. The landing endpoint returned **HTTP 403** and the DOI was not independently resolvable here. These identifiers are therefore **user-supplied leads pending archive identity verification**, not acquired 688.56-kB GPS data. An invented DSpace bitstream address or checksum would be unacceptable.

New \`scripts/ksw668_movebank_gps_acquire.py\` takes \`--input\` (actual exported CSV/ZIP) or \`--url\` (real Movebank bitstream address found through its UI), rejects HTML and malformed CSV, validates timestamp/coordinates/animal IDs, and computes raw payload and selected member SHA-256. It **does not** manufacture treatment assignment or infer homing from GPS without the original reference file, loft coordinates, weather and endpoint definition.

\`\`\`bash
python3 scripts/ksw668_movebank_gps_acquire.py \
  --input '/path/to/Navigation with macrophage depletion in homing pigeons.csv' \
  --receipt /tmp/pigeon_raw_receipt.json
\`\`\`

For ENA the original study accession \`PRJEB98986\` is source-pinned (not the same as a constructed read count matrix). New \`scripts/ksw668_ena_reads_acquire.py\` uses the **official** ENA \`filereport\` endpoint for \`read_run\` and original \`fastq_ftp,fastq_md5,fastq_bytes\`, with explicit optional downloads, ENA MD5 validation, local SHA-256 and a 1-GiB default size budget. It was source-written but **not executed against the live ENA API** in this environment.

\`\`\`bash
python3 scripts/ksw668_ena_reads_acquire.py --execute --receipt /tmp/pigeon_ena_runs.json
python3 scripts/ksw668_ena_reads_acquire.py --execute --download-reads \
  --output-dir data/ena_PRJEB98986 --receipt /tmp/pigeon_ena_raw.json
\`\`\`

### Exact owner and acceptance status (this tranche)

| Gate | Source-carrier advance | Actual missing acceptance |
|---|---|---|
| A1 | Published MMS original exact 8-second event and matched-instrument fetch program; physical Fourier signed counterexamples already on PR | SDC-derived exact burst segments + FGM/EDP/FPI original SHA checks + measurement frame + original physical MHD comparison |
| B1–B2 | MMS raw acquisition pipeline + checked formula for \(J\cdot E'\) frame/unit conversion | Actual vector-calibrated same-epoch sample, boundary surface-volume Maxwell measurement and original Agda PDE weld |
| C1 | Existing original evaluated masses, four-momentum source-form tests | Corrected original nuclear final-state physical reaction source |
| C2 | Correlated original N14 2026 measured cross-section fit and **new finite spectral integral** | Source-author Gordon/PARMA actual numeric flux, location/date/hydrogen/geometry, energy-dependent cross-sections beyond 1.8 eV |
| D1–D2 | Original LIGO propagation and Bell diagnostics remain separated | New actual tested metric/cone/operational KK source |
| E1 | **Original 34 human AMS assay rows acquired**; actual typed two-donor comparisons; Movebank/ENA acquisition scripts | Raw verified pigeon GPS/FASTQ, treatment join, human diet and regional time/AMS data |
| E2 | Explicit source/reconstruction identifiability theorem remains | Same-human within-person isotope baseline, controlled intervention, matched exposure and evidence-backed causal identification |

**Verification:** Data in the human source table are transcribed from the published primary paper and reconciled as 34 rows/28 donors. Local independent analytic checks for neutron integration and published paired-donor contrasts were performed. New scripts and Agda modules are present in GitHub but exact-head Python replay and Agda 2.9 kernel verification are still pending. No original external MMS/Movebank/ENA/PARMA raw bytes downloaded here; do not claim a full physical empirical closure.

---

## Phase P0–P3 continuation — 2026-11-14 exact max-cut physical and empirical advances

### E1 source-specific progress: source-measured individual AMS vs acquired NH source curves

**Important correction:** Heinemeier et al. (2013), DOI 10.1096/fj.12-225599, original Table 1 involved human donors from Arkansas, USA. The earlier acquired *Southern Hemisphere* curve is unsuitable as a naive same-location calibration. Acquired the three available **Northern Hemisphere annual 1950.5–2019.5** original Hua et al. (2021/2022) radiocarbon curves, at exact original upstream \`Maarten14C/rintcal\` Git blob SHA-1:

- NH1: \`f7ff49b2ff6ed99f2a6b5aa811c86a774082cbcf\`;
- NH2: \`296b7fbbee8f69f87501be05f9b1a1391a49e0f5\` (**working Arkansas comparator, subject to zone/diet corrections**);
- NH3: \`aafd74536ec0690f1c1943ac98da3caf7972f59f\`.

Each original source file contains 70 annual calibrated atmospheric radiocarbon-age and uncertainty rows. Original full curves remain in the upstream GPL-licensed distribution; hashes were actually checked through connected original GitHub source. We computed the explicitly **uncalibrated** reference number \`100*exp(-14CageBP/8033)\`, restricted to original donor birth year through the **2000 source autopsy date**, for all **30** original tendon AMS rows and compared numerical envelopes to observed \`pMC\`. This is a SCREEN, not a calibrated isotope likelihood, because atmospheric F14C and human pMC carry distinct conventional/decay/fractionation normalizations and tissue carbon has a nontrivial dietary lag.

**Concrete acquired-source finding:** the three original author-flagged anomalous donors 25, 28, 30 comprise five original tendon assay rows, and **all five** lie outside the simple post-birth 1950–2000 annual NH1, NH2, NH3 envelopes, with **0/25** other tendon assay rows outside these envelopes. NH2 source-derived pMC-vs-proxy gaps:
- donor 25 original AMS IDs \`15882.1\` and \`15882.2\`: *below* lifetime minimum by 4.390349 / 5.020349 proxy units;
- donor 30 original AMS \`16252\`: *above* lifetime maximum by 15.467841 units;
- donor 28 original AMS \`15883\` and \`16247\`: *above* lifetime maximum by 17.490083 / 19.800083 units.

This reproduces the qualitative original-author outlier classification across independent northern-hemisphere source curves; it **does not** infer new isotope production, nuclear conversion, a statistically calibrated deviation, deliberate contamination or emotional causation. Other plausible causes include sample identity, diet/birth estimates, contaminants, and conventions. User must not take the atmospheric proxy numerical residual as a raw measured isotope conservation residual.

- Executable source-pinned \`scripts/ksw668_human_atmospheric_lifetime.py\` supports \`--curve-dir\` with original source files or download + blob verification.
- Actual source-derived full per-assay screen and source hashes: \`Artifacts/ksw668/human_original_ams_northern_lifetime_screen_20261114.json\`.
- Original direct raw human Table 1: \`Artifacts/ksw668/heinemeier2013_original_human_ams_table1.csv\`; original paper's outlier flags preserved.
- Exact-head Python fetch of newly source-written NH script still PENDING; independent original-source GitHub calculation of all source rows and source-receipt creation verified.

### B1/B2 source-typed full vector Maxwell and exact nontrivial integrated boundary

New \`DASHI/Physics/Plasma/KSW668FullVectorMaxwellJetExact.agda\` is a generic original \`C3.RealField\` source-written theorem over the **full three-vector, nine spatial Jacobian first derivatives for E and B**, with explicit 3D curl computed from each Jacobian, Ampère \(\partial_t E-\nabla\times B+J=0\), Faraday \(\partial_t B+\nabla\times E=0\), local energy-rate coefficient and \(\nabla\cdot(E\times B)=B\cdot\nabla\times E-E\cdot\nabla\times B\) in its spatial product-rule form. \`fullVectorBudgetNormalForm\` uses an **original RealField ring solver with 21 independent real coordinates**; \`fullVectorMaxwellPoyntingIdentity\` then consumes both actual source jet curl equalities. Exported by \`Plasma/Everything.agda\` and \`KSW668SourceCrosswalkExact.agda\`.

**Nontrivial exact 3D polynomial test:** choose \(A=t(xy+z^2,\ yz+x^2,\ zx+y^2)\), \(E=-\partial_tA\), \(B=\nabla\times A=t(y,z,x)\), \(J=\nabla\times B-\partial_t E=-t(1,1,1)\), normalized vacuum units. \`scripts/check_ksw668_maxwell_3d_jet.py\` checks Faraday, Ampère, \(\nabla\cdot B=0\), charge continuity, local \(\partial_tu+\nabla\cdot(E\times B)+J\cdot E=0\), all six face surface fluxes, and the original **finite cube** \([0,L]^3\) exact identities:

\[
\frac{d}{dt}\int_\Omega u\,dV=L^5t,\quad
\oint_{\partial\Omega} (E\times B)\cdot n\,dS=-\frac{11}{4}L^5t,\quad
\int_\Omega J\cdot E\,dV=\frac74L^5t,
\]
so the integrated balance is identically zero without assuming boundary flux vanishes. Symbolic \`sympy\` local equivalent source check PASS; exact GitHub code execution on a checked-out head and Agda kernel 2.9 still PENDING. Receipt: \`Artifacts/ksw668/three_dimensional_maxwell_exact_receipt_20261114.json\`. This is **not** observed MMS or a complete continuum U1/SI Maxwell derivation. The local jet record requires original \(C^1\) field producer and source physical medium/constitutive assumptions.

### A1/B1 physical MMS same-event joins

\`scripts/ksw668_mms_cdf_energy_reconstruct.py\` now consumes the **actual original MMS1 SHA-256 CDF manifest** emitted by \`ksw668_mms_burst_acquire.py\`; checks source probe/event, file digests, original CDF epochs, GSE FGM nT, EDP mV/m, FPI electron/ion density cm⁻³ and bulk velocity km/s, rejects duplicate epochs and out-of-tolerance temporal joins. Source 2017-06-17 published event \`20:24:03–20:24:11 UTC\` and DOIs \`10.1029/2020GL088761\`, \`10.1029/2022GL098445\`.

In physical units it computes the **actual candidate** \(J=e(n_i v_i-n_e v_e)\) from separate source particle moments, \(E'=E+v_e\times B\), and both electron-frame \(J\cdot E'\) and lab \(J\cdot E\) with explicit conversions. Outputs signed min/median/max, fraction negative and valid epoch fraction; **does not claim** correct original author's exact method, CDF data quality, source uncertainties, matched original physics or a calibrated measured result. Actual SDC original burst segments and original raw CDF **NOT acquired in this environment**, thus no signed observational receipt. This is distinct from the finite Fourier MHD transfer exact source algebra.

### C2 actual *cross-energy* nuclear evaluated-source discrepancy

EPRI/NWT Corporation (2010), *Estimation of Carbon-14 in Nuclear Power Plant Gaseous Effluents*, EPRI report **1021106**, Table 2-2 (attributed by report to original **OECD-NEA JEF Report 14, 1994**), records **historical EVALUATED** (not independent modern original measurements) \(^{14}N(n,p)^{14}C\) cross sections at **14 MeV**:

| Historical evaluated library | 14-MeV cross section (barn) |
| --- | ---: |
| JEF-2.2 | 0.04325 |
| ENDF/B-VI | 0.04447 |
| JENDL-3.2 | 0.00420 |
| BROND-2 | 0.05404 |
| CENDL-2 | 0.04324 |

Among these evaluations, max/min ratio \(\simeq12.8667\). Naive application of the **separately measured 2026 Li et al. 0.0036–1.8 eV** fit \(0.2706E^{-0.5103}\) to **14 MeV \(=14\times10^6\) eV** yields merely \(6.10462\times10^{-5}\) barn, **709-ish times below** JEF-2.2 (exact computed ratio \(\approx708.48\)), and is **physically INVALID** since far outside experimental fit support. The historical evaluated-library spread is not a statistical error interval for a modern nuclear evaluation. Original source is https://restservice.epri.com/publicdownload/000000000001021106/0/Product, Table 2-2, with historical authority separated from the 2026 measured low-energy paper DOI \`10.1080/00223131.2026.2750299\`.

New \`scripts/ksw668_neutron_energy_nonextrapolation.py\` hard-rejects physically invalid fit evaluation above 1.8 eV and checks original source-evaluation reported numbers and derived spread; original-source ledger \`Artifacts/ksw668/n14_high_energy_evaluated_nonextrapolation_20261114.json\`. **No modern evaluated all-energy cross-section grid or site-specific neutron spectrum acquired; C2 total production remains OPEN.** No whole-body radioactive source is inferred.

### Updated original A1–E2 exact remaining cuts

- **A1:** original \`IdealElsasserFourierState\` with a *concrete finite signed ±1 rational three-mode and ordered magnetic strengths* is not Agda inhabited/kernel-accepted yet; source-form tests are separate. Actual MMS instrument observational weld awaits FGM/EDP/FPI CDF.
- **B1:** full original RealField **3D local curl-jet** source-written, with signed identity. Full physical U1 C1 field/constitutive and Agda acceptance remains. 
- **B2:** exact analytic full 3D cube **all six faces** proven by SymPy source form, but actual measured surface remains OPEN.
- **C1:** source two-body idealized nuclear kinematics supplied earlier; full ion/electron state and experimental final-state calibration OPEN.
- **C2:** original low-energy measured fit and historical high-energy EPRI evaluations now source-separated; **no extrapolation**. Full modern \(\sigma(E)\), \(\Phi(E)\), body transport OPEN.
- **D1/D2:** no new physically inhabited 5D Einstein–matter/KK causal transport. Flat Lorentz and Bell diagnostics only, SAME selected physical solution OPEN.
- **E1:** individual original human AMS + new NH lifetime envelope cross-source **diagnostic** added; original pigeon GPS and ENA FASTQ downloads and treatment joins remain OPEN.
- **E2:** controlled same-specimen emotions/uptake/clearance/neutron exposure nuclear-residual causal discrimination is neither observed nor proved. Existing original biology experiments do not imply it.

**Acceptance:** Offline GitHub workflow now installs pinned \`sympy==1.14.0\` and runs the new 3D Maxwell polynomial proof/test, 14-MeV extrapolation negative control, original human AMS table checks and existing eight regressions. Execution is not claimed until a real Actions result/CI receipt is returned. **Agda/Nix binaries and internet archive fetch are not available in this task environment; no invented acceptance.**

---

## 2026-11-14 local-first maximum cut, tranche 4 — source-carrier status

The user instructed **local verification over CI**. The current authoritative repo remains PR #1504, not a separate branch or duplicate PR. Kernel acceptance must be recorded from local Agda/Nix, and empirical claims from actual original source bytes. Nothing is passed merely because a script, proof definition, or API link exists.

### P0 — deterministic original archive routes and local replay

**Official MMS SDC source**, https://lasp.colorado.edu/mms/sdc/public/about/how-to/ (original file list and download API):
- \`scripts/ksw668_mms_sdc_direct.py\` is a new PySPEDAS-independent, direct original MMS1 downloader. It requests official \`file_names/science\` for MMS1, 2017-06-17 burst L2, classifies FGM / EDP-DCE / FPI DES-MOMS / DIS-MOMS by original published filename patterns, selects only names actually returned by the SDC, obtains source CDFs one at a time through \`download/science?file=<exact filename>\`, SHA-256 hashes them, and **checks the actual original CDF Epoch entries overlap 20:24:03–20:24:11 UTC**. A burst-file *start timestamp* is explicitly insufficient to prove event coverage.
- Prior \`scripts/ksw668_mms_burst_acquire.py\` stays as an alternate original PySPEDAS burst-segment route; \`scripts/ksw668_mms_cdf_energy_reconstruct.py\` remains a candidate time-matched \(J\cdot E'\) producer with unresolved FPI error flags/method differences, not a measured result.
- User original Movebank DOI \`10.5441/001/1.744_2\` and pigeon FASTQ \`PRJEB98986\` acquisition programs remain on branch, but no original GPS, ENA FASTQ or source MMS CDF **bytes were acquired during this tool execution** (network DNS unavailable). No SHA-256 for a nonexistent download is invented.
- \`scripts/run_ksw668_local_maxcut.sh\` is the **local-only** entrypoint. \`bash scripts/run_ksw668_local_maxcut.sh --math\` runs available source numerical regressions; \`--all\` requires actual raw MMS receipt, original Movebank file, ENA receipt and the repo's pinned \`scripts/run_agda29_parallel_check.sh\` for all targeted original modules. Missing raw data/toolchain **fails closed**. This assistant session has no Agda/Nix and has not executed this exact-head runner.

### C1 — original NIST electron-conserving final-state channel

New source-indexed Agda owner \`DASHI/Physics/Chemistry/KSW668NuclearElectronStateLedgerExact.agda\`. Neutral \(\mathrm{^{14}N}\) target has seven electrons, so the instantaneous nuclear product cannot simply replace it with two neutral atoms unless the electron rearrangement/recombination channel is tracked. Distinguish:
1. **Neutral effective mass convention:** \(^{14}\mathrm N_{\mathrm{atom}}+n\to {}^{14}\mathrm C_{\mathrm{atom}}+{}^1\mathrm H_{\mathrm{atom}}\), net ground-state Q based on rounded original atomic masses **625,870.654542472395 eV**. Not a measured instantaneous 2-body microscopic scattering final state.
2. **Ion/electron-conserving neutral daughter:** \(^{14}\mathrm C_{\mathrm{atom}}+p_{\mathrm{bare}}+e^-_{\mathrm{free}}\), a 3-particle final electronic channel in the idealized source model. Q from the same atomic mass data **625,857.056107872693 eV**, i.e. 13.5984346 eV below the neutral C+H convention (hydrogen binding).
3. **Bare nuclear two-body:** \(^{14}\mathrm N^{7+}+n\to {}^{14}\mathrm C^{6+}+p\), before embedding in the original neutral chemical environment. Q from NIST ionization energies **626,313.005436782693 eV**, **+442.350894310298 eV** relative to neutral C+H convention.

NIST ASD 5.12 DOI **10.18434/T4W30F**, successive N I–VII ionization energy sum **1486.0578277 eV**, C I–VI sum **1030.10849879 eV**, H I **13.598434599702 eV**. Source Agda has exact **fixed-point 10^-12 eV scaled** addition/electron inventory equalities. Scripts \`ksw668_nuclear_electron_final_states.py\` and \`ksw668_bare_nuclear_two_body_kinematics.py\` calculate and independently check those results.

**Real bare two-body on-shell calculation:** using 2022 CODATA proton mass 1.0072764665789 u, electron mass \(5.485799090441\times10^{-4}\) u, rounded NIST original neutral masses and summed electron binding, the zero-relative-kinetic-energy COM benchmark gives \(Q_{\rm bare}\approx0.62631332268\) MeV, outgoing common momentum magnitude **~33.11702617 MeV/c**, \(T_p\approx0.5842633883\) MeV and \(T_{^{14}\mathrm C}\approx0.04204993438\) MeV. Full four-momentum, both daughter shells and kinetic sum checked with high-precision Decimal. The bare Q from independent CODATA proton/electron masses differs from the neutral-atom derived value by **~0.317244 eV**: source mass precision/constant edition/electronic isotope/rounding joins are **not** closed; retain and propagate, never erase. This is neither an ionization-resolved cross section nor a beam spectrum/physical branching experiment.

### D1/D2 — conditional genuine KK spacelike-fibre no-shortcut theorem

New Agda owner \`DASHI/Physics/Gravity/KSW668KaluzaKleinSpacelikeFiberCausalExact.agda\`. In sign \((-+++)\), for a **standard spacelike** fifth fibre \(g_5(v,v)=g_4(v_4,v_4)+\phi^2(v^5+A_\mu v^\mu)^2\), with \(\phi^2\ge0\), five-dimensional causal \(g_5(v,v)\le0\) implies **four-dimensional projected causal** \(g_4(v_4,v_4)\le0\). The proof uses the repository's original exact rational ordered field and square positivity, not a fictitious new gravitational field configuration. Exported into the original KSW source crosswalk.
- \`scripts/check_ksw668_spacelike_kk_projection.py\` enumerates 405 exact-rational samples, including 135 five-dimensional causal cases; all project causally. Negative control with a **timelike fifth signature** gives a 5D causal/4D spacelike point, proving the standard metric-sign assumption is material.
- **No** Einstein–matter 5D solution, 5D/4D stress equivalence, actual observer Hamiltonian, or measured operational transport has been constructed. Thus **D2 physical mechanism remains open**. This conditional theorem *constrains* claims of standard KK shortcuts; it does not assert FTL universally impossible under arbitrary nonstandard geometry.

### E1 — Northern-zone atmospheric age/dietary-timing stress

Original Arkansas Heinemeier human donor \`pMC\` cannot be calibrated against Southern Hemisphere \`F14C\` without original conventions. The prior source-pinned NH1/NH2/NH3 \(70\times3\) annual Hua curves are now joined to \`scripts/ksw668_human_lifetime_lag_sensitivity.py\` and \`Artifacts/ksw668/human_ams_nh_lifetime_lag_sensitivity_20261114.json\`.

The model *expands both endpoints* of each individual's birth-to-autopsy (2000) potential atmospheric source years by \(L=0,1,2,5\) years, deliberately overconservative to stress reference-year sensitivity. **All five** original Heinemeier OL-flagged tendon assays from three donors (25, 28, 30) remain numerically outside **every NH1/NH2/NH3** annual \(100\exp(-^{14}\!C{\rm age}_{BP}/8033)\) envelope at all four L values; all other **25 original tendon assays** remain inside all three envelopes. With NH2, at L=5 the five positive outside-envelope distances are ~**1.647, 2.277, 4.311, 8.230 and 10.540 proxy units**; source assay-to-donor associations preserved in receipt.

**Scope:** published author outlier diagnostic is stable under this **one** environmental timing sensitivity. This is **not a fully calibrated tissue isotope standard, probabilistic significance, actual human-diet source input, contamination test, nuclear residual or causal intervention**. A five-year extension is a stress test, not a claim the observed dietary lag is five years.

### Exact remaining max-cut — differentiated

| Gate | Strongest new source result | Unpaid primitive physical or proof interface |
| --- | --- | --- |
| P0 | Official MMS SDC direct source-file/epoch/hash acquisition plus PySPEDAS fallback, original Movebank/ENA scripts, local runner | Networked environment + actual original bytes, the exact source filenames/digests and pinned Agda run |
| A1 | Original state/transfer normal form and source-signed finite triad | Nontrivial **all-mode** rational \`IdealElsasserFourierState\` with selected signed orders accepted by Agda, and same observation of MMS plasma |
| B1–B2 | Full local 3-vector Poynting identity and 3D exact six-face cube budget | Physical original continuum C1 E,B,J field owner, SI constitutive medium, physically measured surface/time data |
| C1 | Real electron conservation, original NIST ionization-corrected neutral vs bare Q and **on-shell bare two-body kinematics** | Initial physical target ionization, actual daughter ions/free electrons/photons and measured channel branching; mass-input uncertainty reconciliation |
| C2 | Energy-bounded measured low-energy fit, 14MeV original evaluated-source negative control | Complete current evaluated \(\sigma(E)\), site/body energy-dependent neutron fluence and attenuation |
| D1–D2 | Conditional standard spacelike KK **projected causal** theorem; timelike-sign counterexample | Actual physical same-metric Einstein–matter solution and observer/communication test (not implied by KK geometry) |
| E1 | 34 actual human AMS original observations and 210 NH atmospheric annual source points, four lag stress windows | Real diet/residence, assay standardization/systematics, pigeon raw GPS/FASTQ and treatment join |
| E2 | Original residual-identifiability theorem and source-bounded nuclear inputs | Matched controlled human isotope intervention, uptake/clearance/flux and detection-limit evidence; no fabricated proof or exclusion |

**Acceptance:** independently locally checked mathematical source equivalents for 3D Maxwell, Decimal nuclear final-state corrections and 405 exact-rational KK diagnostic; original GitHub-head Python/Agda compiler validation remains to be run on the user's local toolchain and original downloaded data. Per request, **do not use CI status as a gating criterion**, but never call an uncompiled Agda proof kernel-green.

---

## Phase 4 — 2026-11-14 maximum-cut: what was actually completed, and the exact remaining witnesses

**Governance:** continue the single Clay/physics programme PR #1504; do not gate on GitHub Actions/CI. Kernel-green requires a *local* pinned Agda checker; laboratory-positive requires actual original raw bytes and acceptance. Scientific citation, source-file registry, numerical model, and completed physical theorem are distinct.

### P0 — complete deterministic data retrieval and source integrity

Official NNDC current evaluated neutron library: **ENDF/B-VIII.1** (DOI **10.11578/endf/2571019**; 2026 source publication DOI **10.1016/j.nds.2026.04.001**). A separate pre-existing original acquisition ledger in **AvilaLabs/OpenBNCT**, file \`validation/fir1-k63-water-phantom/evaluated-neutron-source-selection.json\` at commit \`fe5150b896bf525f98bcc5c0a544b6b9d4428e79\`, records the source neutron archive and N14 member:

| Original NNDC item | Source-reported size | Source-reported SHA256 |
|---|---:|---|
| \`neutrons-version.VIII.1.tar.gz\` | 343,724,780 bytes | \`decff90016bfb5c25c8d4c7fb8d81f94ff2f104853165f0fe6a21bf61c4164e4\` |
| \`neutrons-version.VIII.1/n-007_N_014.endf\` | 1,253,924 bytes | \`fd5c0c0beccefbcd0b57c49bcdf835449d2014e3740830377ce24760478c06d8\` |

These digests are **from an independently existing source ledger**. The original NNDC archive/member bytes have **not been downloaded or rehashed in this assistant execution**; do not imply otherwise. New exact source extractor \`scripts/ksw668_endf81_extract_n14.py\` demands both digests and sizes before extraction. New \`scripts/ksw668_endf81_n14np_original.py\` independently reads the real **ENDF-6 MAT=725, MF=3, MT=103** \(^{14}N(n,p)^{14}C\) evaluated full-energy table, respecting TAB1 record padding and NBT/INT interpolation regions, rejecting extrapolation and folding against a real differential neutron flux if supplied. \`scripts/test_ksw668_endf81_primary.py\` uses a deliberately **synthetic ENDF negative control**, including a padded interpolation record and fake-source SHA refusal. The local source-equivalent test passed.

\`\`\`bash
# Step 1: download the official NNDC ENDF/B-VIII.1 neutron archive
# via the NNDC ENDF release page. Do not invent a direct bitstream URL.
python3 scripts/ksw668_endf81_extract_n14.py \
  --archive /original/neutrons-version.VIII.1.tar.gz \
  --out data/ksw668/n-007_N_014.endf
python3 scripts/ksw668_endf81_n14np_original.py \
  --endf data/ksw668/n-007_N_014.endf

# Step 2: AFTER author-site spectrum export AND source audit.
# CSV must be exactly energy_eV,differential_flux_cm2_s_eV.
python3 scripts/ksw668_endf81_n14np_original.py \
  --endf data/ksw668/n-007_N_014.endf \
  --flux-csv /actual_measured_or_PARMA_site_flux.csv \
  --target-n14-atoms 1e20 \
  --out /tmp/source_specific_n14_model.json
\`\`\`

Original ground-level neutron flux \(\Phi(E,\vec x)\), surface-to-tissue attenuation, geometry, chemical inventory, and full physical 14C source production remain **OPEN**; modern \(\sigma(E)\) is identified and an exact source-replay pipeline supplied, not measured in this execution.

MMS direct original SDC source remains \`scripts/ksw668_mms_sdc_direct.py\`; original CDF bytes **not acquired** due inaccessible DNS, ENA \`PRJEB98986\` FASTQ bytes **not acquired**, and Movebank original GPS/reference files **not acquired** (landing 403). P0 cannot be declared fully accepted. Source-derived original human AMS and NH atmospheric points remain previously acquired/reconciled.

### A1 — explicit rational all-mode source and an exact observational no-go

New \`DASHI/Physics/Plasma/KSW668RationalThreeModeSourceExact.agda\` defines \`sourceZPlus\` and \`sourceZMinus\` as **total original rational C3 Fourier coefficient functions** on every \(k\in\mathbb Z^3\), using the repository's exact \`Output.modeEqual\`; outside six selected ±modes they are zero. Explicit modes and coefficients:

\[
p=(1,0,0),\quad q=(0,1,0),\quad k=p+q=(1,1,0);
\]
\[
z^+(q)=e_x,\quad z^+(k)=e_x-e_y,\quad z^-(p)=\pm i e_y,
\quad z^\pm(-m)=\overline{z^\pm(m)}.
\]

Original physical \(b=(z^+-z^-)/2\) has squared strengths **\(|b(k)|^2=1/2>|b(q)|^2=1/4\)**, while original projected normal form \(\mathrm{Re}[-i(z^-(p)\cdot q)\langle z^+(k),z^+(q)\rangle]\) evaluates to **\(+1\)** for positive sign and **\(-1\)** for negative sign. \`scripts/ksw668_a1_original_rational_fourier_witness.py\` locally verifies all finite support formulas and 686 signed checks over \(7^3\) finite mode samples; all-mode behaviour follows from the explicit finite-support definition, but **Agda proof of all-mode reality and divergence-free is not yet provided**.

**Sharper same-observation no-go:** at the same point \(\vec x=0\), both signed states have \(z^+(0)=(4,-2,0)\) and \(z^-(0)=(0,0,0)\) as *physical spatial field values*, although \(\partial_{x} z^-_y(0)=-2\) or \(+2\). Local values agree, actual original modal transfers oppose. Thus a single point's field values **cannot identify** the signed modal transfer without spatial-gradient/mode information. This does **not** say that calibrated multi-spacecraft MMS with measured current-density gradients cannot distinguish the states. Exact Agda \`IdealElsasserFourierState\` global proofs, rational inverse square normalization, and original MMS multi-point/source frame **OPEN**.

### B1/B2 — same original continuum 4-potential and boundary field

\`scripts/ksw668_u1_4potential_continuum.py\` constructs the actual smooth **four-potential** \(A_\mu=(0,t(xy+z^2),t(yz+x^2),t(zx+y^2))\) on Minkowski \((-+++)\). It derives \(F_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu\), \(E_i=-F_{0i}\), \(B=(F_{23},F_{31},F_{12})\) and physical source convention \(J^\nu=-\partial_\mu F^{\mu\nu}\), with **four current** \(J=(-x-y-z,-t,-t,-t)\). Original full antisymmetry, all four Bianchi identities, gauge invariance under \(\chi=t^2xy+3z^2/7\), Maxwell source equations and charge continuity are checked exactly by SymPy on the **same** polynomial fields.

Same spatial cube \([0,L]^3\), exact source \(dU/dt=L^5t\), outward Poynting flux \(=-11L^5t/4\), and \(J\cdot E=7L^5t/4\). This pays an **actual smooth U(1) 4-potential to Maxwell/Poynting** mathematical subgate rather than assuming arbitrary jets. The original repository U1 socket is \`DASHI/Physics/Electromagnetism/U1ElectromagneticApplicationExact.agda\`; no automatic claim that socket SI typing or Agda kernel has proven this calculation. A physical measured MMS surface, original sample geometry and SI constitutive observations remain OPEN.

### C1/C2 — source channels and evaluated modern energy

C1 ion/electron bookkeeping, Q difference ~442.35 eV, bare \(^{14}N^{7+}+n\to{}^{14}C^{6+}+p\) two-body COM energy and CODATA mass-input ~0.317 eV independent-constants mismatch remain as earlier source. Actual ion/excited-state branching, measured final-state photon/electron/radiation and experimental geometry remain OPEN.

C2 now has **actual current evaluation source identity and precise original expected archive/file hashes** (above) and a **source-bound ENDF-6 full-energy parser** with interpolation, source-spectrum integral and synthetics that refuse fake original-data acceptance. Actual modern original file/fluence download, modern uncertainties and biological geometry remain OPEN. The old 14 MeV evaluation spread was a negative control, not sufficient for modern site/whole-body calculations.

### D1/D2 — a genuinely inhabited, but noninteracting, vacuum solution

\`scripts/ksw668_kk_vacuum_observer_solution.py\` derives an explicit **constant Lorentz-signature 5D metric** \(ds_5^2=-dt^2+dx^2+dy^2+dz^2+(dw+\frac23dt)^2\). It checks **125/125 Christoffel entries zero, 625/625 Riemann components zero, 25/25 Ricci and 25/25 Einstein tensor components zero**. Therefore **\(G_{AB}=0=T_{AB}\) with \(\Lambda=0\)** is a real, exact **vacuum** Einstein–matter system solution with *zero* matter, not merely a symbolic dimension comparison. Its constant KK connection is **pure gauge** and cannot transport any physical field faster than the base causal cone.

One explicit five-dimensional null ray moving from \(x=0\) to \(x=4\) reaches a model coordinate clock at \(t=4\); a second null ray with nonzero fifth-fibre velocity and slower four-dimensional projection arrives at \(t=5\). Both are on the same 5D metric. The original \`KSW668KaluzaKleinSpacelikeFiberCausalExact.agda\` rational no-shortcut theorem is consistent. This pays a **vacuum solution and mathematical model-clock calculation**, *not* an interacting Einstein–matter mechanism, 4D–5D operator/Hilbert/OS identification, actual detector record, or FTL physics.

### E1/E2 — honest source join and exclusion test

E1 \`scripts/ksw668_movebank_original_treatment_join.py\` requires original GPS CSV and separately sourced original treatment/loft/overcast/session/reference metadata with both actual SHA-256s, declared source time-zone and loft radius. Per-bird trajectories are evaluated against original release time and date; **GPS absence without documented complete same-day observation is right-censored, NOT counted as non-homing**. Synthetic regression \`test_ksw668_movebank_join.py\` passes; raw original pigeon GPS + reference metadata are not fetched. Original author 16/16 vs 0/18 intervention result must not be auto asserted as reconstructed.

E2 \`scripts/ksw668_e2_zero_count_exclusion.py\` implements an **honest conditional** 95% one-sided Poisson upper bound on additional \(^{14}C\) nuclear reaction-product counts. It requires the SHA-256–verified actual raw experiment, original same specimen, matched controls, assay specifically calibrated to nuclear-product detection (not ordinary AMS radiocarbon fraction), positive lower detection efficiency, nonnegative lower known background and exposure time. For observed **zero events under those premises**, the total Poisson mean upper limit is \(-\log(0.05)\approx2.995732\), and produced-event bound is \((2.995732-b_\text{min})_+/\epsilon_\text{min}\). For a positive original count the program inverts the Poisson CDF. **No actual E2 controlled human original experimental file exists among the sources acquired here**, so the program cannot compute any genuine human exclusion or establish emotional causation. Synthetic negative control \`test_ksw668_e2_bound.py\` passes.

### Local replay receipt (not CI or Agda kernel)

Eight independent **local source-equivalent** Python runs all passed on this assistant's container: A1 rational finite Fourier, B1 4-potential continuum, D2 5D vacuum, modern C2 ENDF TAB1 parser, E2 conditional Poisson, E1 GPS treatment/censoring, earlier B2 3D cube, and the source 70-row atmospheric/14N fit benchmark. Actual exact GitHub PR-head scripts are **not** executed by container copy; the equivalent locally authored programs were run. This environment has no Agda/Nix or external archive DNS. Original receipt summary: \`Artifacts/ksw668/phase4_source_verified_maxcut_20261114.json\`. Full local-only runner now includes all new mathematical cases and the original A1 rational coefficient Agda target.

**No CI dependency.** Per user instruction, local work and exact physical evidence are authoritative. All newly source-written Agda modules remain **not kernel-accepted** until pinned local Agda 2.9 checks.

### Exact remaining atomic obligations (owner / acceptance)

| Gate | Next primitive theorem or empirical witness | A/B/C |
|---|---|---|
| **P0** | Original CDF/Movebank/ENA/N14 ENDF source bytes; hash, actual timestamps and local Agda acceptance | A — execute on accessible local machine |
| **A1** | \`sourceZPlus/sourceZMinus\` original global \`RealityCondition\`, \`DivergenceFreeCondition\`, normalized \`ModeInverseSquare\`; signed \`selectedPlusTransfer\` from actual \`IdealElsasserFourierState\` | A/B — source proof, then 3D instrument observation |
| **B1/B2** | original Agda proof from smooth four-potential/field tensor through U1 source and actual measured complete boundary | B/C — continuous source weld vs measured data |
| **C1/C2** | original measured same-event nuclear/electronic branching; acquire 1.254-MB ENDF original file and real site \(\Phi(E,\vec x)\), physical attenuation | A/C — source data / full transport |
| **D1/D2** | nontrivial stress-energy / 5D metric solution with common four-dimensional physical observer, real communication and arrival clock | C — physical dynamics/experiment |
| **E1** | original Movebank GPS + reference treatment & complete follow-up, raw ENA FASTQ, calibrated original human pMC/dietary transfer | A/C — source ingestion and assay data |
| **E2** | original human controlled and source-calibrated same-specimen nuclear-product detection (or an actual bounded physical exclusion via real dose/efficiency/uncertainty) | C — experiment still absent |

Do not promote the mathematical local ray/detector or the synthetic Poisson/MMS/pigeon tests to physically observed KSW 668 mechanisms.

---

## Tranche 6 — 2026-11-14: maximum-cut reconciliation after original source retrieval audit

**Ownership:** All new work is kept in this single existing DASHI research PR #1504. Golden scientific theorem owners are original Agda modules; local source/kernal verification precedes acceptance. CI is explicitly not an acceptance requirement. No external source bytes, Agda kernel acceptance, instrument observations or hypotheses are fabricated.

### T6.D2 — first genuine *curved, nonvacuum* 5D Einstein–matter solution

The earlier constant-pure-gauge \(M_4\times S^1\) was a valid **flat vacuum**, but was not the requested interacting matter solution. There is now a demonstrably different explicit exact **5D Einstein–massless-scalar** solution:

\[
ds_5^2=-dt^2+t^{1/2}(dx^2+dy^2+dz^2+dw^2),\qquad
\phi(t)=\frac{\sqrt3}{2}\ln t,\quad t>0,
\]
with spatial \(w\sim w+4\), \(8\pi G_5=1\), \(\Lambda=0\), \(T_{AB}=\partial_A\phi\partial_B\phi-\frac12g_{AB}(\nabla\phi)^2\). The fibre is spacelike and its physical radius is **time varying** \(a(t)=t^{1/4}\), so this is a compact KK cosmology but **not** constant-radius pure-gauge KK and not a tested quantum-gravitational mechanism.

Exact symbolic computation **executed locally** in \`scripts/ksw668_kk_einstein_scalar_cosmology.py\`:
- 125 Christoffel positions, **12 nonzero**; 625 Riemann positions, **40 nonzero**; full 25-component \(G_{AB}=T_{AB}\) exactly (nonzero stress); \(R=-3/(4t^2)\).
- \(\rho=p=3/(8t^2)>0\), \(\square\phi=0\), \(\nabla_A T^{AB}=0\).
- Two actual *null geodesic curves* from \(t=1,x=0,w=0\) to the **same comoving detector** \(x=3,w\equiv0\pmod4\). Direct ray \(v_x=1,v_w=0\): \(t=(13/4)^{4/3}\simeq4.81405611\). Fibre-winding ray \(v_x=3/5,v_w=4/5\) completes one \(S^1\) turn: \(t=(19/4)^{4/3}\simeq7.98469159\). Full metric-null, nonaffine geodesic and endpoint identities verified; both arrivals are same-detector *modelled proper time*, **not a real recorded observation**. No FTL shortcut.
- New \`DASHI/Physics/Gravity/KSW668FiveDimensionalEinsteinScalarFRWFriedmannExact.agda\` source-writes exact rational 5D Friedmann relations \(6H^2=\rho\), \(-3\dot H-6H^2=p\), \(\frac12\dot\phi^2=\rho\) in \(u=1/t\), trace relation and a compact-fibre **squared-distance no-shortcut inequality** using existing rational KK positivity. The full \(\sqrt3,\log,t^{1/4}\) analytic metric and Christoffel tensor are **verified only by SymPy**, not Agda. Local Agda typecheck PENDING.
- Still OPEN: the particular user's proposed stress/gauge/observer physical KK solution, a common OS observer Hilbert space, empirically realised signal and actual operational measurement. This source is a genuine **existence result for a conventional 5D Einstein–scalar model**, not universal transport.

### T6.C2 — original ENDF interpolation-law discontinuity repaired

New \`scripts/ksw668_endf81_c2_law_integral.py\` consumes SHA-verified NNDC **ENDF/B-VIII.1** N14 original MAT725 MF3 MT103, source DOI **10.11578/endf/2571019**, and source-labelled site differential neutron flux. It partitions at EVERY original N14 cross-section and flux-energy knot, applies the true ENDF interpolation laws **INT=1,2,3,4,5**, including genuine histogram jumps and repeated-energy left/right discontinuities, and integrates between discontinuities by adaptive interior 8/16-point Gauss–Legendre with explicit convergence refusal. The preceding \`ksw668_endf81_n14np_original.py\` did a simple trapezoid through histogram end values which can produce a **wrong integral**; its physical-rate API now delegates to this safe method and REQUIRES a flux provenance string.

Local synthetic **7/7 regression tests** in \`scripts/test_ksw668_endf81_law_integral.py\` (histogram jump, lin-lin flux×sigma, log-energy, exponential, log-log, repeated-energy discontinuity, out-of-domain and missing-source negative controls) PASS; synthetic samples are **not NNDC original raw bytes**.

Original NNDC \`n-007_N_014.endf\` expected SHA256 \`fd5c0c0beccefbcd0b57c49bcdf835449d2014e3740830377ce24760478c06d8\` and size 1,253,924 **remain unacquired here**. The source-evaluated E1/E2 model must not call an interpolated original evaluation a measured physical body neutron fluence.

**Site spectrum software:** JAEA official **EXPACS/PARMA 4.19** updated 2026-11-05, official https://phits.jaea.go.jp/expacs/top-eng.htm; software downloads have explicit noncommercial/attribution terms. New \`scripts/ksw668_parma_site_spectrum_adapter.py\` offers a clearly identified **secondary Neptoon offline PARMA 4.10** adapter requiring actual site latitude/longitude, elevation, date, water fraction and atmospheric depth (or documented estimate), writing eV differential-flux densities with original settings and source SHA256. DO NOT equate PARMA4.10 with JAEA4.19, site air flux with internal body fluence, or the documented 0.01–100000 MeV Neptoon example with **thermal 0.0036–1.8 eV** coverage; separate genuinely sourced thermal spectrum/ground-albedo/Geant4 transport is essential. No source site output generated here.

### T6.C1 — actual incident-energy-dependent LAB two-body kinematics

New \`scripts/ksw668_n14_relativistic_lab_final_state.py\` solves exact high-precision relativistic \(^{14}N^{7+}+n\to{}^{14}C^{6+}+p\) at **any provided incident neutron kinetic energy** using the previously source-indexed NIST neutral masses, electron ionization correction and CODATA proton/electron values. It computes Källén COM momentum, Lorentz boost, proton/daughter lab energies/momenta for \(\cos\theta_*=-1,0,1\), and verifies all four-momentum components and both daughter mass shells:
- illustrative \(T_n=0.0253\) eV: proton lab KE **0.5842470765–0.5842797443 MeV**, \(^{14}C\) recoil **0.0420336036–0.0420662715 MeV**;
- illustrative fast \(T_n=1\) MeV: proton lab KE **1.2967867081–1.6209603372 MeV**.
- source-grounded input \(Q_{\mathrm{bare}}=0.62631332268\) MeV from independent rounded CODATA masses; earlier NIST neutral+ionization Q differs by ~0.317 eV due source precision/constant convention, a retained uncertainty seam.

Source-specific neutron *incident event energy*, true charge-state branching, atomic electronic final states, excited daughter gamma production, angular cross-sections, sample environment and source uncertainties are still OPEN. The two illustrated incident energies are BENCHMARKS, not measured events.

### T6.E1 — recovered independent original Movebank GPS checksum + exact bitstream identifier

The earlier Movebank landing-page-only source was upgraded by actual **independent third-party original acquisition metadata**:
- Public \`zuizui0223/RSDS\` original \`research/GLOBAL_SOLAR_AZIMUTH_NEW24_PROVIDER_FROZEN_SOURCE_FILE_MANIFEST_20261025.json\` and \`research/GLOBAL_SOLAR_AZIMUTH_NEW24_ORIGINAL_GPS_FIRST_V2_RESULT_20261025.json\`;
- exact Lisowski Movebank package \`2f38f106-42bf-4c4a-b7a4-17d758bdd9a9\`, DOI **10.5441/001/1.744_2**, original bitstream \`b36da51a-30d5-4e4a-856c-940d7b9c27e3\`, original \`Navigation with macrophage depletion in homing pigeons.csv\`;
- original **705,083 bytes**, provider **MD5 \`420dd8de4e0afe50f78ac848846591ba\`**, independent original-MD5 verified, reported **4,347 GPS rows, 34 birds**, **CC BY-NC 4.0**; original third-party direct source receipt Git blob \`eae522571b5902ee0ab901d6bbebbb46ece55d48\`.
- New \`scripts/ksw668_movebank_lisowski_original_bitstream.py\` targets official DSpace \`/server/api/core/bitstreams/<UUID>/content\`, independently enforces exact provider MD5, original file size and census, then locally SHA256 hashes successful original bytes. It also accepts an original manually acquired local file.
- This assistant has NOT acquired the 705-kB original CSV bytes from Movebank; *external independent original MD5 checked* and *ours locally downloaded+SHA checked* are distinct statuses. No treatment group, loft, weather, timestamp matching or source 16/16 vs 0/18 reconstruction has been invented. The existing \`ksw668_movebank_original_treatment_join.py\` still explicitly requires independent original hashed treatment metadata.

### T6.P0 — fail-closed local original-data and Agda acceptance

\`scripts/run_ksw668_local_maxcut.sh\` now runs locally:
- new D2 Einstein–scalar exact symbolic model and rational KK negative control,
- original C1 parameterized on-shell nuclear laboratory kinematics,
- the seven ENDF interpolator source-format and discontinuity tests,
- original E2 conditional neutron visibility bound,
- preexisting U1/Maxwell and source evidence regressions,
- plan-only Movebank original bitstream, MMS SDC and PARMA acquisition interfaces.

\`--all\` refuses to accept:
- absent raw original MMS burst CDF SHA/epoch receipt,
- absent original Movebank CSV or its **exact provider MD5** replay,
- an ENA JSON without actually readable **every FASTQ** original MD5/SHA256 (new \`ksw668_ena_fastq_receipt_verify.py\`),
- absent verified NNDC ENDF/B-VIII.1 N14 original file SHA and real source-specified site spectrum,
- absent pinned local Agda 2.9 acceptance of all new source theorem owner targets.

**No CI acceptance required.** The current runtime cannot resolve the original archive hosts and does not have Agda/Nix. Source-defined checks are committed; exact PR-head all-file replay and Agda 2.9 kernel remain PENDING.

### T6.A1 — original C3 rational transfer row specificity

\`DASHI/Physics/Plasma/KSW668RationalThreeModeOriginalRowsExact.agda\` consumes the **actual original** \`sourceZPlus\` / \`sourceZMinus\` total integer-mode functions, confirms selected C3 row values, same doubled magnetic squared strength \(|2b(k)|^2=2>|2b(q)|^2=1\), and gives normal-form signed transfer **real-embedded** \(+\mathrm{embed}(1)\) and \(-\mathrm{embed}(1)\) in the original C3 carrier. The theorem consuming the original \`selectedPlusTransfer\` still explicitly takes the original complete all-mode RealityCondition / DivergenceFreeCondition hypotheses. The numerical Python all-mode finite support check passes, but **the Agda global all-mode conditions and normalized physical inverse-square projector are STILL OPEN**, and none of this is a measured MMS signed transfer.

### T6.E2 — conditional source-specific isotope effect-size, NOT empirical exclusion

New \`scripts/ksw668_e2_neutron_isotope_visibility_bound.py\` makes the thermal-channel inequality explicit:
\[
N_{\mathrm{new}\,^{14}C}
\le N_{^{14}N}\,\Phi_{\rm thermal,upper}\,\sigma_{\rm thermal,upper}\,10^{-24}\,\Delta t
\]
conditional on **actually verified upper** flux and cross-section across the relevant band, then converts to an assumed measured-carbon isotope pMC upper under explicit carbon mass and modern C14/carbon ratio. It assumes all produced C14 remains in the sample (conservative for this channel).

A strictly **synthetic** one-year example with \(10^{20}\) target N14 atoms, *representative mean not upper* ambient \(4\mathrm{n/cm^2/hour}\), a source 2026 thermal fit illustrative \(\sigma=1.987\) barn, 1g carbon and **assumed** \(^{14}C/\mathrm{C}_{\rm modern}=1.2\times10^{-12}\) gives **6.9672168 atoms** and \(\Delta\mathrm{pMC}\le1.15796517\times10^{-8}\) **only if the assumed ambient mean were a hard upper**. Because it is NOT a measured hard bound, these are **scenario values and not a real exclusion**. Fast/epithermal neutrons, tissue shielding, other nuclear channels, human metabolic uptake and sample contamination are not covered.

The existing \`ksw668_e2_zero_count_exclusion.py\` now rejects original background lower estimates that are themselves statistically incompatible with actual 0-count evidence, rather than turning inconsistency into a false zero-signal bound. No controlled human experiment, same-specimen source-pinned trial or universal emotion nuclear mechanism established or excluded.

### T6 decisive remaining original leaves

| Lane | New strongest delivered cut | Exact next primitive |
| --- | --- | --- |
| **P0** | Original GPS UUID/provider-MD5 located; ENA actual byte replay; official SDC CDF epoch-source program; NNDC original ENDF exact SHA; local runner | Networked execution of *actual* GPS/CDF/FASTQ/ENDF plus P0 local Agda acceptance |
| **A1** | Original C3 signed +/− real-embedded transfer source row exact Agda authored | Original six-mode all-integer-domain Fourier reality+transversality inhabitants and normalized inverse-square, Agda kernel; same observed MMS turbulence transfer |
| **B1/B2** | True original four-potential Maxwell U1 PDE/gauge Bianchi plus six-face continuum field cube | Source **measured** E,B,J field/boundary and calibration with uncertainty, original PDE/agda weld |
| **C1** | Ionization-corrected channel and exact relativistic arbitrary-input-energy 2-body kinematics | Actual event neutron energy, excited nuclear/electronic states and gamma/ion branching, mass covariance |
| **C2** | NNDC latest evaluated library source, true ENDF laws 1–5, proven synthetic discontinuity tests; PARMA route | Actual full raw ENDF grid, measured/validated all-energy including thermal/site neutron source, in-tissue transport/self shielding |
| **D1/D2** | **Curved nonvacuum Einstein–scalar 5D solution + same-detector null geodesics** mathematically completed | Analytic Agda original 5D full tensor weld, particular physical KSW mechanism and genuine instrument/observer measurement |
| **E1** | Original independent pigeon GPS 705083-byte MD5/4347 fixes/34 birds provenance; 34 human AMS + NH1/NH2/NH3 source sensitivity | Exact original raw GPS/treatments/FASTQ joins, diet/residence/AMS fractionation/decay/assay histories |
| **E2** | Conditional thermal-only effect-size and source-data-gated Poisson bound | Real source verified upper spectra and actual same-human controlled isotope interventions or constrained, exposure-specific exclusion |

**Promotion rule:** mathematical solution ≠ original KSW mechanism ≠ source original data ≠ actual human experiment; source script ≠ executable receipt ≠ Agda 2.9 kernel theorem.

---

## Tranche 7 — 2026-11-14: all-mode Fourier proof reuse and actual four-spacecraft spatial-boundary cut

**Same authoritative original PR #1504; no CI acceptance requirement.** These changes are source-authored and numerically independently cross-checked where stated, but the Agda proof owners are not yet typechecked by a pinned Agda binary in this isolated execution environment. External original source data remains unavailable here.

### A1-7 — real Fourier-reality proofs on all Z³, no finite mode-box assumption

Original code had only total sparse \(z^+(k),z^-(k)\) source functions and a global-state constructor requiring callers to supply \`RealityCondition\` and \`DivergenceFreeCondition\`. New:

1. \`DASHI/Physics/Plasma/KSW668SparseModeLookupNegationExact.agda\`: proves the generic original integer-mode selector theorem
\[
\texttt{modeEqual}(-m,s)=\texttt{modeEqual}(m,-s)
\quad\forall m,s\in\mathbb Z^3
\]
by four exhaustive Boolean cases using original \`Output.modeEqualSound\` / \`modeEqualComplete\` and \`Symmetry.negateModeInvolutive\`, with no new choice postulate or bounded representative.
2. \`DASHI/Physics/Plasma/KSW668SparsePairRealityExact.agda\`: constructs an explicit source \(p,-p\) conjugate pair, proves a *universal* all-mode \`pairedSparseReality\` with a real non-self-opposite witness, and applies it to the actual original source \`sourceZMinus\` for **both transfer signs**. Also constructs the separate \(q,-q\) and \(k,-k\) source pairs and their additive \(z^+\) field, proving that ADDITIVE reconstruction's global Fourier reality through existing repository \`complex3ConjugateAdd\`. A \`sourceMinusRealityCondition\` consumes the original \`Audit.RealityCondition\` target.
3. Existing original \`KSW668RationalThreeModeOriginalRowsExact.agda\` retains source-authentic positive/negative signed transfer and exact doubled squared magnetic strengths; no arbitrary scalar transfer surrogate.

**Still explicitly OPEN**: source-written Agda types must be accepted locally; the four-support additive \(z^+\) reconstruction must be proved identical to the original PRIORITY nested lookup at **all integer modes** (pair-support collision exclusion); the actual original plus/minus global \`DivergenceFreeCondition\` and normalized inverse-square projector must be constructed. Original MMS event remains unmeasured in the project. No claim that the original full \`IdealElsasserFourierState\` is already inhabited.

### B2-7 — physically meaningful original MMS1–4 boundary as an explicit measurement object

Prior exact U(1) four-potential/3D cube is a **mathematical solution**. A single MMS1 time series is NOT a three-dimensional measured boundary. Added:

- \`scripts/ksw668_mms4_tetrahedron_boundary.py\`: source-record schema with 2 exact UTC epochs inside **2017-06-17 20:24:03–11**, all **four** source MMS spacecraft, same calibrated GSE reference frame, positions [km], E [mV/m], B [nT], J [nA/m²], timestamp skew, numerical component absolute error bounds, and user-supplied CDF SHA-256 digests that are checked against ACTUAL local bytes. It requires quality flags and rejects degenerate spacecraft geometry.
- The *fixed* spatial observation tetra is obtained by shrinking the first-epoch source tetra. **Both epochs must interpolate strictly within their measured source convex hulls**, not extrapolate. The E,B,J data are interpolated **affinely** from each epoch's four spacecraft. On that explicit model, the surface Poynting flux over **all four faces** and volume integrals of \(u=\frac12(\epsilon_0|E|^2+|B|^2/\mu_0)\) and \(J\cdot E\) are integrated **exactly** using degree-two barycentric moments. The two-time Poynting balance and conservative, componentwise error-only residual bound are output; incomplete clock, interpolation, original physical instrument calibration and time-curvature uncertainties remain EXPLICITLY unqualified.
- \`scripts/test_ksw668_mms4_tetrahedron.py\` adds source-free tests: 3D Maxwell affine plane wave, exact quadratic tetra face integral \(L^4/(12\mu_0)\), volume integral \(VL^2/10\), degenerate-geometry rejection and raw-source-data refusal. An independent hand-built local Python calculation of the same exact plane-wave volume/face algebra gave reference volume \(2.08333\times10^4\,\mathrm m^3\), energy change \(\simeq-2.19544\times10^{-12}\,\mathrm J\), time-integrated outward flux \(\simeq+2.19544\times10^{-12}\,\mathrm J\), relative conservation residual \(\simeq8.6\times10^{-11}\). **Exact PR-head test runner was not executed**.
- \`scripts/ksw668_mms4_fgm_ephemeris_bridge.py\`: confirms from the FGM Level-2 **original** documented ancillary CDF \`mms#_fgm_r_gse_brst_l2\` [km] and its actual \`Epoch_state\` that source positions bracket the event; interpolates only inside original times, with 120s maximum gap, no source fill values or fabricated high-rate survey positions. Requires all four independently source-named and SHA-checkable FGM burst CDFs. FGM Data Products Guide (2016) section 2.9.2.1, Table 5; https://lasp.colorado.edu/mms/sdc/public/datasets/fields/.
- Source provenance caveat: a *matching user-supplied CDF hash* is not independently verified archive origin or a signed instrument calibration. Actual CDF variables, multi-probe instrument error flags and original-SDC source manifest must be audited. The receipt explicitly leaves \`source_physical_boundary_empirically_accepted=false\`. The measured/original MMS boundary B2 physical gate therefore STILL OPEN.

The local \`--all\` acceptance runner now requires actual four-probe FGM ephemeris CDF metadata and a separately sourced four-probe synchronized calibrated E/B/J boundary JSON, rather than accepting MMS1 alone for B2. Example:

\`\`\`bash
bash scripts/run_ksw668_local_maxcut.sh --math

KSW_MMS4_FGM_MANIFEST=/verified/original_mms4_FGM_source.json \
KSW_MMS4_BOUNDARY_JSON=/verified/synchronized_mms4_GSE_EBJ.json \
# alongside the original MMS1/Movebank/ENA/NNDC/site env and pinned Agda
bash scripts/run_ksw668_local_maxcut.sh --all
\`\`\`

### C2-7 — date-domain guard for the offline PARMA secondary source

Official Neptoon documentation (https://www.neptoon.org/en/latest/user-guide/parma-offline/) states its **PARMA 4.10 bundled historical solar W-index ends 2026-03-26**. That is not source data for November 2026: atmospheric neutron spectra must not be silently generated from an unverified W-index extrapolation. \`scripts/ksw668_parma_site_spectrum_adapter.py\` now explicitly fails closed for dates after 2026-03-26, pending a separately provenance-checked extension; it retains the separate **official JAEA EXPACS/PARMA 4.19** versus *secondary Neptoon 4.10* version distinction. It also still requires an actual geographical site, atmospheric depth and source water fraction, and cannot infer a sample/body thermal spectrum from its documented 0.01 MeV lower bound.

### Consolidated exact original max-cut (remaining)

| Gate | New T7 advance | Unpaid primitive |
| --- | --- | --- |
| A1 | Every-Z³ original mode-negation lookup lemma; real original \(z^-\) global conjugacy and additive \(z^+\) global conjugacy are **source-written** | Kernel-accepted proof; additive-to-nested z+ source equality; global transverse C3 dot-zero for +/−, real inverse-square, measured MMS transfer |
| B1/B2 | Original full smooth U1 PDE and now fixed geometric **four-spacecraft** real-data interface with exact affine source face/volume integration | Original multi-MMS raw data, raw ephemeris/quality/calibration uncertainty, physically observed signed flux and measured residual |
| P0 | All-MMS four-point and ephemeris raw provenance added to original archive runner | Actual source CDF bytes, Movebank GPS, ENA FASTQ, NNDC N14 data, site flux and locally pinned Agda |
| C1 | Existing actual NIST Q and relativistic LAB final-state generator | Original neutron event, all electronic/γ/charge-state branching, full source uncertainty |
| C2 | ENDF/B-VIII.1 law-aware quadrature + explicit PARMA W-index date guard | Real original grid, actual thermal through fast neutron site spectrum, in-tissue transport |
| D1/D2 | Curved Einstein–massless-scalar spacelike S1 solution and rational Friedmann source | Kernel full metric/tensor calculus, model-specific KK/observer weld, actual empirical transport |
| E1 | Exact Movebank original independent provider MD5, real human AMS/NH curves | Original downloaded treatment-linked GPS/FASTQ, human diet/fractionation/assay calibration |
| E2 | Source-conditional Poisson bound and isotope effect-size model | Genuine same-specimen controlled counts, measured exposure upper limits or conditional physical exclusion |
