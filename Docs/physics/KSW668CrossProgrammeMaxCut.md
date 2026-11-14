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
