# SAXON Q 2026 primary-paper × existing quantum computer: consumer-specific cut

**26 October 2026.** Research adaptation: Johl Brown with OpenAI assistance. Mathematical and physical origin retained below. This is a *read-only cross-PR integration map*, not a claim of authoring any donor proof or of kernel compilation.

## Source-root ledger

| Claim | Primary authority | Epistemic status |
|---|---|---|
| Grover algorithm and ideal success amplitudes | Lov K. Grover (1996), DOI:10.1145/237814.237866 | mathematical prior art |
| Ambient NV-diamond Grover device (three nuclear search qubits), pulse controls and reported success | Gemsheim et al., *Grover Search with Semiconductor Spin Qubits at Ambient Conditions*, arXiv:2609.13022v2 | primary author experiment; not independently reproduced here |
| QC2026 Dual Core and 16×8/32×16 configurations | SAXON Q company / Kneiß–Gemsheim–Grundmann QC2026 technical publication | manufacturer architecture and product claims; distinct source roots from Grover preprint |
| NV axial Hamiltonian / spin basis in DASHI | original PR #1238 (`chatgpt/diamond-mcg-causal-bioem-20261022`) | existing finite formal model, not sourced device calibration |
| Spin-one and local-gate quantum compiler interface | existing `NonAbelianFusionFromSpin`, `DASHIQuantumBridge` and PR #1262 | existing structural formalisation; do not duplicate |
| Same-object spectral + readout programme | existing PR #1269 | prior finite proof/readout models; do not duplicate |
| Diamond crystallography/axes | existing #1238, #1261 | prior exact finite geometry, *not* a physical gate |
| Grover/cutting regressions, candidate qubit-basis choice | PR #1270 | this adaptation, with explicitly limited claims |

## Precise physical-compiler consumer

The **experimental three nuclear-spin qubits** should not be represented by three copies of the *electron* spin-one carrier: the electron is a readout/control ancilla and nuclear Hilbert spaces differ by isotope. The nitrogen nuclear spin-one `I=1` requires a **specific selected two-dimensional subspace**, and each carbon-13 nucleus `I=1/2` is already two-level. Distinguish all four carriers:
1. Electron spin-one interface, with its spin triplet and optical control.
2. Nitrogen-14 nuclear spin-one; qubit is a selected two-dimensional subspace.
3. Carbon-13 nuclear spin-half first qubit.
4. Carbon-13 nuclear spin-half second qubit.

`SaxonQFiniteQutritLogicalEncodingExact` is only a basis-level *candidate* for item 2 and is intentionally **not** an asserted mapping of the exact `m_I` levels used by Gemsheim et al. An actual paper-specific gate correctness theorem requires: chosen basis, pulse schedule, driven Hamiltonian including isotope- and site-specific hyperfine tensors, calibration/control uncertainty, leakage projector, evolution-to-logical-circuit bound, readout instrument and data receipt. The absolute minimum new implementation is a *typed consumer of those existing donor operators* with same-device parameter and source witnesses; creating new SpinIrrep/Qutrit/Core/OpticalLikelihood modules is counterproductive.

## Readout receipt: don't reinvent it

#1238 already has `NVPhotonBinaryLikelihoodExact`, `NVFiveLevelOpticalMasterExact`, `NVOpticalRateSteadyStateExact`, `NVCrystalOrientationExact`. #1269 has `NVPhotonHistoryCountSufficiencyExact`, `NVPhotonPascalCountClassesExact`, `NVPhotonHistoryLikelihoodExact`, `NVPhotonBinaryDecisionRiskExact`, and exact Python readout checks.

For Grover experimental evidence, the required instance is **one and the same apparatus/run** linking measured post-Grover nuclear-spin configuration to conditioned optical photon counts and readout-correction matrix. An equal-prior toy photon model does not establish the actual instrument fidelity. Crucially, the usual gate/algorithm success `77.3 ± 3.4%` or `87.0 ± 4.2%` (as reported in the preprint) is not an independently measured fidelity of all SXQ128 cores.

## Multicore distinction

#1262 already defines Fin 16 × Fin 8 addresses and same-core gates; #1270 must import those **after merging/stacking exact commits**, never publish a second topology. Native coherent width cannot be identified with `16×8=128` absent coherent intercore resources. Circuit cutting can reconstruct particular observables by signed sums but is *not* evidence of a 128-qubit coherent machine. Existing #1270 exact algebra tests verify only finite examples, with covariance distinctions; not a universal performance theorem.

## Pareto critical path

**P0** Establish paper identity by DOI/arXiv and source-version pin; extract selected `m_I` basis and compiled primitive pulse/gate list from original supplementary PDF.

**P1** Stack verified #1238→#1269 and #1262 ownership into a consumer branch without transplanting duplicated finite group or Hamiltonian machinery. Check imports and typecheck focused modules locally (CI optional).

**P2** Give source-calibrated Hamiltonian and measured control/readout artifact one same-device key. Without it, leave physical correctness a labelled contract; do not fill it with fake parameters.

**P3** Prove specific `compile(pulse schedule) = logical Grover oracle/diffusion` (up to global phase) conditional on a calibrated Hamiltonian. Make logical projection and leakage explicit.

**P4** Check measured output histograms, uncertainty model, and the source authors' corrections against the original artifact, then connect to existing photon Bayesian inference receipts.

**P5** For manufacturer multicore claims, measure or source a device-specific cut decomposer, allocation, runtime and variance; independent benchmark controls decide overhead/benefit. No inference from aggregate advertised qubit count.

Every stage carries source root, original author, dated claim, exact identifier, artifact hash where obtainable, testimony/measurement/proof distinction, confidence, and a correction/retraction mechanism. Proof of a conditional model and external-world corroboration must not share a success badge.


## 2026-10-26 Hamiltonian donor audit / parallel PR progress

Inspection of #1238 `DASHI/Physics/QuantumSensors/NVSpinOneAxialExact.agda` confirms a *parameterised rational electron-spin* spectral Hamiltonian `H_e = D S_z² + γ_e B S_z`, represented by energies `(D+γB,0,D−γB)`, symmetric diagonal matrix and exact signed splitting. #1269 provides the same-object C3/qutrit label weld and electronic field-reversal theorem. #1262 has a distinct finite C3 noncommutation proof; these are **already existing Hamiltonian owners** and should not be rewritten in #1270. The wider repository additionally has `DASHI/Quantum/SelfAdjointGenerator.agda`, `DASHI/Physics/SchrodingerGap.agda` and other Hamiltonian machinery; a filename search does *not* establish their hypotheses are suitable for the NV pulse system. No generic quantum/Hamiltonian re-implementation is justified.

#1269 has also advanced with `NVReadoutRegisterBoundaryExact.agda` and `Docs/physics/NVSaxonQMCGRegisterCrossPR20261026.md`. That donor **already** types electronic `Level electronSensor` apart from candidate nuclear `Level nuclearMemory`. #1270 must consume it after exact-commit integration, not add another indexed carrier. This resolves a high-priority attribution and register conflation risk.

New #1270 consumer regression `scripts/check_saxonq_nv_existing_hamiltonian_projection.py` tests **27 exact rational parameter triples** and every two-state basis selection for the pre-existing axial formula, including reversal `B ↦ −B` and electron `m_s=±1` degeneracy at zero field. This is an independently replicated *algebraic model check*, not a new Hamiltonian, Agda proof, measurement, or source-established nitrogen hyperfine tensor. The zero-field ± electron degeneracy does **not** apply automatically to the candidate ket0/ket1 subspace (whose energies at D ≠ 0, B=0 are D and 0), and cannot be promoted to a statement about the nitrogen nuclear register. Local exact-Fraction reproduction of 27 parameter cases passed. Full committed script execution was not performed locally.

Attribution: physical NV spin Hamiltonian standard NV-center literature; finite axial model and exact module theorem belong to existing #1238, symmetry/readout wrappers #1269, compiler and spin #1262; Gemsheim et al. retain authorship of the Grover experiment; SAXON Q retains ownership of its hardware announcements; regression and cross-PR audit adaptation by Johl Brown with OpenAI assistance, 2026-10-26. No changed epistemic status for physical gate compilation.


## 2026-10-26 jFine / consumer-relative snowball (latest requested cut)

**Directly inspected existing sources**: `DASHI/Biology/JCoarseFineEvaluationFibreExact.agda`, `JCoarseFineConsumerReductionBridgeExact.agda`, `DASHI/Foundations/Base369JCoarseFineStableIdentityDisciplineExact.agda`, and `DASHI/Core/CoarseFineRelativeFibreExact.agda`.

The real reusable prior art is a **relative residual and consumer-indexed exactness contract**, not the number 19683 as a physical register size:
- `CoarseFineReopening` records `coarse`, `relativeFine`, `reopen`, and `reopenExact`.
- With `CoarseDynamicsClosure` and `CoarseConsumerFactorisation`, `coarseProjectionAsExactReduction` and `coarseProjectionRetainsRelativeFineResidual` give a *consumer-specific* reduction that retains its exact reopening witness.
- `FineSensitiveConsumer` plus `fineSensitivityRefutesCoarseOnlyReduction` is the collision discriminator if two fine implementations look identical to a coarse observer but one consumer distinguishes them.
- JFine's harmonic `3^9=19683` relative fibre, semantic decision `19683` carrier, absolute `9×19683` address, and any NV defect Hilbert space are **separately typed carriers**. Matching numbers do not give a bridge: see `Base369JCoarseFineStableIdentityDisciplineExact`.

**New adapter** `DASHI/Algebra/Quantum/SaxonQConsumerRelativeFineBoundaryExact.agda` directly invokes the repository's existing exact-reduction and failure theorems. It is conditional on an explicit consumer-supplied coarse/fine geometry, dynamics, and observation. It makes no claim that any manufacturer core, laboratory pulse, optical readout, or 128-qubit machine satisfies those hypotheses. No new C3, j-invariant, quantum computer, Hamiltonian or probability carrier is defined.

**Operational target for physical application**: model `FineState` as a source-authenticated hardware execution record carrying core assignment, per-core pulse trace, calibrated leakage/error and measurement history; coarse presentation might retain merely core ID, advertised qubit count or aggregated outcome. For a consumer that sees only aggregate counts, a coarse reduction may be adequate under proven factorisation; for phase-sensitive cross-core correlations, errors or provenance inspection it may not. Produce two same-coarse states and a distinguishing observation to invoke the obstruction theorem, with actual experimental artifact witnesses. These examples are design intentions and **not proven physical instances**.

**Recent cross-pollination**: #1269's `NVReadoutRegisterBoundaryExact` and #1238's axial electron Hamiltonian ensure any consumer is register-specific. Neither the jFine evaluation section nor mathematical fibre-surjectivity supplies hyperfine pulse evidence, and an electronic spin spectral collision must not be transferred to nuclear qubit states by label coincidence.

Attribution: Katz–Mazur (1985) and Duncan–Ono (2016) source roots remain with existing jFine modules; their modular mathematics is not claimed as a mechanism behind SAXON Q. Earlier DASHI consumer-reduction kernel remains the theorem owner. The SAXON Q paper belongs to Gemsheim et al.; the product architectures belong to the manufacturer. This conditional adapter and audit are a 26 October 2026 Johl Brown/OpenAI research adaptation. CI intentionally ignored; Agda kernel status remains unchecked.


## Scope correction: jFine was a terminology clarification, not a proposed hardware carrier

On 2026-10-26 the requester clarified that mentioning `jFine` was a response to the assistant's use of “superfine,” rather than a request to incorporate modular-j fine fibres into diamond physics. The assistant's addition of `SaxonQConsumerRelativeFineBoundaryExact.agda` in commit `046fb952` was therefore an unjustified scope expansion. **That adapter was deleted** at commit `9b2bd43f`; it is not a current requirement or an outstanding proof obligation. Prior notes proposing a physical `FineState` instantiation are retired, not promoted.

The original jCoarse/jFine proofs remain valid within their original formal domain and retain their authors' attribution. This correction does not invalidate those results. Do not equate “superfine,” fine control resolution, shot-level data, and `jFine`; they are different descriptions unless a concrete typed and empirically warranted mapping is supplied.

Web primary-source check 2026-10-26:
- SAXON Q's April 2026 QC2026 release explicitly says **two cores, five qubits per core**, independently controlled; https://www.saxonq.com/news/saxonq-stellt-dual-core-quantencomputer-vor/ .
- SAXON Q's technology page reports a **16/32-core 128/512-qubit offering**; https://www.saxonq.com/technology/ . This is a manufacturer description, not a cross-core entanglement receipt.
- The company's April whitepaper states current classical intercore links and circuit-cutting overhead; https://www.saxonq.com/wp-content/uploads/2026/04/SaxonQ-Whitpaper-QC2026-web.pdf .
- Gemsheim et al., `arXiv:2609.13022` (submitted 11 September 2026), reports three **nuclear spin** qubits, measured one-/two-marked Grover success 77.3±3.4% / 87.0±4.2%. These are paper-author measurements on their studied machine, not independently replicated SXQ128 benchmarks: https://arxiv.org/abs/2609.13022 .

Now-prioritized max-cut is **paper-specific Hamiltonian + nuclear register mapping + driven pulse compilation + source-authenticated photon readout and per-core evidence**, reusing #1238/#1262/#1269. CI remains optional. This note corrects source framing and requirements; it does not certify the experiment or discharge the physical compiler theorem.


## 2026-10-26 external verification and paper-to-observation consumer

Fresh public source checks: original experimental preprint `https://arxiv.org/abs/2609.13022` (Gemsheim, Klüpfel, Kneiß, Raatz, Herzig, Mendt, Kreissig, Rückert, Hänel, Meijer, Grundmann; submitted 11 September 2026) explicitly reports one/two-marked three-nuclear-spin Grover results 77.3 ± 3.4% / 87.0 ± 4.2%. These are **reported measured algorithm success**, not ideal probabilities, universal output-state fidelities or cross-core quantum connections. SAXON Q's April 2026 QC2026 Dual Core announcement `https://www.saxonq.com/news/saxonq-stellt-dual-core-quantencomputer-vor/` says 2 × 5 cores/qubits with independently controlled cores. Manufacturer whitepaper `https://www.saxonq.com/wp-content/uploads/2026/04/SaxonQ-Whitpaper-QC2026-web.pdf` explicitly identifies classical links and circuit-cutting limitations. SAXON Q's August product news `https://www.saxonq.com/news-press/` advertises SXQ128 orderability and SXQ512 roadmap. None of these sources is interchangeable with the raw instrument-run dataset.

**New precise finite consumer**: `scripts/check_saxonq_source_gated_grover_readout.py` computes an exact ideal Grover distribution for each of 8 singleton and 28 doubleton oracles, then a *caller-supplied*, column-stochastic classical reporting channel. With identity readout, observed=ideal. With synthetic 10% cyclic misreporting, it correctly exhibits altered success without violating probability normalization. This separates physical logical-output distributions from a measured/classically corrected outcome, and is intended as an eventual consumer of #1269's actual NV photon history/readout bridge. It does NOT pretend the synthetic channel is the actual SAXON Q detector nor duplicate the canonical photon-history likelihood. Script committed; no running or kernel verification claimed in this receipt.

Latest nearby PR #1272 (`DASHI/Physics/Optics/FourierPixelBidirectionalExact.agda`) is optically adjacent but a Fourier-pixel observation proof on a different physical carrier; no automatic import into the NV optical readout. #1269 remains the direct photon-readout same-object owner, #1238 owns NV Hamiltonian and optics, #1262 quantum gate addressing, and #1270 the SAXON Q-specific finite observer tests. The former jFine suggestion was explicitly retired after clarification and remains out of scope.

**Minimal unresolved source join**: obtain actual preprint supplementary pulse/readout operations and independent per-run photon confusion/count records, bind each to a physical device ID and run condition; only then instantiate a non-synthetic channel or prove a calibrated drive-to-unitary refinement. An existing parameterized Hamiltonian proves no such identification without these source values.


## 2026-10-26 late-source cut: product-count vs connectivity, silicon prior art

**Original document families independently checked**:
- Original Grover paper: Gemsheim et al., `arXiv:2609.13022`, submitted 11 September 2026. This is a three-*nuclear*-spin search experiment; its result may not be silently promoted into SXQ128 native eight-qubit/core hardware.
- SAXON Q, April 2026, `QC2026 Dual Core` press release, https://www.saxonq.com/news/saxonq-stellt-dual-core-quantencomputer-vor/ : 2 processors × 5 qubits, each independently controlled, parallel execution. Manufacturer assertion/announcement.
- SAXON Q, August 2026, https://www.saxonq.com/news/orders-for-128-qubit-512-qubit-room-temperature-quantum-computers-open/ : describes SXQ128 as eight fully entangled qubits per core, 16 cores; SXQ512 sixteen per core, 32 cores. Vendor commercial assertion; available to order is **not** a same-device measured register proof.
- Independent reporting of an attributed interview, `Supercomputing News`, 27 July 2026, https://www.supercomputing.news/quantum/saxonq-sxq128-coupled-nv-room-temperature-quantum : CEO Marius Grundmann described *one eight-qubit coupled-two-NV single-core system* as a Q3 delivery milestone and the full 128-qubit demonstration as still being set up as of that interview. This is **reported contemporaneous testimony**, not our independent measurement; date and system-version distinct from August availability.
- Comparative *separate* silicon experiment: `Grover’s algorithm in a four-qubit silicon processor above the fault-tolerant threshold`, `Nature Nanotechnology` 20, 472–477 (2025), https://www.nature.com/articles/s41565-024-01853-5 . Reports electron–nuclear hyperfine mediated nuclear-spin gates and an approximately 95% three-qubit Grover search. **Silicon/phosphorus ≠ diamond/NV**; only a methodological gate-architecture comparator. Preserve the external paper's own original author list and DOI in citation intake before specific claims about its proof/measurement are reused.

**Mandatory typed evidence key**: `(source_root, device_model, chip_or_core_id, apparatus_config, experiment_protocol, run_date, control_calibration, raw_observation_id)`. No source key with `device_model=three-qubit_Grover` is automatically equal to one keyed `SXQ128_all_cores`. Likewise `single_core_two_NV` is different from both `16_core_aggregate` and `intercore_quantum_entangler`.

**Pareto discriminator**: A coherent single-core eight-qubit claim requires experimentally sourced eight-qubit operation/entanglement witnesses on one eight-qubit register (not simply capacity arithmetic); a coherent inter-core claim additionally requires a physical quantum link or separately certified entanglement resource. A completed 128-qubit multicore assembly only proves count/parallel orchestration unless its communication/connectivity evidence upgrades the topology. Site-labelled gate operation and time-to-result, with shot count and reconstruction error, are better discriminators than raw advertised qubit totals.

**Theorem integration**: existing #1262's `LocalGate.pairWithinCore` is already scoped to a core; #1269 distinguishes electron/nuclear memories; #1238 provides a simplified NV axial Hamiltonian. Nothing in their finite source proofs proves manufacturer-wide entanglement. This is a source/evidence specification, not a new conditional or kernel-certified theorem, and no CI claim is made.

**Attribution**: mathematical/physical prior art credited to original researchers; independent interview to its publication and quoted speaker; manufacturer announcements to SAXON Q; preexisting DASHI proof/implementation to its own file/PR authors; this source joining/operational discriminator to Johl Brown with OpenAI assistance, 26 October 2026.
