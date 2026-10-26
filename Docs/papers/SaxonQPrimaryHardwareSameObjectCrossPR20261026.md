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
