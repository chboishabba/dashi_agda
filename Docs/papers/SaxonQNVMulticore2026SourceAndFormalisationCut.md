# SAXON Q NV-diamond multicore: source/audit/formalisation cut (2026-10-26)

## Attribution and claim classes

- Primary **experimental** source: Sebastian Gemsheim, Fabian Klüpfel, Max Kneiß, Nicole Raatz, Tobias Herzig, Matthias Mendt, Evgeny Kreissig, Ulrike Rückert, Albrecht Hänel, Jan Meijer, and Marius Grundmann, *Grover Search with Semiconductor Spin Qubits at Ambient Conditions*, arXiv:2609.13022 (2026), https://arxiv.org/abs/2609.13022 . Credit the experiment to its listed authors. It concerns a three-nuclear-spin-qubit search register, NOT an SXQ128 experiment.
- Primary **architecture / manufacturer's technical account**: Max Kneiß, Sebastian Gemsheim and Marius Grundmann, *The SAXON Q QC2026 Dual Core Quantum Computer*, listed at https://www.saxonq.com/whitepapers/ ; and SAXON Q, *Where are we with Quantum Computing in 2026?*, https://www.saxonq.com/wp-content/uploads/2026/04/SaxonQ-Whitpaper-QC2026-web.pdf . Credit these statements to the authors/manufacturer, not to external reviewers.
- Manufacturer **sales/roadmap assertion**: SAXON Q, August 2026 128/512 offer, https://www.saxonq.com/news/orders-for-128-qubit-512-qubit-room-temperature-quantum-computers-open/ . 128 = 16 cores × 8 qubits; 512 = 32 cores × 16 qubits. Orders/orderability is not an independent demonstration of every operating core and is not proof of a coherent 128-/512-qubit register.
- **External journalistic challenge and interview**: https://www.supercomputing.news/quantum/saxonq-sxq128-coupled-nv-room-temperature-quantum (27 July 2026); keep interview testimony attributed, not promoted to instrument traces.
- **Formalisation/adaptation/analysis**: Johl Brown and OpenAI assistant, 2026-10-26. No assignment of new research findings or formalisation to the named experimental authors. Follow repository-wide attribution and evidence-promotion policies.

## Two orthogonal hardware dimensions

Represent a machine by (core count K, physical/logical register size per core n_i, inter-core link type L, allowed operations G, calibrated noise/latency E). Report **aggregate occupancy** N = Σ_i n_i separately from **native connected quantum width** W = max_i n_i when L is *classical only*. For SXQ128 claims: (K=16, n_i=8, N=128, W<=8) conditional on the vendor architecture being realised as described; SXQ512 (32,16,512,W<=16).

A **classical link** transports classical bits and instructions, not coherent superpositions. For disjoint cores A,B with only local CPTP maps plus classical messaging (LOCC), initially separable inputs remain separable across A|B. This does not prohibit within-core entanglement, shared classical randomness, independent parallel sampling, or simulated >W-qubit observables reconstructed via circuit cutting. It *does* prohibit promoting N to a single coherent physical register without an explicit quantum interconnect/entanglement-resource witness.

Formal boundary: for every separable ρ_AB = Σ_j p_j ρ_A,j ⊗ ρ_B,j and every finite LOCC protocol Λ, Λ(ρ_AB) is separable across A|B. Hypotheses explicitly require no pre-shared entangled resource. A circuit-cutting estimator can reconstruct a global expectation using multiple runs and classical coefficients; this is NOT physically enacting the global coherent gate.

## Paper-specific proof obligations (do not claim discharged)

1. **NV center:** crystal defect, spin-1 ground manifold, nitrogen nuclear spin-1, optional nearby 13C nuclear spin-1/2. Link site/symmetry/spin formalism via typed maps only; physical carrier is not automatically a computational qubit.
2. **Logical encoding:** define orthonormal selected m-sublevels and isometry V:C²→C³; prove V†V=I₂ and projection VV†; separately track leakage out of range(V).
3. **Pulse model:** NV Hamiltonian H= D S_z² + γ_e B·S + S·A_N·I_N + Σ_C S·A_C·I_C + H_drive(t) with coefficients/calibrations source-bound. Derive a unitary/channel from time evolution; show pulse-to-logical-gate relation up to phase and error. Do not invent device values.
4. **Grover ideal reference:** for N=8, m=1 and r=2 the ideal P=121/128; for m=2,r=1 P=1. Compare only like-with-like experimental search distributions, not whole-device gate fidelity.
5. **Readout:** include preparation, measurement confusion matrix, binomial sampling uncertainty, experimental shots and corrections; reconstruct only when original artifact exists.
6. **Core count:** formalise sum of per-core capacities; prove width boundary conditional on classical-only connectivity.
7. **Cutting:** define boundary cut size c, quasi-probability decomposition coefficients a_s, expectation estimator Σ_s a_s E_s; derive unbiasedness if every term is estimated unbiasedly, plus variance Σ_s a_s² Var(E_s) under independent sampling. No universal numerical overhead without cut coefficients, circuit family and shots.
8. **Benchmarks:** compare at equal task, success/accuracy, device boundary and time/energy; separate one-qubit, two-qubit, algorithm success and full-stack times.
9. **Physical authority:** manufacturer's claim -> paper/trace -> calibrated same-device artifact -> independent replication; no promotion by analogy or successful typechecking.

## Existing repository reuse map

- Inspect latest PR heads for spin-1, C3/diamond symmetry, nuclear spin and qubit embedding, Grover/circuit machinery, parallel/LOCC/information causal boundaries, experimental evidence receipts and proof-search. This note is a cross-PR integration surface, *not* proof these imports are available on master.
- Existing `DASHI/Foundations/Base369BinaryTernaryRefinement.agda` provides a conceptual source for retaining information across ternary→binary projections. **Do not conflate** that encoding with spin-1→spin-1/2 logical selection.
- `DASHI/Unified/GRQuantumProofAdapters.agda` and GRQuantum proof/evidence documentation: reuse their typed proof-vs-empirical policy, not imply empirical validation of a SAXON Q device.
- Sibling quantum simulator and crystal-symmetry branches are integration candidates after file/commit exactness is established.

## Max-cut dependency DAG

**A** verify manufacturer's core description and primary provenance (done, as dated text) → **B** mathematical N/W and classical-link theorem → **C** source-specific pulse/isometry and Grover proofs → **D** full calibration/observable trace join → **E** cross-core cutting benchmark with uncertainty → **F** independent hardware replication. A does not imply B–F; B and ideal Grover can be checked independent of C–F.

## Falsifiable discriminators

- Prepare Bell pair spanning cores, demonstrate joint phase-sensitive correlators and Bell violation under controlled closure of loopholes, or document quantum link/preshared entanglement. Absence maintains classical-only classification.
- Publish a complete SXQ128 component/core inventory and same-system randomized benchmark receipts, not just purchase availability or one-core extrapolations.
- For a family of increasing cross-core cuts, measure wall-clock, sampling budget, estimator variance, fidelity and CPU recombination costs against direct classical methods and equal-accuracy single-register systems.

**Status:** Documentary/source and ideal mathematical assertions only in this cut. No physical or kernel certification from this Markdown file; no independent replication claimed.


## 2026-10-26 corrective audit: same-day PRs (supersedes generic gap claims above)

The earlier roadmap overstated missing infrastructure because it inspected only default-branch results. The following **actual PR branch files** were inspected via GitHub and are established reusable implementation, not speculative future work:

- dashi_agda **PR #1262**, branch `feat/nv-spin1-multicore-adapter-20261026`: `DASHI/Algebra/Quantum/NVSpinOneMulticoreAdapter.agda` imports pre-existing `DASHI.Physics.QFT.NonAbelianFusionFromSpin` and `DASHI.Algebra.Quantum.DASHIQuantumBridge`. It proves `nvElectronCarrierDimensionIsThree` by `refl`, defines Fin 16 cores × Fin 8 sites, same-core addressing for `pairWithinCore`, and an adapter parameterised over `CertifiedQuantumBridge`. Its source comment explicitly declines to infer physical fidelity or inter-core entanglement.
- PR #1262 `DASHI/Algebra/Quantum/NVSpinOneC3HamiltonianObstructionExact.agda`, `NVSpinOneC3ChartAdapter.agda`, and `NVSpinOneFiniteSUSYFactorisationExact.agda`: finite C3 chart, non-invariance of symbolic Sz² under cyclic relabelling, finite SUSY-QM supercharge, **not** physical SUSY or quantum hardware calibration. Source: `Docs/roadmaps/NVSpinOneC3CrossPRMaxCut20261026.md` on the branch.
- dashi_agda **PR #1269**, branch `feat/nv-mcg-same-object-weld-20261026`: `DASHI/Physics/QuantumSensors/NVMCGQuantumComputingSameObjectWeldExact.agda` imports existing `DASHI.Algebra.Quantum.FiniteQutrit`, `DASHI.Physics.QuantumSensors.NVSpinOneAxialExact` and `FiniteC3OrbitStabilizerExact`, proves label/ket inverse maps, axial spin energy symmetry under field reversal, and zero-field ±1 spectral exchange. Actual Hamiltonian is **axial symbolic**, not a complete sourced NV laboratory pulse Hamiltonian. This PR explicitly says the #1262 and #1269 surfaces are independent pending stacked merge.
- dashi_agda **PR #1261** has `DASHI/Mathematics/Symmetry/DiamondNVFourAxisPermutationExact.agda` and `DiamondTernary111AxisBridgeExact.agda` as well as crystallography/C3/ternary contexts. They are typed geometric carriers, not evidence that a diamond NV control system implements every abstract action.
- dashi_lean4 **PR #76** (quantum mereology, partial trace/g-TPS) and **#85** (channel/superselection machinery) were identified by the #1262 authors as possible reuse; do not claim inspected code/branch imports here.
- dashiQ PRs **#2** (MDL promotion) and **#3** (experiment receipt) likewise referenced by #1262's provenance audit, not checked or merged by this branch.

**Amended cut:** do *not* implement fresh SpinIrrep, finite qutrit, NV axial Hamiltonian, 16×8 gate address or general certified quantum bridge. The new paper-specific work is a same-object witness relating (a) the manufacturer's sourced machine/version/core and (b) the measured Grover device/register to the correct existing modules, plus actual laboratory control pulse/channel, logical NV nuclear register encoding, calibration, measured probability reconstruction and proof of an instantiated compiler. With manufacturer's classical-only cross-core communication, LOCC/separability and circuit-cutting error budgeting are still distinct unless confirmed in corresponding existing PR proof files.

**Integration restriction:** Avoid import from a different unmerged PR branch as though it were already on `master`; either stack branch bases with a verified merge, or retain external correspondence references. This PR adds no duplicate Agda source file and makes no typecheck or hardware validation claim. The exact-Python fixture is an optional independent ideal-model regression, not a replacement for existing computer/quantum kernels.

Provenance: original experimental authors and manufacturer's authored whitepaper retain authorship for their work. The branch discovery, corrected reuse map and formalisation linkage are credited to Johl Brown and OpenAI assistant (2026-10-26). A mere source mention, prior PR title, or model inspection is not a new empirical receipt.


## 2026-10-26 executable regression correction and paper-specific limits

The initial `check_saxonq_multicore_grover_ideal.py` called a success-probability bound a "full 8-outcome normalization" test. That description was too strong. The regression now verifies the complete exact normalization invariant
`m*a_good**2 + (8-m)*a_bad**2 == 8` for m=1..8, steps=0..4, with amplitudes scaled by sqrt(8), and directly enumerates all eight distinct singleton oracle markings using the full 8-entry amplitude vector. Forty normalization cases and eight target-oracle checks were reproduced locally in Python 3 using Fraction. This is a **finite ideal Grover** receipt only, not a pulse-level or device-level validation. No Agda compiler is installed in the local execution environment, so a kernel check of the Agda logical encoding is still required.

Proof boundary refinement: `SaxonQFiniteQutritLogicalEncodingExact.agda` uses *pre-existing* `FiniteQutrit` and `Dirac` for two basis states and leakage classification. It is finite **basis-level** encoding, not `C² → C³` as a full complex-linear isometry: construction of the latter must import the existing concrete scalar/vector or Hilbert implementation. Its canonical basis choice is deliberately not attributed to the experimental device without matching the published `m_I` lab convention. Device-scale core width is also architectural, not a new empirical theorem; a classical-only cross-core channel preserves separability absent a preshared entangled resource.

Attribution: ideal Grover and circuit invariants are standard prior mathematical art (Grover's search, 1996; https://doi.org/10.1145/237814.237866); the reported laboratory data are Gemsheim et al. (2026), https://arxiv.org/abs/2609.13022; original existing DASHI modules retain repository provenance; correction/test adaptation by Johl Brown and OpenAI assistant, 26 October 2026. Do not conflate the 2026 manufacturer product roadmaps with the authors' experimentally implemented three-qubit instance.


## 2026-10-26 circuit-cutting algebraic regression

`scripts/check_saxonq_circuit_cutting_exact.py` (commit `50e0b56d`) provides exact-Fraction receipts for (a) signed weighted expectation reconstruction, (b) the **independent** estimator variance identity, (c) 81 finite distributivity checks for the product of two local linear sums, and (d) a same-shot covariance counterexample proving the independent formula cannot be used for correlated estimators. The model does not assume that a manufacturer physically supplies a cross-core entangler or has implemented the particular decomposition, and establishes no bounded end-to-end runtime or energy advantage.

Local reproduction of the 81 distributivity cases, variance and covariance identities passed under Python 3; the full committed source has not been executed as a file in this environment. The first version of the tensor-product test erroneously compared an inner product to a four-term product expansion; corrected in commit `50e0b56d` before this receipt. This correction is recorded as part of the revisable knowledge trail, not erased.

Provenance: mathematical identities are standard linear algebra and probability; experiment by Gemsheim et al. (arXiv:2609.13022); manufacturer core topology claims by SAXON Q; exact regression adaptation and correction by Johl Brown and OpenAI assistant, 2026-10-26. The path from these identities to an SXQ128 instrument is **not proven**.


## 2026-10-26 no-duplication cross-PR gate (additional cut)

A redundant `SaxonQFiniteCoreAddressExact.agda` was briefly introduced at commit `8b1d3923`, then **deleted** at `fe9a2ef9` in the same branch because PR #1262 already owns `Core=Fin 16`, `Site=Fin 8`, `Address`, and `LocalGate.pairWithinCore`. No duplicate local-gate definitions should persist in this PR. The correction is retained for accountability.

Exact dependency ownership, confirmed from the changing file lists at the PR heads:
- **#1262**: NVSpinOneMulticoreAdapter, C3 chart/Hamiltonian obstruction, finite SUSY factorisation.
- **#1269**: NVMCGQuantumComputingSameObjectWeldExact, NV photon two-shot/history, Bayesian and readout identifiability surfaces.
- **#1261**: DiamondNVFourAxisPermutationExact and DiamondTernary111AxisBridgeExact.
- **#1270**: limited candidate spin-one→logical basis retraction, ideal Grover and exact circuit-cutting regressions, and attributed source/evidence ledger.

For a **stacked merge**, import #1262's actual `NVSpinOneMulticoreAdapter.Address` and `LocalGate` as canonical; do not declare replacements. Consume #1269's `labelToKet`/`ketToLabel` bijection and `axialSwapFieldReversal` (source-specific real spectral results) only after dependency commit alignment. The #1269 branch explicitly warns that the other PR is not merged; therefore imports in #1270 currently remain **unresolved cross-branch obligations** and a documentation pointer is *not* an implementation of their composition.

**Readout seam has advanced in #1269**: `NVPhotonHistoryCountSufficiencyExact.agda`, `NVPhotonPascalCountClassesExact.agda`, and `scripts/check_nv_photon_count_class_bounds_exact.py` were present at this audit, in addition to previously listed two-shot kernels. Do not implement a duplicate generic photon likelihood. The genuinely source-specific tasks are calibrating its parameters, mapping the measured detector protocol to the paper's count/histogram, and obtaining source-authenticated raw count data.

**Formal theorem boundary**: a finite ket-label retraction is weaker than a Hilbert-space isometry; a 16×8 namespace is weaker than a connected register; an ideal Grover success identity is weaker than a device pulse compilation theorem; and a signed classical cutting sum is weaker than a calibrated multicore speedup. No experimental data, proof authority, authorship or peer-review status is promoted by these correspondences.

Attribution: underlying spin representation, quantum bridge, C3, qutrit, diamond crystal and photon readout developments retain their original module/PR origin and their original cited mathematical authors. Grover reference: L. K. Grover (1996), DOI 10.1145/237814.237866. Gemsheim et al. (2026) receive attribution for their experiment; SAXON Q for vendor architectural/product assertions; identification of reuse obligations and correction here is an adaptation by Johl Brown with OpenAI assistance, 26 October 2026.
