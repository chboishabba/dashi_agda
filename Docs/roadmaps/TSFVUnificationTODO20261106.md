# #1460 unification TODO — Pareto source construction and fail-closed acceptance

**Canonical:** [186 exact P00–P11 lemma IDs](Emergent31QuantumYMKKExactLemmaRoadmap20261103.md). **Executable:** [48 deliverables / five phases](TSFVUnificationExecutionPhasesDeliverablesExactLemmas20261106.md). This is our lane only; do not mutate #1444 YM-owned science.

## Actually completed source and integration work this round

- [x] Reconcile #1444 physical-cube PCUBE/CMP116 donor into #1460 through [#1470](https://github.com/chboishabba/dashi_agda/pull/1470), merge SHA `1f71c1d58cc2d231a0fdc42c50b0c9969d35e49b`. Pin donor source head; later parent updates require a new sync.
- [x] Source-write `TSFVAcousticLocalImpulseThirdDerivativeExact`, actual selected nearest-neighbour kick (q'''(0)=-L\delta_0), all six first-neighbour response coefficient (c^2/a^2), outside-first-ball zero and mass blindness.
- [x] Source-write `TSFVAcousticMassInverseBidiNoGoExact`; selected (3,1) principal does not identify mass, whereas complete frequency response determines squared mass at the zero Fourier point.
- [x] Import/export both from original child `DASHI.Unified.TSFVUnifiedRegression`, preserving separate YM and TSVF/KK/OS owner roots.
- [x] Execute 2,764 equivalent exact Fraction checks of coupling/response/mass inverse BIDI; commit `scripts/check_tsfv_acoustic_impulse_mass_bidi_20261106.py`. This is a reference, NOT Agda.
- [x] Preserve 186 canonical IDs + 186 status entries; write 48-task five-phase execution crosswalk to 101 original canonical lemma IDs, inspect all IDs against the live original ledger.
- [x] Implement `scripts/run_tsfv_unification_maxcut_20261106.sh`, Nix-aligned `--safe` source proof candidates, original YM/TSVF/combined roots, and CI source/reference/48-ledger checks.

## Exact remaining physical max-cut (do not mark complete)

- [ ] **S01** physically selected original microscopic TSVF pointer/environment with actual Born/ABL/non-signalling recorded observables (O01–O04).
- [ ] **S02** measured observer-local retarded response on the ORIGINAL source; the chosen oscillator impulse is only a control (O05–O06).
- [ ] **S03** independently produce a dimension-four continuum and a causal interval-volume estimate rather than assuming a cubic spatial graph (O07–O08).
- [ ] **S04** construct original hyperbolic propagator/null cone, unique selected timelike axis and calibrated spatial principal quadratic (O09–O12).
- [ ] **S08** genuinely complete and noncollapsed original complex observer Hilbert, Stone group, dense invariant core and self-adjoint Hamiltonian (H01–H05).
- [ ] **S09** source-state-preserving onto unitary from observer Hilbert to physically reconstructed YM/OS Hilbert; actual same H/domain, spectral projections, real/imaginary-time continuation and Wilson observables (H06–H12, B07). S07 original physical OS producer remains #1444 worker dependency.
- [ ] **S05** actual selected positive-radius smooth five-dimensional Einstein–gauge–matter action/solution, nonzero source stress or controlled matter-free scope, scalar/radion dynamics and KK modes (K01–K06).
- [ ] **S06** horizontal reduction equals the **independently measured** original observer metric, with observable/field/stress calibration and limits (K07–K09).
- [ ] **S10** full reverse/forward same-source BIDI, noninjectivity controls, cutoff/volume/history/KK limit commutation and quantitative comparisons (B01–B08).
- [ ] **S11** actual pinned-head Agda compiler and zero-meta/transitive trust reports, independent analytic proofs and physical measurement receipts (V01–V06). GitHub Actions has reported no runs for the #1460 branch; a workflow file is not acceptance.
- [ ] **Parent synchronization** on future #1444 commits: compare pinned donor head and repeat conflict-aware parent→child integration, never child→parent without independent YM owner's review.

**Required command on clone/Nix:** `nix develop .# --command bash scripts/run_tsfv_unification_maxcut_20261106.sh`. All files above have source GitHub readback but no actual Agda compiler receipt in this turn. The terminal full E1 theorem and Clay endpoint remain OPEN.
