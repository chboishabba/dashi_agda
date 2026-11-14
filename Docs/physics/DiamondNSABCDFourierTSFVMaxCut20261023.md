# Navier–Stokes ABCD → finite optical Fourier/TSFV cross-pollination (2026-10-23)

## Actual inspected prior art
- [PR #1091](https://github.com/chboishabba/dashi_agda/pull/1091) is the NS A/B/C/D audit max-cut.
- `DASHI/Physics/Closure/NSABCDMaxCut20261007Exact.agda` explicitly distinguishes A/B physical analytic leaves from C/D released-proof audit.
- `DASHI/Physics/Closure/NSIntegerFourierLattice.agda` supplies exact mode coordinates in Z³, addition and mode closure.
- `DASHI/Physics/Closure/NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact.agda` already PROVES a division-free signed centering identity for a finite family:
  `n*(-sum r_i w_i)+(sum r_i)(sum w_i)=-sum_(i<j)(r_i-r_j)(w_i-w_j)`.
  NS `w_i` is coherent fixed-output *real cross work*, not the Born-positive photon-count weight. Quantitative NS physical rate estimates are separate.

## Concrete integration implemented
`DASHI/Physics/QuantumSensors/NVNSABCDSignedOpticalCovarianceBridgeExact.agda` **imports the actual NS donor** rather than restating the cancellation proof. The finite optical alternative carrier has a FourierMode, a rational damping-rate coefficient, and a *signed interference-work* coefficient. All sums and the pair-difference centering theorem are instantiated directly with the donor functions. An explicit Fourier mode-matching proof field expresses `p+q=k` when a physical realization exists.

`scripts/check_nv_ns_abcd_signed_fourier.py` provides a finite signed-three-path rational audit plus a coherent three-amplitude interference example, highlighting that negative interference *cross terms* can cancel without individual probabilities being negative.

## Correct separation of physics
1. NS periodic Fourier mode Z³ and dissipation rates denote fluid frequencies and energy-work contributions. In diamond optics, analogous coordinate labels and damping exist, but mapping them to physical Maxwell/ODMR propagation requires calibrated units and a common observable definition.
2. Quantum amplitudes add coherently before Born measurement; photon probabilities/intensities are nonnegative. Signed interference-work/covariance terms may be negative. **Do not** identify NS rate-weighted work directly with a photon count probability or a quantum state.
3. TSFV physical path action S/hbar, source-to-mode map, coherence, stationary-phase/asymptotic estimates, and quantum measurement remain separate requirements.
4. Existing Shor cyclic QFT / Born weights and ordinary complex qutrit owners supply *actual* quantum coefficient/measurement machinery. The NS theorem supplies valuable division-free signed cancellation and bookkeeping that complements them, not a replacement.
5. The optical experiment should test distinguishable vs indistinguishable photon histories with SPAD time tags and phase/linewidth/source control; it cannot infer a path integral or neural mechanism merely from observed fluorescence.

## Next genuine highest-alpha work
- Connect `NVShorTSFVCoherentObservationExact` coherent amplitude cross terms to a rational/real signed-work producer with conjugate symmetry. Then instantiate the NS signed centering theorem with actual generated work, rather than arbitrary rational annotations.
- Build physical mode coupling for Maxwell/optical propagation and periodic Fourier carrier with correctly dimensional frequency/wavenumber calibration.
- Derive positive finite evolution of the 5-level NV optical generator; construct a conditioned coherent pulse + incoherent collection instrument; calibrate raw ODMR photon counts.
- Maintain the KK/Einstein–Maxwell sibling results as a separate background source, not an observed optical mode or an automatic NS PDE corollary.

Verification: source-written Agda, unexecuted script in this session, no kernel/CI. Attribution to the NS ABCD donor and quantum-optics prior art.
