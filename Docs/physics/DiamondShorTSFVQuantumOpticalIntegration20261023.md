# Shor / quantum-computing prior art → TSFV optical interference (2026-10-23)

## Actual repository owners inspected
- `DASHI/Algebra/Quantum/ShorCyclicPhaseAmplitudeQFTExact.agda`: coefficient authority with literal cyclic character phase and finite Fourier sums. More informative than a bare abstract invertible-map QFT, where the identity could satisfy the interface.
- `DASHI/Algebra/Quantum/ShorFiniteVectorAmplitudeRegisterExact.agda`: exponent×target finite coefficient table, typed basis and oracle.
- `DASHI/Crypto/ShorFiniteVectorBornWeightsExact.agda`: squared-norm observation weights over target and exponent, conditioned on an explicit norm authority. Its module comments expressly distinguish TSVF from Shor state carrier.
- `DASHI/Crypto/ShorFiniteVectorBornProbabilityExact.agda`: division interface for normalized weight ratios; this owner expressly does not prove probabilities sum to one.
- `DASHI/Algebra/Quantum/OrdinaryComplexQutrit.agda`, `QutritMatrixGates.agda` and `DASHI/Physics/Foundations/ActionPhaseLiftBoundaryExact.agda`: complex qutrit operators and honest action-to-quantum-phase boundary.

## New implementation
`DASHI/Physics/QuantumSensors/NVShorTSFVCoherentObservationExact.agda` is a reusable finite observation consumer over the *actual Shor phase-coefficient and Born-weight interfaces*. It constructs:
1. Two history/path amplitudes with an explicit cyclic-character phase;
2. coherent amplitude sum and its Born weight;
3. distinguishable-path weight (sum of individual weights);
4. an observation port and proof that equal summed amplitudes yield equal weight/readout.

This is a compositional theorem on the same algebraic authority surfaces, not an embedding of the full Shor factoring circuit into a diamond device. It does not assume the real biological NV paths have cyclic discrete action phases.

`scripts/check_nv_shor_tsfv_fourier_optics.py` provides a concrete normalized 3-point Fourier transform over exact algebraic complex numbers, a coherent equal-amplitude state whose Fourier output has unit detection probability in port 0, and the fully dephased mixture giving 1/3 in that port. This realizes finite interference versus classical mixing with a normalized 3-port Born measurement.

## Relation to experiments and TSFV
Finite quantum Fourier interference is directly meaningful for coherent microwave control, interferometric optical measurements, and distinguishability of photon paths. Real NV fluorescence is driven open-system emission; quantum coherence does not imply that all photon-count components should be combined coherently. A measurement channel must say which paths are indistinguishable, which environment labels are traced out, and which observables record phase. The existing five-state NV Markov generator remains useful for incoherent pumping and shelf kinetics.

TSFV Candidate256 action-mismatch, phase, Gibbs weights, and MDL priors remain separately typed. To claim physical Feynman path integrals from TSFV requires a real-valued action S, a dimensioned Planck constant calibration S/ℏ, a physical path measure, continuum/convergence control, and experimental prediction. Shor's QFT does not automatically supply those requirements.

## Next high-alpha physical cut
Build an instrument model using the existing finite qutrit coherent spin evolution plus classical five-state optical pumping, expressed as a completely positive state update or explicit conditioned instrument. Establish probability normalization and positive readout for a specific calibrated pulse sequence; attach measured NV strain, linewidth and photon collection parameters. Separately extend event-resolved observations to TSFV history-identifiability witnesses with source-attested photon timing data.

## Receipt
New Agda source and Python exact-symbolic assertions committed on PR #1238; no CI, Agda kernel, or independent script execution receipt asserted. All quantum/QFT/Shor physics and mathematics are credited to prior art.
