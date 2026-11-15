# YM 369 / NS ABCD / Shor Fourier / TSFV / NV optics — 2026-10-24

## Repo prior art inspected (actual owner interfaces)
- `DASHI/Core/ThreeChannelC3EquivarianceGateExact.agda` owns `OrderThreeAction` and `EquivariantMap`; matching three channels is not enough without an intertwiner.
- `DASHI/Physics/YangMills/BalabanCMP109SpatialC3ActionExact.agda` recovers a physically aligned three-spatial-coordinate C3 on the CMP109 grid; an unrelated index-cycle must not be equated to that grid action without a map.
- `DASHI/Physics/YangMills/SU2Bracket369OrientationBridgeExact.agda` identifies su(2) quaternion bracket as twice the cross-product on 3 axes, and keeps YM/EM/NS mechanism identifications explicitly false.
- `DASHI/Physics/YangMills/BalabanC3MonsterEquivarianceAuditExact.agda` distinguishes actual classical C3 curvature and stress symmetries from selected nonlinear source identification remaining outstanding.
- `DASHI/Physics/Closure/NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact.agda` owns the *proved* division-free finite signed covariance identity used here.
- `DASHI/Algebra/Quantum/ShorCyclicPhaseAmplitudeQFTExact.agda` and `DASHI/Crypto/ShorFiniteVectorBornWeightsExact.agda` own actual cyclic phases and norm-squared weights; `TSFVActionPhaseWeightSeparationExact` keeps structural actions, physical quantum phases and Gibbs weights distinct.

## Concrete implementation
1. `DASHI/Physics/QuantumSensors/NVYM369C3OpticalFourierExact.agda`: a literal 3-channel optical C3 permutation satisfying rotate³=id, exact sum/intensity invariance, and a checked-by-construction equivariant map to a trivial scalar action. Retains original Balaban physical grid C3 as a separate source owner. No map equating the two is assumed.
2. `DASHI/Physics/QuantumSensors/NVYMC3SignedInterferenceWorkExact.agda`: extracts signed optical pair-interference work `w_ij=2*a_i*a_j` from rational real amplitudes, and directly applies the pre-existing NS division-free covariance theorem to these actual generated terms, not arbitrary assigned work parameters.
3. `scripts/check_nv_ym369_c3_ns_signed_work.py`: SymPy tests for C3 cyclic and intensity invariance, cyclic covariance of three interference cross terms, exact amplitude squared decomposition, and NS signed covariance.

## Limits / highest-alpha next cut
- Real rational amplitudes are an elementary slice. Genuine 3-dimensional complex cyclic Shor QFT phase and Born squared norms need a **same-object** complex optical producer and phase-calibrated physical realization. General coherent optical paths have complex conjugate pair cross terms, not merely `2ab`.
- Optical/detector dynamics and the measured human MCG experiment require actual state preparation, physical NV Hamiltonian pulse model, collection optics, photon likelihood, and biological field calibration.
- NS shell estimates, YM continuum mass-gap arguments, the 5D KK vacuum examples, and TSFV Candidate256 nonseparable transition kernel cannot be inferred from the above shared finite identities.
- Physical YM C3 generated-action/source transport is not supplied by the optical indexing; no phenomenological claim about Monster/369 physics is made.
- The next *mathematical* cut is an exact 3-channel complex/Hermitian amplitude pair-work producer feeding this NS theorem and the Shor Born measurement on the identical coefficient carrier.
- The next *physical* cut is a calibrated phase-sensitive optical or NV spin experiment with explicit measurement instrument and time-dependent noise source.

## Receipt
Agda changes committed, no CI or Agda kernel run. Checker source committed; unless an independently executed result is attached, no symbolic execution receipt is asserted.
