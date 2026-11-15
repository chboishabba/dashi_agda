# BioEM/KK max-cut follow-up — 2026-10-22

## Live donor review
Read current diff of [Agda PR #1239](https://github.com/chboishabba/dashi_agda/pull/1239). It now includes `C3ContinuousFramingObservationBoundaryExact.agda`, `C3BraidFramingInformationLossExact.agda`, `C3NineSiteSixStepMirrorExact.agda`, and the Möbius endpoint framing material, in addition to its earlier local KK gauge proof and 2+1 symbolic metric script. The *KK additive gauge module itself* in this inspected diff remains the previously imported owner. Do not claim a newly available full Einstein–Maxwell dimensional-reduction theorem.

## New implemented source-bearing chain
`DASHI/Physics/QuantumSensors/NVDiscreteGaugeCurvatureBridgeExact.agda` supplies a single concrete finite chain:
1. Triangle potential `A` with vertex gauge transform `A' = A + d chi`.
2. Exact discrete curvature `F = dA`, with `F' = F` from the earlier `BioEMDiscreteCurvatureGaugeExact` proof.
3. Affine sensor-axis field coefficient `B = gain * F + background`.
4. `NV.axial-nv(D,gamma,B)` into existing rational spin-1 model.
5. `R.predictODMR` symbolic labelled transition-frequency data.
6. `fieldGaugeInvariant` and `resonanceGaugeInvariant` are provided by congruence over the discrete gauge theorem.

This bridges two previous finite models into one concrete *gauge-to-quantum-frequency* observable. The physical meaning of its triangle flux and the conversion gain are not derived; they require independent calibrated geometry and units.

## Framing and winding boundary
The newest #1239 module demonstrates a finite no-go for recovering an unwrapped integer turn count from terminal site observation. In physical sensing, a fixed NV axis projects B and cannot determine arbitrary three-dimensional orientation, ribbon framing or full C3 braid homotopy from one scalar time point. Reconstructive claims need additional vector sensors, moving geometry/time history and frame transport.

## Physical proof gates still genuinely open
- 4+1 circle metric patching, Levi-Civita/Ricci scalar and Einstein–Maxwell with scalar branch.
- Smooth 4D EM exterior curvature, Hodge dual/B projection and a conductivity-current boundary-value solution, including units.
- Full complex spin-1 NV Hamiltonian and physical microwave/optical dynamics, measured-photon likelihood and noise.
- A valid approximation/identification map from cardiac or neural source currents to this finite triangle/cochain or Fourier surrogate.
- Actual experimental source data, error receipts, identifiability restrictions and spectral/optogenetic counterfactuals.
- Typed *same object* relation between C3 framed braid coordinates and a physical KK fibre; analogy alone is not transport.

## Reuse and verification
Original KK group theorem from sibling PR #1239 was imported on this branch in prior round and consumed by the BioEMKaluzaDonorAdapterExact module. This round does not duplicate it. CI deliberately omitted; Agda exact-head kernel type-checking not performed, hence source-written proofs are not certified.
