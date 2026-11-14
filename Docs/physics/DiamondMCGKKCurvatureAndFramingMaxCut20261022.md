# BioEM KK curvature and C3 framing follow-up, 2026-10-22

## Live sibling discovery
PR #1239 has advanced beyond its original local KK one-form gauge identity:
- `DASHI/Foundations/C3ContinuousFramingObservationBoundaryExact.agda` distinguishes an unwrapped winding/twist state from a terminal position/phase observation and supplies a counterexample to endpoint recovery.
- `DASHI/Foundations/C3BraidFramingInformationLossExact.agda` and six-step-mirror modules separate positional trajectories from frame/normal-bundle information.
- KK additive gauge module remains the same in the inspected diff. Its representative circle metric script remains a 2+1 algebraic fixture, **not** a 4+1 Einstein–Maxwell reduction.

## New PR #1238 contribution
`DASHI/Physics/Measurement/BioEMDiscreteCurvatureGaugeExact.agda` instantiates a finite discrete exterior-coboundary model on an oriented triangle, with edge potentials, vertex gauge values, exactly gauge-invariant triangle flux (d²=0), and an affine flux-to-sensor readout with invariant output. This is a concrete curvature calculation rather than an abstract equality-transport interface.

The new gauge shift is the oriented edge coboundary of vertex potential; the sum around 0→1→2→0 cancels algebraically. It is an exact finite analogue of F=dA, not a continuous electromagnetic field strength or proof of Maxwell's equations.

## Relevance of framing to optical/biomagnetic sensing
A sensor-axis or endpoint position is not sufficient to recover the total twist/winding of a framed trajectory. Any physical comparison with NV magnetometry needs calibrated *sensor orientations along time*, and any KK connection holonomy claim needs a concrete smooth connection, a lifted path and transport law. An unwrapped phase and a measured scalar B projection are different observables; do not conflate them.

## Next max-cut, physical rather than CI
1. Instantiate KK on concrete rational edge cochains and prove its `dy + kA` connection update is compatible with the explicit triangle gauge change (with the scale conventions).
2. Construct the 4D smooth exterior derivative, field 2-form, Hodge magnetic projection and calibrated sensor geometry with units.
3. Introduce full spin-1 Hermitian matrices and photon ODMR likelihood; close positivity/normalization independently of fitted data.
4. Model tissue conductivity and cardiac / neural current sources quantitatively.
5. Only then integrate 5D metric curvature/Ricci and physical Einstein–Maxwell reduction, using donor #1235 Hopf/U1 and #1239 gauge owners.
6. Keep mitochondrial 71 THz numerical Ogg coincidence in a dimensionless-preregistered hypothesis lane, separate from spectral mechanism evidence.

## Status
Source-written Agda; not kernel checked. User asked to skip CI. No claim of physiological detection, new gravity, recovered ribbon twist or experimentally observed extra dimensions.
