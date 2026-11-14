# Recent EM PR review — diamond-MCG governed continuation (2026-10-22)

## GitHub PRs inspected

- [#1099](https://github.com/chboishabba/dashi_agda/pull/1099), **Formalise controlled EM–gravitational-wave energy exchange**. Diff contains DASHI/Physics/GR/ControlledEMGravitationalWaveEnergyExchangeExact.agda, ControlledEMGWExchangeFiniteReversalExact.agda, ControlledEMGWEnergyFrequencyPhaseCalibrationExact.agda and calibration/degeneracy modules. They are not ordinary default-branch imports in this cut. No novel gravitational readout is inferred from biomagnetometry.
- [#1163](https://github.com/chboishabba/dashi_agda/pull/1163), **field–geometry–matter conservation and causal transport**. Diff contains FieldGeometryMatter* modules and SameObjectConservationLedgerExact.agda; it is a cross-branch owner for conservation and stress-energy scope, not yet imported.
- [#1217](https://github.com/chboishabba/dashi_agda/pull/1217), **unified 369/C3 TOE realization spine**. Diff includes TOEGaugeQFTGRRealizationExact.agda and TOEGaugeInhabitantsExact.agda; compare its gauge realization receipts before promotion.
- [#1238](https://github.com/chboishabba/dashi_agda/pull/1238), current bioelectromagnetic cut.

## Five-dimensional electromagnetic reading

The historical Kaluza–Klein construction encodes a 4D electromagnetic potential in off-diagonal components of a five-dimensional metric under substantive assumptions. It is not equivalent to adding an observed fifth spatial dimension and does not by itself derive the physiology of cardiac or neural currents.

The new BioEMGaugeFibreBoundaryExact.agda encodes only the **gauge-fibre invariant observation** which a candidate geometric presentation must respect. It does not assert existence of a 5D metric, dimensionally reduced action, cylinder condition, scalar/radion sector, coupling normalization or a physical measurement of extra dimensions. These are distinct open physical obligations.

## New crosspollination acceptance targets

1. Establish exact source ref/head for user-recalled EM-as-fifth-dimension PR and inspect its actual definitions. This review located closely related PRs #1099/#1163/#1217 but did **not** verify a direct fifth-dimensional Kaluza–Klein implementation.
2. If the donor owner provides potential/curvature/gauge transformations, write a concrete adapter to GaugeFieldObservation; prove equality of curvature-derived sensor readout under compatible gauge shifts.
3. Give field to finite NV Hamiltonian coefficient map with physical units and calibrations.
4. For a full 5D theorem, require an explicit metric ansatz, dimensional reduction, connection curvature, Einstein/Maxwell reduction and extra scalar-sector assumptions. Keep these conditional and separate from the biophysics.
5. For EM/GW and antigravity, include background field, RF, vibration, thermal, gradient and apparatus confounders; keep E/B sensor claims separate from metric/gravity claims.

## Status

The gauge-invariance theorem is algebraic and source-written. No Agda kernel check or experimental acceptance receipt attached. This cut adds one generic gauge owner; it does **not** close the complete physical NV optical readout, tissue-volume forward problem, or neural engram intervention model.

## Attribution

Kaluza/Klein geometry, Maxwell theory, NV physics, the cited biology experiments and the research owners of donor PRs retain their original provenance. New DASHI contributions here are scoped adapters and explicit proof obligations, not rediscoveries of established physical laws.
