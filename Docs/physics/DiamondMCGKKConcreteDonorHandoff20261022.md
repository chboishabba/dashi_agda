# Concrete KK donor integration into diamond bioEM PR #1238

## Executed max-cut (22 October 2026)

PR #1239's `DASHI/Physics/Electromagnetism/KaluzaKleinGaugeShiftExact.agda` was copied verbatim from the current PR diff into PR #1238's branch with original file/module attribution preserved. This introduces a real imported theorem owner, replacing the earlier cross-branch-only contract.

`DASHI/Physics/Measurement/BioEMKaluzaDonorAdapterExact.agda` instantiates the existing `LocalKKConnection` consumer from PR #1239's `KK.Gauge` module, then transports its proved horizontal one-form invariance through arbitrary magnetic and frequency observations via the donor's `gaugeInvariantUnderObservable`.

**Donor credit:** PR #1239, 'C3/369: exact alternating nine-site braid and Borromean closure audit'. This is exact reuse rather than independent derivation. Once branches are merged, reconcile identical vendor copies by retaining one canonical module.

## Outcome and honest boundary

The former practical missing-import blockage is discharged on this branch at the source level. An actual concrete additive group inhabitant must still be supplied for a numerical electromagnetic potential. The adapter is parametric in a valid `KK.AdditiveGroup`, which is mathematically appropriate for 1-form coefficient groups.

No 5D metric, 5D Levi-Civita connection, dimensional reduction, Ricci scalar calculation, physical Maxwell derivation, biological Maxwell field-solution, NV optical readout or numerical spectroscopy is proved by this gauge transport. Gauge symmetry is necessary but insufficient for physical equivalence.

## Next physics and evidence obligations by alpha

1. Concrete physical 4D form carrier and exterior derivative with `d²=0`, curvature `F=dA` and measurable magnetic projection, coherent units and boundary conditions.
2. Correctly assembled 4+1 metric block, determinant/inverse, patch transition cocycles and Ricci reduction (the donor Python 2+1 symbolic check is only a toy representative).
3. Quantitative cardiac/neural current fields, conductivity and sensor position, error-certified forward transfer into NV axial response.
4. Density-matrix/POVM NV optical dynamics and source-backed actual photocount/noise model.
5. Mitochondrial coupled-mode spectral discrimination and optogenetic causal outcomes with proper controls; no SSP prime selection after the fact.

## Verification and governance

CI intentionally omitted at user request. No kernel execution receipt is attached. Statements remain source-written; separate prior authors' physical theories, source measurements and new adapter proofs.
