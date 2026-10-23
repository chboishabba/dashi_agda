# Diamond MCG optics / live KK donor max-cut (2026-10-23)

## Live KK sibling PR #1239 findings

Current PR diff includes `scripts/check_kk_5d_ricci_flat_null_einstein_maxwell.py`, claiming and computing a true nonzero-null-Maxwell five-dimensional Ricci-flat Brinkmann-wave example, unlike the earlier fixed-radius pure magnetic fixture, which fails the vacuum radion equation. It includes `check_kk_coupled_radion_magnetic_5d.py`, `check_kk_variable_radion_5d.py`, `check_kk_magnetic_radion_maxwell_euler_lagrange.py`, and `check_kk_maxwell_first_integral_radion_source.py`. The O(2) signed-framing and Clifford/Pin owner suite is also expanded. This review comes from the actual PR diff, not an inferred master-branch state. The universal 4+1 reduction with analytic field equations and an empirical cardiac current/diamond NV realization remains open.

## Implemented on diamond PR #1238

`DASHI/Physics/QuantumSensors/NVOpticalRateSteadyStateExact.agda` supplies a rational two-population pump/microwave model with explicit inverse-rate witness, finite steady-state populations, normalization and stationary rate-balance proof. It directly produces `NVOpticalPhotonReadoutExact.PopulationReadout`, removing the purely abstract spin-population source for this *specific phenomenological model*.

The rate balance is `dp0/dt = r(1-p0)+W(1-2p0)`, yielding `p0=(r+W)/(r+2W)`. This model omits NV photophysical intersystem crossings, spin-selective shelving and three spin projections. The microscopy literature's ground-state triplet optical cycle is NOT equivalent to two independent states without approximation conditions.

`scripts/check_nv_optical_rate_dynamics.py` includes SymPy steady-state, linear stability eigenvalue `-r-2W`, Lorentzian microwave transition-rate input and predicted fluorescence mean with formal field derivative and conditional Poisson Fisher information.

## Relevant reused cross-pollination

Prior repo optics owners: `OpticalPhenomenaKernelBridge` propagation and approximations, `LitavisSPADMultimodalObservationExact` source-attested detector counting and timestamp architecture, `OpticalSurfaceManufacturingToleranceExact` fabrication/metrology, and `LiMinyongPhotopharmacologyBidiExact` biochemical photoswitches (not NV/opsin mechanisms). Existing `MitopolaritonOptogeneticFactorialExact` is a separate optical intervention and null-additivity context; do not infer wavelength exchange or cell-physiology mechanism from a shared optical formalism.

## Next genuine max-cut / physical gap

1. Real multi-level NV photophysics (microwave Rabi drive, laser pump, triplet excited manifold, singlet shelving, ISC and relaxation) with explicit positive Markov or GKSL generator and solved time/steady-state photon statistics.
2. Actual measured ODMR line shape, axis/strain, detector sensitivity, optical transmission and RF/current-source geometry.
3. Magnetic inverse reconstruction and uncertainty propagation with gradiometer multi-axis observations; biological electromagnetic observables carry real dimensions and boundary conditions.
4. Reconcile canonical KK owner following #1239 merge, and separately attach any 5D physical metric to the same measured 4D field only with a dimensional and empirical reduction witness.
5. Mitochondrial mid-IR spectroscopy source figures, optical heating control, optogenetic perturbation data and a causal interaction test.

Verification: Agda source-written, not kernel checked. CI omitted. Scripts are reproducible symbolic assertions; do not confuse commits with independently executed receipts. Established NV photophysics and classical KK are prior art; attribution is retained.
