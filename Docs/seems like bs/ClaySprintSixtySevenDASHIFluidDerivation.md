# Clay Sprint Sixty Seven DASHI Fluid Derivation

Sprint 67 records the current DASHI fluid-derivation route and its governance
boundary.

## Derivation Target

The target is a fail-closed interface from DASHI carrier dynamics to an
admissible incompressible fluid law:

```text
DASHIToIncompressibleNavierStokes :
  CarrierToContinuumField
  -> CarrierMassConservation
  -> CarrierMomentumConservation
  -> IncompressibilityConstraint
  -> IsotropicDefectDescentLimit
  -> NS equation interface
```

Sprint 67 does not inhabit that theorem. It records the obligations that must
be supplied before the Sprint 64-66 CKN route can be treated as downstream of a
DASHI-derived PDE.

## Contract

Relevant existing formal surfaces:

```text
Kernel.KAlgebra
DASHI.Core.KernelMonoid
DASHI.Core.LensKernel
DASHI.Physics.Closure.NavierStokesWeakSolutionInterface
DASHI.Physics.Closure.NavierStokesRegularityTowerReceipt
DASHI.Physics.Closure.ClaySprintSixtyFourNSSourceBudgetExhaustionCKNRouteReceipt
DASHI.Physics.Closure.ClaySprintSixtyFiveNSPressureReconstructionCKNContractReceipt
DASHI.Physics.Closure.ClaySprintSixtySixNSCKNRSweepCalibrationReceipt
```

The intended order is:

```text
DASHI carrier / kernel / defect principles
-> admissible continuum field interface
-> conservation laws
-> incompressibility constraint
-> pressure as constraint multiplier / projection defect
-> isotropic defect descent as Newtonian viscosity
-> Euler / Navier-Stokes interface
-> vorticity and CKN regularity consumers
```

Sprint 67 records these obligations:

```text
CarrierToVelocityField
CarrierCoarseLimit
NoGhostSupport
FluidLawAdmissibilityInvariant
CarrierMassConservation
ContinuumMassConservation
IncompressibleLimit
CarrierMomentumConservation
AdvectionLimit
PressureAsProjectionDefect
IsotropicDefectDescentLimit
DASHIToIncompressibleNavierStokes
```

## DASHI Results

```text
route_decision = DASHI_FLUID_DERIVATION_CONTRACT_RECORDED
navier_stokes_derived = false
ckn_route_downstream = true
clay_navier_stokes_promoted = false
```

The CKN route from Sprints 64-66 remains downstream: it can only consume a
fluid law after the field interface, pressure projection, and suitable-solution
bridges are supplied.

## Governance

Sprint 67 is a derivation contract and receipt, not a completed derivation.
It does not prove carrier-to-continuum convergence, conservation-to-PDE
passage, pressure multiplier authority, the Laplacian limit, derived
incompressible Navier-Stokes, CKN epsilon regularity, no finite-time blowup, or
Clay/NS promotion.
