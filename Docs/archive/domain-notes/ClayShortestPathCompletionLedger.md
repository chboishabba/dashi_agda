# Clay Shortest Path Completion Ledger

This document records the shortest honest route from the current DASHI
state to Clay completion.  It is a completion ledger, not a completion
claim.

## Navier-Stokes

The shortest Clay-facing route is the Navier-Stokes route.  The solved
pieces are the vorticity identity, strain-only stretching, Beltrami null
identity, the Leray/Sobolev scaling obstruction, and the conditional
braid-depletion arithmetic.

ELI5: water has spinning ropes.  Viscosity is soap that smooths the ropes.
The only dangerous move is a rope stretching itself faster than soap can
smooth it.

The live NS gates are:

- `BraidResidueControlsPhysicalStretching`: the trit/braid score must
  actually bound the real vortex-stretching term.
- `DynamicBraidResidueDecayForNS`: actual deterministic Navier-Stokes
  trajectories must lose bad residue across scales.
- `CoherentTubeExclusion`: coherent vortex tubes must be unable to keep
  choosing the bad stretch branch forever.

ELI5: colored traffic lights are not enough.  The traffic-light score must
measure how hard the rope is pulled, and every possible water motion must
be forced to stop choosing red forever.

If those gates close, the conditional path is:

```text
BraidResidueControlsPhysicalStretching
+ DynamicBraidResidueDecayForNS
+ CoherentTubeExclusion / Leray enforcement
=> StretchAbsorption
=> PointwiseEnstrophyControl
=> NoFiniteTimeBlowup
=> GlobalSmoothExistence
=> Clay Navier-Stokes
```

The current code keeps all of those promotion gates false.

## Yang-Mills

The YM route is longer.  The algebraic margin calculation is closed, but
the constructive-QFT route remains open.

ELI5: we know how sticky the block glue must become, but we have not proved
that the real block machine always makes the glue that sticky, nor that the
infinite machine is a real quantum theory with a gap.

The live YM gates are:

- `YMNonperturbativeRGMonotonicity`: the real RG flow must move in the safe
  direction, not just the one-loop diagnostic.
- `ContinuumUniformRhoBound`: the contraction margin must stay uniformly at
  `rho <= 0.90` as the lattice spacing goes to zero.
- `ContinuumUniformLeakageBound`: block-spin leakage must remain uniformly
  summable.
- `HyperbolicShimuraToEuclideanUniversality`: carrier results must transfer
  to flat four-dimensional Euclidean Yang-Mills.
- `SelfAdjointYangMillsHamiltonian`: the Hamiltonian must be a real
  self-adjoint operator.
- `MassGapSurvivesContinuumLimit`: the positive spectral gap must not
  collapse in the continuum limit.
- `OSWightmanReconstruction`: Euclidean data must reconstruct a standard
  Wightman QFT.
- `Nontrivial4DSU3YangMills`: the resulting theory must be interacting
  SU(3), not a trivial theory.

The shortest YM path is:

```text
YMNonperturbativeRGMonotonicity
+ ContinuumUniformRhoBound
+ ContinuumUniformLeakageBound
=> YMBalabanContinuumLimitWithUsableMargin
=> HyperbolicShimuraToEuclideanUniversality
=> SelfAdjointYangMillsHamiltonian
=> MassGapSurvivesContinuumLimit
=> OSWightmanReconstruction
=> Nontrivial4DSU3YangMills
=> Clay Yang-Mills
```

The current code keeps all YM promotion gates false.

## Boundary

This ledger implements the current shortest-path map.  It does not solve
Clay.  It records the exact hard lemmas that would be required to solve
Clay from the current repo state.
