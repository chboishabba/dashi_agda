# Kernel admissibility, invariant signatures, and vacuum geometry

## Status

This tranche is a **typed candidate bridge**, not a promoted derivation of general relativity, quantum gravity, or a theory of everything.

It formalizes the shared schema developed across the DASHI discussions:

1. choose a redundancy or admissible transformation pseudogroup;
2. choose the field carrier available at the current kernel depth;
3. cap the allowed local information by finite jet order;
4. build defects/actions only from invariant generators;
5. treat unresolved representatives as invariant-signature non-separation rather than contradiction;
6. use a first-decisive-witness partition only when uniqueness has actually been supplied;
7. keep valuation-saturation/vacuum and residue/curvature language behind explicit promotion gates.

## Existing repo surfaces reused

The new modules deliberately reuse the existing `DASHI.Geometry.SSP369Ultrametric` prefix geometry rather than introducing a second ultrametric spine. `DASHI.Geometry.Admissibility369UltrametricBridge` maps the one-jet and two-jet admissibility rows into finite 369 addresses and inherits the existing self-agreement and zero-self-distance receipts. This bridge does **not** identify the 369 metric with physical spacetime or with a complete p-adic theory.

The implementation also follows the repository-wide proof/bridge distinction documented in the README: typed carriers and exact receipt equalities are proved, while physics-facing interpretations remain candidate-only and fail-closed.

## Modules

### `DASHI.Geometry.AdmissibilityJetSpec`

Defines a kernel-depth specification

```text
DepthAdmissibilitySpec =
  redundancy
  + field carrier
  + jet order
  + invariant generators
  + locality / finite-jet / quotient-first gates
```

Canonical rows are provided for:

- metric + diffeomorphism + two jets;
- abelian one-form connection + one jet;
- non-Abelian principal connection + one jet;
- spinor bundle + one jet;
- two-point bitensor carrier.

No row claims that merely choosing the admissibility data derives Einstein, Yang--Mills, Maxwell, or Dirac dynamics.

### `DASHI.Geometry.InvariantSignatureDecidability`

Formalizes the meaning of “could not decide” at a depth. The current invariant family may fail to separate redundancy orbits. This is represented by an explicit status and a permitted lift, not by forcing binary identification.

A generic `OrbitSeparationWitness` records the exact theorem shape required to promote an invariant family from candidate signature to complete classifier.

### `DASHI.Geometry.Admissibility369UltrametricBridge`

Connects jet depth to the existing prefix ultrametric carrier. It proves only finite carrier facts: depth matching, self-agreement, and zero self-distance.

### `DASHI.Physics.Closure.FirstWitnessVacuumBridge`

Internalizes the Euler/PDA kill-key lesson:

- unique first witness -> exact-once irreversible discharge;
- schedule may alter death time while leaving the final quotient unchanged;
- competing or contextual witnesses are separate lanes and do not inherit commutativity.

The module explicitly blocks the inference that physical vacuum constraints are universally commutative.

### `DASHI.Physics.Closure.ValuationVacuumEinsteinBoundary`

Defines typed carriers for:

- valuation field;
- saturation and residue status;
- candidate valuation-to-metric interfaces;
- saturated-vacuum / Einstein-vacuum candidate;
- residue-energy / curvature-source candidate;
- the final promotion boundary.

The following remain false and must not be inferred from the carrier definitions:

- a Lorentzian metric has been derived;
- the Levi-Civita connection has been derived;
- the Einstein--Hilbert basis has been uniquely selected and varied;
- a covariant conserved stress-energy tensor has been constructed;
- residue defect energy has been proved equal to gravitational mass;
- quantum mechanics and general relativity have been unified;
- a theory of everything has been established.

### `DASHI.Physics.Closure.KernelAdmissibilityVacuumRegression`

Provides a compact import surface proving the intended gates remain in place.

## Precise GR bridge target

The strongest defensible target is conditional:

> Given a smooth manifold, a Lorentzian metric carrier, diffeomorphism invariance, locality, a two-derivative cap, and the required regularity/boundary hypotheses, show that the leading admissible scalar action basis is the cosmological term plus Einstein--Hilbert curvature (up to boundary and dimension-dependent exceptions).

That target is not discharged by this tranche. The present code makes its hypotheses explicit so that a later Lovelock/Einstein--Hilbert uniqueness module can consume them without conflating admissibility selection with physical derivation.

## Quantum / spinor bridge target

The spinor row records the separate prerequisites:

- existence of a spin structure;
- a spinor bundle as field carrier;
- a covariant first-order operator such as the Dirac operator;
- compatibility with the selected metric/connection lane.

Tensor invariants alone are not assumed to distinguish spinorial representatives.

## Next proof obligations

1. A concrete finite-jet invariant algebra for each canonical depth.
2. Orbit-separation or an explicit non-separation theorem for the chosen invariant family.
3. A typed coarse-graining/RG map between depth specifications.
4. A conditional Einstein--Hilbert/Lovelock basis theorem from the metric two-jet row.
5. A spin-structure and Dirac-operator bridge compatible with the metric lane.
6. A covariant action variation producing a divergence-free source carrier.
7. A quantitative empirical or computational model connecting defect observables to measured physics.

Until these are discharged, the correct repository status is: **coherent typed architecture with explicit theorem seams, not a legitimised theory of everything**.
