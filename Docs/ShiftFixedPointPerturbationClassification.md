# Shift fixed-point perturbation classification

## Position in the existing dynamics stack

This tranche continues the already-localized finite shift dynamics rather than
opening a parallel formalism.

The dependency path is:

```text
DashiDynamicsShiftInstance
  -> exact held fixed point and strict held-potential descent
ShiftPotentialQuadraticEnergy
  -> finite scalar quadratic-energy descent
DynamicsStepCoherence / DynamicsFixedPointUniqueness
  -> closed iteration and unique finite attractor
DynamicsCollapseDepth / DynamicsCollapseDepthMonotone
  -> exact 2 -> 1 -> 0 collapse depth and strict descent
ShiftCollapseChainMDLCompatibility
  -> pressure-depth/potential chain coordinated with the refined execution
     receipt chain start -> next -> middle -> held
ShiftFixedPointPerturbationClassification
  -> finite relevant / marginal / irrelevant classification
FixedPointCFTBoundary
  -> explicit fail-closed handoff to the still-missing continuum/CFT structure
```

## Earned theorem

On the current three-point pressure carrier:

- `start` is classified as `irrelevant`;
- `next` is classified as `irrelevant`;
- `held` is classified as `marginal` in the exact finite fixed-point sense;
- both irrelevant states strictly decrease the existing held potential;
- the marginal state is fixed by the exact finite step;
- no relevant state is inhabited;
- the existing finite quadratic energy is non-increasing;
- the full execution-side Lyapunov/MDL receipt chain remains attached.

This is the first repo-native perturbation classification actually earned by
the bounded dynamics stack. It is stronger than merely recording a fixed point,
but weaker than a linearized RG or conformal-field-theory theorem.

## Why this is not called a linearization theorem

The current carrier has no tangent space, derivative, normed perturbation
space, or semigroup generator. Calling the exact three-point transition a
linearized flow would erase the main remaining mathematical obligation.

`FixedPointCFTBoundary.agda` therefore records the open gates explicitly:

1. tangent perturbation carrier;
2. derivative or linearized semigroup;
3. scaling-dimension spectrum;
4. operator-product or fusion law;
5. continuum RG control;
6. correlation or conformal Ward control.

Until those are inhabited, the finite classification does not promote a CFT,
continuum RG fixed point, physical scaling spectrum, entropy law, or global
identity between collapse depth, potential, quadratic energy, and MDL.
