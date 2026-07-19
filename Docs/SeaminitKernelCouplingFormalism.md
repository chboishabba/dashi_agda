# Seaminit / DASHI-ROM kernel coupling

This document freezes the minimal formal contract for fast body-support design.

## State spaces

- `BodyGeometry` supplies a fixed-topology rest mesh and a pose-indexed deformation map.
- `ROMKernel` supplies pose features, pose admissibility, motion paths, and a path-dependent load cocycle.
- `FabricKernel` supplies material features and material admissibility.
- `BodyBasis` supplies one low-rank coefficient space shared by every body field.

The body basis is defined once on the stable vertex identity of the template mesh. Runtime fields are reconstructed by projection from coefficients rather than recomputed as independent full-resolution simulations.

## Coupling law

The coefficient engine separates three contributions:

```text
z(q,p) = combine3(
  poseOnly(phi(q)),
  fabricOnly(eta(p)),
  interaction(phi(q), eta(p)))
```

This is the typed form of the ROM × fabric × body coupling. The interaction term is first-class: material effects are not assumed independent of pose.

## Shared field basis

Tension, pressure, shear, and support have distinct coefficient maps but share the same projector:

```text
T(q,p)       = B0 tensionCoeff(q,p)
P(q,p)       = B0 pressureCoeff(q,p)
S(q,p)       = B0 shearCoeff(q,p)
Support(q,p) = B0 supportCoeff(q,p)
```

`ProjectionContract.reconstructProject` states the coefficient roundtrip law. This is the central accelerator invariant: projection does not erase the coefficient state used to produce a field.

## Path dependence

`ROMKernel.loadCocycle` records accumulated compensation or load-transfer debt along a motion path. The formalism therefore distinguishes a pose from the derivation that reached it. This is required for hysteresis, friction, seam-load transfer, and repeated-motion analysis.

## Regimes

`RegimeOptimization.Regime` provides the triadic design surface:

- `avoid`: harmful, overloaded, rubbing, impinging, or structurally unsuitable;
- `neutral`: no required intervention;
- `support`: beneficial support or load redistribution.

`joinRegime` is associative, commutative, and idempotent. `avoid` dominates, so a severe local failure cannot be hidden by aggregation; otherwise `support` dominates `neutral`.

## Robust optimisation

`SupportObjective` separates admissibility from evaluation. `RobustOptimal` records a chosen fabric and design together with a proof obligation that they are no worse than any admissible alternative at every admissible pose.

This represents the robust design problem:

```text
min_(fabric, design) max_(q in admissible ROM) J(q, fabric, design)
```

without fixing a numeric score representation prematurely.

## Promotion boundary

`SeaminitSupportPromotion` only promotes an end-to-end system when it carries explicit witnesses that:

1. all output fields use a shared body basis;
2. path-dependent ROM has been accounted for;
3. pose–fabric interaction has been accounted for;
4. a region classifier, support objective, and robust optimum are present.

The current implementation establishes the interfaces and algebraic regime laws. Concrete numeric kernels, mesh data, fitted surrogates, and measured/FEM calibration remain implementation instances rather than hidden assumptions.
