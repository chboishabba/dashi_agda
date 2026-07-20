# Generic compact Lie-group layer for Yang–Mills

The existing SU(2) development remains the concrete proof-development carrier.  This tranche adds the abstraction boundary required before any Yang–Mills theorem can be stated for every compact simple gauge group.

## Layering

`CompactLieGroupCore.agda` defines:

- groups and Lie algebras;
- exponential/logarithm and adjoint action;
- adjoint functoriality and bracket preservation;
- explicit compactness, connectedness, and Lie-algebra simplicity witnesses;
- group and Lie-algebra homomorphisms.

`CompactLieGroupGeometry.agda` owns the quantitative local geometry:

- an invariant inner product, norm, and bi-invariant distance;
- a uniform exponential chart and inverse chart;
- dexp, inverse-dexp, bracket, and adjoint-Lipschitz bounds;
- the distinction between group-dependent constants and scale/volume/background-uniform estimates.

`CompactLieRepresentationData.agda` owns finite-dimensional representation data:

- rank, dimension, roots, bases, and structure constants;
- bounded root and structure-constant data;
- normalized left/right invariant Haar measure and Weyl integration;
- character bounds, spectral gaps away from the center, and tensor-product control.

`CompactLieYangMillsBridge.agda` collects the analytic obligations needed by the Balaban lane:

- generic gauge actions and gauge fixing;
- Faddeev–Popov coercivity;
- equivariant block averaging;
- small-field chart compatibility;
- large-field suppression and polymer diameter entropy;
- reflection positivity and cluster decomposition;
- one-step and iterated RG, infinite-volume limit, exponential clustering, and a positive mass gap.

## SU(2) relationship

The quaternion and rotation-polynomial modules are not discarded.  They should instantiate the generic records for `G = SU(2)` and prove that their concrete adjoint action agrees with generic `Ad`.  Quaternion polynomial identities then prove the SU(2) instance only; they cannot inhabit the generic theorem without a separate uniform compact-Lie-group argument.

## Claim boundary

This tranche supplies typed interfaces and promotion boundaries.  It does not prove the generic analytic estimates, construct Haar measure, classify root systems, establish a uniform RG iteration, or prove the four-dimensional Yang–Mills mass gap.  Those remain explicit fields rather than postulates hidden inside the SU(2) implementation.
