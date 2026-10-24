# C3 / 369 braid endpoint orientation, framing and Möbius max-cut (2026-10-22)

## Established owner archaeology
- `DASHI/Foundations/Base369MobiusTransport.agda`: concrete +3 modulo 6, preserving the triadic phase, flipping orientation sign, order two.
- `DASHI/Reasoning/ParallaxHolonomyBridge.agda`: compatible finite sign transport; semantics and realised context loop are independently gated.
- `DASHI/Geometry/MobiusOrientationGate.agda`: the *geometric* Möbius one-loop orientation reversal remains target-only; no universal geometric promotion.
- `DASHI/Algebra/CliffordSpinLift.agda`: Pin/Spin/double-cover *contracts*, not automatically inhabited physical comparisons.
- `DASHI/Physics/CFD/SparseTwistLESBridge.agda`: signed sparse field, twist operator and codec obligations, not an automatic ribbon-braid theorem.
- `DASHI/Foundations/Base369Ternary27HypervoxelFabricGeometryExact.agda`: balanced signed 27-point cube; more coordinates for sampled orientations, but its finite cardinality does not faithfully encode arbitrary integer framing.

## New modules in this PR
1. `C3BraidEndpointMobiusExact`: explicit endpoint orientation polarity, one-end/two-end flips, order-two returns and comparison to the existing Base369 Möbius polarity. The finite Z2 flip is established at its declared level.
2. `C3BraidFramingInformationLossExact`: counterexample to recovering full integer twists from otherwise identical endpoint positions and orientation bits. The fully untwisted and once-twisted ribbons have identical observed endpoints yet different framing counter.

## Critical distinctions
An oriented line has a tangent; a ribbon also has a transverse direction `n(t)` with `n(t) ⟂ tangent(t)`. A framed curve is a path `(gamma,n)`. A closed oriented ribbon has an *integer* framing/self-linking number relative to a chosen zero framing, not determined by the centreline or terminal sites. The oriented framed braid group `FB_n = B_n ⋉ Z^n` (the action permutes twist counters) is the appropriate algebraic target. In the presence of mirrors or unorientable band attachments, the structure must instead admit orientation-reversing transitions / O(2) frames; this is not the same as a full 2π ribbon twist.

A **Möbius strip** arises on gluing one end of a strip with a half-twist (orientation reversal). In a freely oriented three-strand ribbon braid with unglued endpoints, moving one end around cannot by itself make a Möbius strip. Möbius classification concerns the gluing/holonomy of the *normal line bundle* around a closed loop, detected by `w1 ∈ H¹(loop;Z2)`. The terminal observed direction can diagnose a relative flip only when the initial frame and physical transport/gluing have been fixed. If two end frames can independently rotate, endpoint positions alone tell neither twist count nor orientation class.

Closed oriented circle fibres in the classical Hopf fibration are not Möbius bands. Its circle bundle uses structure group U(1) and first Chern class, whereas a Möbius line bundle uses O(1)=Z2 and a nonzero first Stiefel–Whitney class. Spin(3)→SO(3) is another independent double-cover; 2π and 4π lift effects do not automatically identify a Möbius normal bundle.

## Highest-alpha typed next theorem
Define `FramedContinuousConfiguration = (gamma_i(t), normal_i(t), orthogonality, norm=1, collisionFree)` and an endpoint-framing transport record; project to `(centreline braid word, integer self-twist vector, Z2 gluing parity)`. Prove equivariance under C3 relabelling and show the consumer that only observes selected sites cannot recover the integer twist vector. The existing counterexample witnesses the latter.

For a moving 27-cube, use a signed local 3-axis frame and determinant sign as a finite *chart*, or unit quaternions for **proper rotations** (SO3 via SU2). Quaternions alone cannot encode reflection (det=-1), need O3/Pin or explicit parity. A single quaternion endpoint also does not recover path homotopy or arbitrary ribbon twist count: a 2π turn is the identity in SO3 and -1 in its SU2 lift, while 4π returns +1 and can still leave a ribbon with nonzero framed winding. Sparse/anisotropic metrics are optional discretisation and energy/transport models, not substitute proof of normal-bundle holonomy.

## Physical test / attribution
A real ribbon experiment needs tracked endpoint clamps **and transverse marks along the strand**, sufficiently resolved time history, known no-slip/twist-transfer rules, and a reference normal frame. Test (1) one endpoint fixed versus both rotating, (2) full turn versus half-turn/gluing, (3) different handedness, (4) pairwise crossing number versus individual framing, (5) sparse reconstruction error. This can distinguish Möbius parity from integer twist and braid linkage.

The original alternate-lobe trajectory / endpoint hypothesis comes from the project user; formal counterexample and typed endpoints are current-session implementation. Nothing here claims discovered physical KK/Möbius equivalence or a complete physical theory.

## Acceptance
```sh
agda -i . -i /path/to/agda-stdlib DASHI/Foundations/C3BraidEndpointMobiusExact.agda
agda -i . -i /path/to/agda-stdlib DASHI/Foundations/C3BraidFramingInformationLossExact.agda
```
No exact-head Agda kernel receipt is presently attached; source-written only.
