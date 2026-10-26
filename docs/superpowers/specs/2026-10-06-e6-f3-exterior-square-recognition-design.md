# E6/F3 Exterior-Square Recognition Design

## Goal

Promote the experimentally verified four-trit/E6 bridge into a fail-closed formal theorem surface without identifying the raw punctured carrier `T4^×` with the E6 null cone.

The intended promoted object is the 80-element carrier of nonzero primitive decomposable bivectors arising from symplectic 2-planes in `F3^4`, with an explicit linear isometry into the nonzero null cone of the 5-dimensional quadratic space that also carries the reduced mod-3 `W(E6)` action.

## Existing repo inputs

Reuse, do not duplicate:

- `DASHI.Foundations.SSPTritCarrier`
- Base369 ternary `T4`/hyperfabric carriers and exact recharts
- `DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact`
- existing same-action exceptional recognition interfaces
- existing E6/78 promotion firewalls
- finite `F3` arithmetic and action infrastructure already used by the Monster/Heisenberg lane

The existing raw punctured four-trit carrier remains a distinct typed object. Equal cardinality `80 = 3^4 - 1` is not a recognition theorem.

## Mathematical construction

Let `V4 = F3^4` with the fixed nondegenerate alternating form

`ω(u,v) = u1*v2 - u2*v1 + u3*v4 - u4*v3`.

Let `Λ2 V4` use ordered Plücker coordinates

`(p12,p13,p14,p23,p24,p34)`.

Define the primitive subspace by

`p12 + p34 = 0`.

Represent it by five coordinates

`p = (p12,p13,p14,p23,p24)` with `p34 = -p12`.

For decomposable `u ∧ v`, the Plücker relation becomes

`-p12^2 - p13*p24 + p14*p23 = 0`.

Define `PrimitiveBivector5` and the corresponding quadratic form `qPlucker` by this polynomial. Supply the explicit invertible linear change of coordinates to the standard form `Q5(z)=Σ z_i^2`; the design does not claim that this coordinate choice is canonical.

## Derived 80-state carrier

Define `OrientedLagrangianBivector80` as nonzero primitive decomposable bivectors satisfying the symplectic/isotropy condition. The formal theorem target is an explicit two-sided map

`OrientedLagrangianBivector80 ↔ Q0Nonzero5`

where `Q0Nonzero5 = { z : F3^5 // z ≠ 0 ∧ Q5 z = 0 }`.

Required firewalls:

- do not identify `OrientedLagrangianBivector80` with raw `T4^×`;
- do not infer the equivalence from cardinality 80;
- do not call the carrier E6-semantic without the supplied action intertwiner.

## Incidence theorem

Projectivizing by sign gives 40 symplectic Lagrangian lines and 40 quadratic null points. Prove that the Plücker map preserves the relevant incidence relation:

`L1 intersects L2  ↔  Φ(L1) ⟂ Φ(L2)`.

The 40-point orthogonality/line-intersection graph should therefore realize `SRG(40,12,2,4)` as a finite regression theorem/receipt if the repository's finite-enumeration layer makes that economical. The graph parameters are diagnostic support, not the primary recognition theorem.

## Group action

Define the action of symplectic similitudes on primitive bivectors through the exterior square. Quotienting the kernel `{±I}` gives the faithful 5-dimensional projective action.

The formal recognition interface must expose:

- a `PGSp4(3)`-side actor/action surface;
- a reduced `W(E6)`-side 5-dimensional orthogonal action surface;
- an explicit actor equivalence or generator-level recognition sufficient to identify the two generated matrix actions;
- the commuting action square on the 80-state carrier.

Target theorem shape:

`Φ (actPGSp g x) = actE6 (recognizeActor g) (Φ x)`.

The implementation must preserve the existing distinction between literal matrix equality in a chosen coordinate model and abstract group isomorphism.

## E6 quadratic-space surface

Add or reuse a theorem surface for the mod-3 E6 Cartan form:

1. its radical is one-dimensional;
2. the quotient is 5-dimensional and nondegenerate;
3. a chosen isometry identifies it with `(F3^5,Q5)`;
4. the 72 reduced E6 roots map to the `Q=2` orbit;
5. the reduced simple Weyl reflections preserve `Q5`;
6. the generated image has the same chosen 5-dimensional action as the exterior-square `PGSp4(3)` image.

Do not call the chosen diagonalizing coordinates canonical; only the quotient and induced quadratic space are canonical up to isometry.

## Projective E6 regression

Formalize the 36 root-line quotient `Q2/{±1}` and, where practical, its orthogonality graph with the computationally verified parameters

`SRG(36,15,6,6)`.

This is a finite structural regression supporting the root-line interpretation; it is not required for the base action intertwiner if it creates disproportionate proof overhead.

## Hyperformal weld

Expose the new derived carrier back to the existing 369/hyperfabric stack only through a typed construction from a four-trit symplectic chart:

`T4 chart -> chosen symplectic structure -> primitive exterior-square carrier -> 80-state Lagrangian bivectors -> E6 null cone`.

The weld must explicitly record that choosing `ω` is additional structure on the four-trit chart. The repo's existing raw `T4^×` is retained unchanged.

## Lean mirror

After the Agda owner is source-written, mirror the theorem boundary in `dashi_lean4` using the existing geometric-reasoning integration style:

- typed distinction between raw `T4^×` and the derived Lagrangian carrier;
- explicit exterior-square/null-cone recognition contract;
- action-intertwining theorem surface;
- no cardinality promotion;
- donor receipt for any Agda theorem not fully reproved in Lean.

Do not mark the Lean mirror kernel-green without an exact-head `lake` receipt.

## Attribution and status

- The finite computations motivating the construction are DASHI/local derivations.
- Standard names (`Sp4`, `GSp4`, `PGSp4`, `W(E6)`, Plücker coordinates) remain mathematical reference vocabulary, not source-transfer claims.
- Repo theorem status must distinguish source-written, kernel-checked, computationally verified, and recognition-gated claims.

## Success criteria

The max-cut is successful when the repo has a theorem-bearing path proving or explicitly gating:

1. primitive/decomposable bivector construction from `F3^4`;
2. explicit 80-state two-sided recognition with the 5D null cone;
3. incidence preservation after projectivization;
4. action intertwining between the exterior-square projective symplectic-similitude action and the reduced E6 Weyl action;
5. explicit non-promotion from raw `T4^×`;
6. a Lean mirror preserving the same boundary.
