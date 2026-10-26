# Alexander horned C3 — metric same-object van Kampen cutset (2026-10-26)

Status: **source-written Lean implementation**, with actual classical
geometry and group-theoretic donor reuse; **no exact-head Lean or Agda
kernel check in this cut**, no claim that infinite wild-satellite
coordinate maps have been formalized.

Parent: [DASHI PR #1244](https://github.com/chboishabba/dashi_agda/pull/1244).
Related [stacked PR #1254](https://github.com/chboishabba/dashi_agda/pull/1254):
finite PL ancestry, chronological Cantor event orientation and counterexamples.

## 1. Correct source objects, with original authority intact

* J. W. Alexander (1924), original horned-sphere construction.
* Allen Hatcher, *Algebraic Topology*, Example 2B.2, printed
  pp. 170–172, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf:
  classical punctured-torus exterior group, finite free stages,
  injective commutator transitions and compactness/colimit result.
* Franca Lippert, *The Alexander Horned Sphere and Bing's Hooked Rug*,
  §§2.1–2.3, https://www.maths.gla.ac.uk/~mpowell/WriteUp_Franca.pdf:
  supported construction and tame region away from the wild Cantor
  set; distinct expository source, not independent authorship of
  Alexander's original discovery.
* Classical Seifert–van Kampen theorem, tame 3-ball/regular
  neighbourhood and Schoenflies facts retain original authority.
* Formal implementation donor:
  Deicyde/hatcher-at pinned at
  `fb20d71b6a7561c80f66350c14af118f3962377a`.
  Its `Hatcher.coprodIEquiv` and existing cover
  free-product equivalence are *reused*, not rewritten.

The current specific rational (C_3) positioning, proof interfaces
and verification harness are the existing user-directed DASHI
implementation. A source mention, nominal lemma name, successful
finite example, and proof-checker receipt are different evidence.

## 2. Existing head: exact implementation chain

Source paths under `proofs/horned_c3_lean/HornedC3/`:

1. `ThreeArmVanKampen.lean` — existing Hatcher-at pointed-cover
   group isomorphism under real geometric certificates.
2. `ThreeArmCollarIntersections.lean` — actual union/intersection
   identities from disjoint satellite-only sets.
3. `ThreeArmCollarCoverAssembly.lean` — existing cover-fields
   assembly; no imaginary central contractibility.
4. `ThreeArmCentralPi1Reduction.lean` — one central `π₁(C)`
   subsingleton cert suffices for all off-diagonal overlap groups.
5. **NEW** `ThreeArmHatcherGroupTransport.lean` — uses the pinned
   `Hatcher.coprodIEquiv` to map any three supplied genuine
   cover-member source groups into `π₁(E,x₀)` in one composition.
6. **NEW** `ThreeArmRadiusCutGeometry.lean` — constructs actual
   radius-cut open sets by continuous preimage of balls/closed balls
   in the ambient `Y`. It derives openness, full coverage,
   disjointness and common-basepoint membership from numerical
   inequalities rather than taking them as unrelated assumptions.
7. **NEW** `ThreeArmRadiusCutHatcherTransport.lean` — composes the
   metric cut certificate, central `π₁` reduction and free-product
   equivalence. Registered into the existing `HornedC3.lean`
   library root, no second group-presentation framework.

### Correct ambient spaces

Set `X=E=ℝ³\B` with the subspace topology and
`Y=ℝ³` carrying the Euclidean metric, with inclusion
`f:E→Y`. The centres `c_i=9e_i` lie inside the removed
wild solid `B`, so they **cannot** be centres of balls
in the metric space `E` itself. The new module correctly
takes `centres:Fin 3→Y` and continuously pulls the radial
cuts back to `E`.

For `r_-=15/4, r_+=17/4`:
```text
C = f^{-1}((union_i closedBall(c_i,r_-))^c)
S_i = f^{-1}(ball(c_i,r_+))
U_i = C union S_i
```

Numerically `r_-<r_+` and
`(2r_+)²=289/4<162=|c_i-c_j|²`.
Therefore every point of E either lies outside all
inner closed balls (and in C) or inside at least one
outer open ball (and in a corresponding S_i).
The outer balls are disjoint. This proves the **full
relative open cover of the chosen X**, not merely
a finite sample of Euclidean positions.

The proof uses Mathlib's actual finite-index API
`isClosed_iUnion_of_finite` (not an invented
`isClosed_iUnion`), `Metric.mem_closedBall`,
`Metric.mem_ball`, the triangle inequality and
`linarith` for centre separation. The correction
was source-inspected against Mathlib documentation.
That is still **API inspection**, not a compiled
kernel receipt.

## 3. The remaining minimal same-object geometric suppliers

| Gate | Exact required data | Current status |
| --- | --- | --- |
| Radius cover/overlap set algebra | `r_-<r_+`, `2r_+<dist(c_i,c_j)`, `x₀∈C` | Implemented as Lean conditional metric lemmas; rational placement from existing scripts |
| Connected central region | `IsPathConnected C` for actual subspace E | Classical tame star regular neighbourhood route; Lean witness absent |
| Trivial central `π₁` | `Subsingleton(FundamentalGroup C x₀)` | Paper-level tame-tree/Schoenflies argument; Lean witness absent; `C` is **not** contractible in R³ |
| Connected cover members | `∀i, IsPathConnected U_i` | Source-supported collar argument; Lean witness absent |
| Actual source-to-member group maps | `∀i, G_A ≃* FundamentalGroup(U_i,x₀)` | **Principal P0 geometry wall**: Hatcher-supported wild satellite, prescribed inward cap, relative collar equivalence, meridian maps and basing paths |
| Symmetry naturality | source- and target-induced (C_3) maps agree on those meridians | Explicit cyclic basing paths exist; group-map equality remains open |
| Exact-head compiler | Lean/Lake build of new modules on pinned Hatcher dependency | No compiler receipt; source-written code only |

The outer (C_3) action on the abstract free product,
finite (2I) quotient, and gauge simulator do not pay any
of these topology suppliers.

## 4. Clopen ball / latest-PR directional correction

Original `CantorProjectiveCylinderMeasureExact.leftChild`
prepends a bit in *newest-first stack* order. PR #1254's
`ExoticCantorCylinderOrientationExact` correctly
distinguishes a chronological cylinder **event**
and proves that APPENDING refines that event. Parent
`AlexanderHornedC3ChronologicalClopenBridgeExact`
reverses the stack first, retaining exact mass and
external sector C3 rotation without claiming that
the clopen ends make the connected exterior clopen.

`alexander_horned_c3_clopen_spatial_realization.py`
directly reuses the existing tame-ball constructor
and gives a real (C_3)-equivariant affine Cantor
embedding. Existing local source was executed this
cut: **511** finite binary prefixes and **1533**
sector-prefix checks pass. This proves the explicit
tame control is coherent; its points and cylinder
algebra alone do **not** determine ambient linked
horn stages, the Alexander `G_A`, or geometry's
physical spin holonomy.

PR #1254 is stacked on #1244 and has already consumed
the parent chronological bridge. It was inspected,
not cherry-picked, force-merged or reassigned to
the parent. Other new PRs #1271, #1269/#1270,
#1266/#1267, #1260/#1261 were considered for
specific geometry inputs; none supplies the chosen
wild satellite's relative exterior equivalence.
This is selective source-driven snowballing, not
citation accumulation.

## 5. Pareto/Ibrahim terminal frontier

The highest-ROI single object is now a
`HatcherSupportedSatelliteRelativeExterior`:
a chosen embedded wild 3-ball with actual stage
maps and two-sided *stationary inward cap*,
a pair of collar-slide homotopies identifying its
bounded outer piece with the original Hatcher
exterior, and induced meridian maps. Its (C_3)
copies and source-specific based paths then feed
`radiusCutSourceGroupsEquivPi1` without more
abstract algebra.

Only when those geometric maps are instantiated
and the pinned Lean chain typechecks can the
fully internal, same-object
`π₁(E) ≃ G_A*G_A*G_A` be promoted from a
source-supported classical argument to
**kernel-certified exact-head theorem**.

Stop rather than invent a false proof if no concrete
satellite relative homeomorphism is present; preserve
the evidence graph and do not turn finite icosahedral
quotients, clopen addresses or source citations into
geometric identities or independent physical evidence.
