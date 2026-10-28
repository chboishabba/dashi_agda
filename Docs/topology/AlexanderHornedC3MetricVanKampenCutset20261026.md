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


## 2026-10-27 original-source / exact-path cut

### What the original PDF actually supports

Hatcher *Algebraic Topology* Ex. 2B.2 **printed pp. 171–172**,
author PDF zero-indexed pages **179–180**, was checked against
the printed figures and text, rather than paraphrased from a reprint.
Page 171 starts from `X_0` a SOLID TORUS (one attached handle),
describes `X_n` as a ball `B_n` with `2^n` handles, and proves the
uniform-limit map `f:B_0→R³` is an embedding using injectivity and
compactness. Its exterior `Y_n=R³\X_n` is increasing with
`π₁(Y_n)=F_(2^n)`. The circular annulus used at the one-sector
stage is glued to a punctured torus to produce the child-meridian
commutator. Page 172 states the induced maps are injective,
and compactness transports stage loops AND homotopies into the
limit `π₁(R³\B)`; every generator lies in a commutator subgroup,
so the limit has trivial abelianisation.

**Nonpromotions:** the geometrically tame `B_n` is NOT the
stage handlebody `X_n`; a binary cylinder mass, a round nested
ball, the presence of linked loops, or an algebraic commutator
substitution does not alone establish the source's same-object
3-dimensional punctured-torus attachment.

### Newly implemented Lean transport: genuine source space, not a group label

`ThreeArmHatcherHomotopyTransport.lean` takes a real
source space `W_i` in each sector, a chosen basepoint `w_i`,
and a genuine topological homotopy equivalence
`e_i:W_i ≃ₕ U_i` **plus an equality** `e_i(w_i)=x₀`.
It uses exactly the pinned Hatcher-at declaration
`Hatcher.fundamentalGroupMulEquivOfHomotopyEquivOfEq`
and existing `Hatcher.coprodIEquiv`. This is stricter
than needed for naturally chosen satellite-side basepoints.

`ThreeArmHatcherPathTransport.lean` is the preferred
adapter: for every `i` take
`e_i:W_i≃ₕU_i`, `w_i∈W_i`, and an actual based path
`p_i:Path (e_i(w_i)) x₀` *within U_i*. The result is the
composition

```text
   *_(i=0,1,2) π₁(W_i,w_i)
      -- Hatcher.coprodIEquiv of:
         (Hatcher.fundamentalGroupMulEquivOfHomotopyEquiv e_i w_i)
            ≪trans≫ (FundamentalGroup.fundamentalGroupMulEquivOfPath p_i)
      --> *_(i=0,1,2) π₁(U_i,x₀)
      -- centralPi1CoverFreeProduct -->
        π₁(E,x₀)
```

Both homotopy invariance and based-path transport are EXISTING
upstream formal theorems. The actual equivariant straight paths
`γ_i(t)=(1-t)(20,20,20)+t(13e_i)` from #1244 give
a source-specific geometric route for the basing witnesses;
the Lean `Path` values and satellite maps have not yet
been constructed/typechecked. Crucially the new path adapter
does not demand that the original source basepoint coincide with
the common ambient one.

Mathlib original API independently checked:
`FundamentalGroup.fundamentalGroupMulEquivOfPath`,
`Mathlib/AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean`.
Pinned Hatcher-at original implementation independently fetched:
`Hatcher/VanKampen/WedgeFundamentalGroup.lean`.
These are imported *theorem donors*, not novel historical claims.
Agda #1254 remains STACKED and unmerged; it already consumes
the older clopen chronological bridge but does not contribute a
wild-exterior homotopy equivalence.

### Pareto/Ibrahim/snowball hard wall

The **only new source-specific geometric input** needed by
`threeArmHomotopyPathSourcesEquivPi1` is now plainly typed:
`W_i` must be the genuine supported one-sector Hatcher exterior,
`e_i` the actual satellite-relative collar homotopy equivalence
onto the chosen *same* open member `U_i`, with `p_i`
a path to the common basepoint. The existing radius-cut
certificate still separately demands central `π₁`
triviality, central connectivity, and member connectivity.
Upstream Mathlib and Hatcher-at supply the remaining algebraic
functoriality and group transport.

Compiling these new Lean modules against the exact branch pin
is still outstanding; source-written is NOT kernel-certified.
Classical 3D collar/satellite equivalences are not conjured by
their typed Lean signatures. Current independent local arithmetic:
`r_-=15/4<17/4=r_+`, pair centres squared
distance 162, cut diameter squared `289/4<162`,
and fixed basepoint clearances all PASS using exact fractions.
