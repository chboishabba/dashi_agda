# 13 in 27: same-carrier antipodal quotient and diamond-axis restriction

## Reviewed primary repository PR donors (2026-10-26)
- PR #1249: `DASHI.Unified.Hyperfabric27MinusOneAntipodalSameCarrierCutExact` proves the sign inversion on the **original** path-graph cube, involutivity, unique fixed origin, adjacency-preservation, and reuses the two-sided 1+26 Albert-*shape* chart. The 13-pair cardinality is already sourced to `IbrahimA027907PathCubeTernaryExceptionalThirteenSnowballExact`; do not duplicate its owner or promote the set bijection to exceptional-Jordan multiplication.
- PR #1239: `JInvariant369Cube27ModularSliceActionExact` defines a specific mod-3 linear action on each nine-site xy slice, which is bijective but **not** a native nearest-neighbour cube-graph automorphism; `Base369AlbertF3CubeHamiltonianSymmetryMaxCutExact` distinguishes the nonperiodic path cube from C3³ torus translations and from Jordan/Monster actions.
- PR #1261: `DiamondTernary111AxisBridgeExact` and `DiamondNVFourAxisPermutationExact` encode eight signed corners and four unoriented body-diagonal axes, respectively.

## Exact refinement: not just four but thirteen axial classes

For X = {-1,0,1}³, coordinate negation has one fixed point 0 and
13 size-two orbits. The nonzero sign-support stratification is:

| nonzero coordinate count | number of points | antipodal pairs | directions |
| 1 | 6 | 3 | axial [100] families |
| 2 | 12 | 6 | face-diagonal [110] families |
| 3 | 8 | 4 | body-diagonal [111] families |

The total is 3+6+4=13. Thus the diamond <111> quotient is an
equivariant subcarrier of four elements inside the 13-class quotient,
not the entirety of it. The full cubic signed-permutation group B3
preserves all three support-size strata. The full action on the 13 projective axes has kernel {±I}, while the action on the 26 oriented nonzero sites is faithful (unlike the action on only four body
diagonals, whose kernel is {±I}).

## Three distinct uses of 13/111 (avoid a false equivalence)

1. Ordinary base-three numeral 111_3 evaluates to 13, as proved by
   `AllOnesPadicThresholdBoundary.allOnesPrefix3`.
2. With **ordinary base-three position digits** d in {0,1,2} and
   *centred coordinates* x=d-1, the linear 0..26 index 13
   (digits 111_3) corresponds to the origin (0,0,0), not the corner
   (+1,+1,+1). The latter has ordinary digits 222_3 and index 26.
3. With **balanced ternary signed digits** {-1,0,+1}, the string
   (+1,+1,+1) evaluates to integer 13, and is a corner [111].
   This is a different codec/evaluation map.
4. The *thirteen nonzero antipodal pairs* count is a quotient
   cardinality, not the number 13's position in an index scheme.

This is an important semantic distinction: a single surface form 111
may refer to the centre under one indexing convention and to an outer
corner under another. Preserve the codec tag and the residual.

## Mathematical and physical gates

- Direct reuse: import the PR #1249 original antipode and quotient
  once merged, rather than creating a second arbitrary antipode.
- Define a typed quotient orbit and support-count classifier with
  reconstructible orientation residual; certify 3+6+4 orbit strata.
- Prove B3 equivariance with the central ±I kernel on all 13 axes and restrict to the diamond
  four-axis subcarrier. For four body-diagonal axes the effective
  permutation group is S4 with central ±I kernel; for all thirteen
  axes the action is faithful because coordinate sign flips and
  permutations are distinguished on coordinate and diagonal lines.
- The native modular sheet map from PR #1239 generally does not
  preserve support-size stratification or nearest-neighbour
  adjacency: do not identify its order-four orbit with a spatial C4
  rotation without an equivariance proof.
- Diamond NV defect directions use only [111]-type orbits. Their
  physical site stabilisers and quantum Hamiltonian representations
  still need independently typed symmetry proofs.
- No equality between Albert algebra multiplication, Monster
  actions, bosonic-string dimensions, scalar 13, and physical
  crystal structure follows from the shared 27-site cardinality.

## Attribution
Classical cubic group actions/projective axes and base-three
arithmetic are prior art. Native formal proofs and computational
receipts remain attributed to their PR owners, including the 2026-10-24
PR #1249 and PR #1239 work. This document only cross-references
and adds the typed codec/stratification consequences; it does not
claim these PRs are merged or typechecked locally.
