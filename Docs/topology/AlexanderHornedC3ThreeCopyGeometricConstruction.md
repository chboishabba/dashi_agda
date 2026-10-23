# Equivariant boundary-connected sum of three Alexander horned balls

**Date:** 2026-10-24. **Role:** mathematical construction and proof specification,
NOT an Agda geometric kernel receipt.

## Classical donor and provenance

- J. W. Alexander (1924): horned sphere.
- Allen Hatcher, *Algebraic Topology*, Example 2B.2, printed pp.170–172,
  <https://pi.math.cornell.edu/~hatcher/AT/AT.pdf>. In particular Hatcher
  supplies a tame cap away from the Cantor wild set, approximating
  nested handlebodies X_n, a nested-ball limit, an explicit van Kampen
  commutator expansion and its injectivity.
- Theorem applied, not reinvented: Seifert–van Kampen applied to a
  cover with path-connected simply connected overlaps gives free
  products. For the gluing argument below the caps and tube collars
  are deliberately placed in *tame* patches.
- Repo sources: `DASHI/Core/FiniteC3OrbitStabilizerExact.agda`,
  `AlexanderHornedC3AmbientRotationExact.agda`,
  `AlexanderHornedC3FiniteStageExact.agda`.
- New: the symmetry-by-three-copies construction, complementary
  sector-retraction detector, and the exact conditional theorem
  `AlexanderHornedC3FreeFactorDetectorExact.agda`.
- Attribution rule: a source being cited does not create Agda proof,
  and a typed conditional theorem does not supply its geometric inputs.

## Explicit geometric construction

Start with an Alexander horned 3-ball H_A subset int(D³)
whose wild Cantor set is disjoint from a chosen small boundary disk
D of a *tame* patch. This is possible since Hatcher's construction
is locally ordinary off the wild Cantor set. Choose three disjoint
round balls U_0,U_1,U_2 in R³ with centers on one orbit of the
order-three rotation R(x,y,z)=(z,x,y). Choose orientation-preserving
similarities f_i mapping a common containing ball to U_i, with
f_(i+1)=R∘f_i (indices mod 3). Put H_i=f_i(H_A).

Choose a small round central ball C on the fixed diagonal axis.
Connect C to the tame disk f_i(D) by a narrow embedded 1-handle
T_i. Choose T_0 along a tame, unknotted arc and T_i=R^i(T_0).
All three tubes and their neighborhoods are pairwise disjoint and
disjoint from the wild portions; choose the arcs as a radial
three-pronged star. Let

    H = C union T_0 union H_0 union T_1 union H_1
          union T_2 union H_2.

The attaching graph is a TREE: a central vertex and three terminal
vertices. Boundary-connected sum along a tree of 3-balls by
product-collared tame disks is again a 3-ball. Thus H≅D³ and
∂H≅S², while R(H)=H. Since the wild Cantor sets are untouched,
the resulting embedding is wild in three disjoint patches.

Choose nested Hatcher handles X_(i,n)=f_i(X_n). Use the *same*
central C and tubes at every stage, attached to a fixed tame patch:

    X^sum_n = C union tubes union (union_i X_(i,n)),
    X^sum_(n+1) subset X^sum_n,
    intersection_n X^sum_n = H.

The last equality is finite-union/intersection distributivity
for the three local decreasing families in disjoint supports.
The original Hatcher X_n include all tame attaching caps.

All these choices can be made C3-equivariantly by picking the data
in U_0 once and obtaining sectors 1 and 2 by rotation, *not* by
choosing three independently incompatible isotopies.

## Complement computation

Let E_n=S³\X^sum_n, E=S³\H and base the fundamental groups
at infinity, fixed by R. Decompose E_n using the three separating
round shells ∂U_i, each punctured by exactly one unknotted tube.
After a small open collar thickening, each interface retracts
onto a 2-disk, hence is path-connected and simply connected.
The central exterior of the three-arm regular neighborhood is
simply connected (regular neighborhood of a tame embedded tree),
and each local exterior piece has the same π₁ as S³\X_n:
the modification is inside a product collar on the chosen tame cap.

Iterated van Kampen therefore gives

    π₁(E_n,∞) ≅ F_(2^n) * F_(2^n) * F_(2^n)
              ≅ F_(3*2^n).

This conclusion has an important **gluing prerequisite**: the
sector-to-central overlaps must really be the collar-thickened
simply-connected disks described above. An arbitrary arrangement of
three horns or tubes cannot be substituted without rechecking
linking and intersections.

Inclusions E_n -> E_(n+1) preserve sectors, and Hatcher's local
calculation supplies precisely

    x_(i,w) -> [x_(i,w0), x_(i,w1)].

Every factor map is injective, by the Hatcher free-product-of-cyclic
subgroups argument. Thus all the threefold transition maps are
injective. Every loop and every nullhomotopy in E has compact image
contained in some E_n, since E is the increasing union of open E_n.
Hence

    π₁(E,∞) ≅ colim_n F_(3*2^n) =: G.

The added point at infinity does not change π₁ relative to the
R³ exterior: in an open 3-manifold, loops and 2-parameter homotopies
can be perturbed off a single point by general position. It DOES
matter for H² and bundle classification; never transport the
H²=0 statement between the two exteriors without checking.

## Symmetry and noninnerness with no finite A5 detector

At every n the ambient rotation sends x_(i,w) to x_(i+1,w).
Because ∞ is fixed, the maps on based π₁ are honest
automorphisms, not only outer automorphisms.

Let G_A=colim F_(2^n). Since filtered colimits commute with finite
coproducts in Groups, or directly by the universal properties,

    G ≅ G_A * G_A * G_A.

Each G_A contains a nonidentity meridian m, because its transition
maps are injective and F_1 is nontrivial. The free product has
canonical retractions p_0:G->G_A sending the first factor
identically and the others to 1. Thus

    p_0(m) = m != 1,   p_0(R_*(m)) = 1.

If R_* were conjugation by h in G, the projection would imply

    1 = p_0(R_*(m)) = p_0(h)m p_0(h)^(-1),

forcing m=1, contradiction. Therefore R_* is NOT inner. Since
R_*^3=identity, the associated class has EXACT order three:

    [R_*] in Out(π₁(E,∞)) has order 3.

This is stronger and requires fewer external algebraic ingredients
than the A5³ quotient route. The finite A5³ probe remains an
independent witness and a useful nonabelian representation test.
Each generator becomes a commutator at the next level; thus G
is nontrivial and perfect, with no nontrivial abelian characters.

## Explicit distinctions and proof certification

- **Mathematical construction:** geometric boundary-connected-sum
  argument and specified van Kampen collars above.
- **Agda exact files:** `AlexanderHornedC3AmbientRotationExact`,
  `AlexanderHornedC3FiniteStageExact`,
  `AlexanderHornedC3ComplementActionExact`,
  `AlexanderHornedC3OrbitSolidExact`,
  `AlexanderHornedC3FreeFactorDetectorExact`. The complement and orbit
  modules construct an order-three point-set action on the exterior
  of an explicit union of three translates. The factor detector proves
  the corresponding **abstract statements conditionally**.
- **Not yet kernel-checked:** this specific 3-ball embedding,
  the tame-collar cover deformation retractions, van Kampen
  isomorphisms, compactness/direct-limit equivalence, and
  nontrivial infinite group/factor retractions in Agda.
- **Do not overclaim:** this is not a theorem about Monster states,
  KK fields, the physical universe, DMT, or a genuine faithful
  nonabelian braid action on the exterior. The B3->S3 shadow
  only yields the finite strand permutation.

## Acceptance

    python3 scripts/alexander_horned_c3_a5_probe.py
    python3 scripts/alexander_horned_c3_free_factor_probe.py
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3AmbientRotationExact.agda
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3FiniteStageExact.agda
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3ComplementActionExact.agda
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3OrbitSolidExact.agda
    agda -i . DASHI/Mathematics/Topology/AlexanderHornedC3FreeFactorDetectorExact.agda

A reviewable true-topology proof should present the explicit
collar-thickened open sets and verify all contractible overlaps.
The Agda kernel cannot infer their existence from the above prose.
