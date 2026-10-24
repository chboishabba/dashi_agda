# Alexander horned C3: clopen-ball prior art, embedding/linking discriminator and rational handle tree

Date: 2026-10-24. Owner: existing `alexander-horned-c3-equivariant-20261024`,
PR #1244. All original-source authorship and theorem status preserved.

## Highest-value finding

**The clopen-ball work IS relevant, but it addresses the ENDS.**
It cannot, even in principle, identify the wild exterior `pi1`
on its own. There is a natural symbolic wild-end space

    K = C3_ext x {0,1}^N = C3_ext x Z2.

A depth-n basic clopen cylinder has label (c,b0..b_(n-1))
and product probability mass 1/(3*2^n).

An ordinary/uncrossed embedding and a wild linked embedding
may induce precisely the SAME finite clopen Boolean algebras,
inverse-limit cylinder topology and rational cylinder mass.
The distinction between these embedded objects is in
**ambient 3D linking/collar maps**, not in K.

The open exterior E of a filled horned ball is connected.
Every continuous map from a connected space to totally
disconnected K has connected image, necessarily a POINT.
Therefore **there is no nonconstant continuous map E -> K**.
The C3 x Z2 labels live on the endpoint set/defining stage
regions, not as a global continuous clopen decomposition
of E. This connectedness obstruction is independent of
C3 lift choices, 2I/A5 or p-adic field selection.

Three satellites can have clopen *end subsets* and STILL
be joined via handles into one connected 3-ball; the
global complement's nonabelian fundamental group responds
to linking in the attachments.

## Existing formal donors and actual proof status

1. `DASHI/Geometry/SSP369ClopenBallBridge.agda`
   - proves finite 3/6/9 common-prefix depth refinement,
     containment of finer in coarser prefix balls;
   - `canonicalClopenAuthority` merely chooses constructors
     `prefixBallOpen` and `prefixBallClosed` of
     `ClopenWitness`. Those LABELS are not proofs that a
     subset of any specified topological ambient space is
     open and closed.
   - The digit radix there is ternary/mixed, not literal
     two-child Hatcher branching.

2. `DASHI/Foundations/InverseLimitClopenRefinement.agda`
   - real records for projective finite tower and compatible
     threads;
   - its `CompleteClopenAuthority` supplies
     `intersectionSingleton : Set` and
     `ultrametricComplete : Set` as FIELDS, not inhabited
     completeness and singleton-intersection proofs.
   - Do not promote the mere record to an actual metric
     completion theorem.

3. `DASHI/Foundations/Base369PrefixUltrametricExact.agda`,
   `DASHI/Geometry/ProObjectSemantics.agda`:
   actual depth-prefix agreement, symmetry/refinement and
   formal-depth ball statements. The latter is a pro-object
   point/construction, not a smooth R3 ball.

4. `DASHI/Foundations/CantorProjectiveCylinderMeasureExact.agda`,
   `CantorFiniteClopenPremeasureExact.agda`:
   actual binary-cylinder dyadic mass, consistent child
   refinement, finite Boolean clopen algebra, complements,
   disjoint unions. THIS is the best proof-bearing donor
   for the horned endpoint (Z_2) boundary.
   Countably additive Borel extension is explicitly open.

5. `DASHI/Analysis/NonArchimedeanPadicCylinderBorelSourceExact.agda`:
   identifies exact mathlib p-adic cylinder/Borel sources as
   citation/library interfaces; do not call the source
   written Agda module a compiled metric/Borel implementation.

6. `DASHI/Mathematics/Topology/AlexanderHornedBinaryPadicCylinderExact.agda`:
   our previously integrated ACTUAL binary horn address
   cylinder contract; chronological stream orientation
   is opposite the prepend newest-first Horn.suffix.
   `AlexanderHornedMixedPrimeCRTWeldExact.agda` places
   independent external C3 sector and binary cylinder
   in the correct 3*2^n finite stages.

7. `DASHI/Mathematics/Topology/AlexanderHornedC3OrbitSolidExact.agda`:
   constructs `OrbitSolid=Seed union R(Seed) union R²(Seed)`
   and proves point-set rotation invariance of solid and
   complement from R³=id for **any** chosen seed.
   This already pays the ABSTRACT `R(B)=B` invariant
   for a solid DEFINED as an orbit union. The hard gate is
   choosing a seed and collared glue so the union is
   actually an EMBEDDED WILD 3-BALL with desired pi1.
   Don't prioritize another conditional R-invariance lemma.

## New actual binary cylinder/mass Agda owner

`DASHI/Mathematics/Topology/AlexanderHornedC3ClopenCylinderMassExact.agda`

Uses literal `HornAddress=(C3, newest-first Bit list)`,
maps its left/right child to the EXISTING
`Cantor.leftChild/rightChild` rather than making
a duplicate dyadic measure library. Defines

    mu(sector,prefix) = 1/3 * Cantor.cylinderMass(prefix),

proves strict invariance under C3 sector rotation and
mass(parent)=mass(left)+mass(right), plus 3 root sectors
having total mass one. It also defines decidable finite
binary prefix-cylinder membership, complementary membership
and nesting via the pre-existing binary cylinder
projection theorem. These are source-written term-level
statements, NOT kernel checked in this round by request.

No circular application of the word 'clopen': finite
coordinate membership and complement form a Boolean
partition, and classically their inverse images are
clopen in the inverse-limit topology BY DEFINITION
of the cylinder topology. This does not make them
clopen subsets of the connected exterior E.

## New independent exact geometric discriminator

`scripts/alexander_horned_clopen_linking_impasse_probe.py`

C1 is the CCW circle in z=0 bounding the disk

    D1: x²+y² <=4, z=0.

C2_h(t)=(h,1+cos t,sin t), h in {1,5}.
Two transversal plane crossings occur at

    t=0: (h,2,0), derivative z'=+1;
    t=pi: (h,0,0), derivative z'=-1.

For h=1 the *negative* hit is inside D1, and positive
hit is outside: signed intersection = -1.
For h=5 both are outside: signed intersection = 0.

By the classical intersection/linking theorem,

    lk(C1,C2_1) = -1,   lk(C1,C2_5) = 0.

The curves are disjoint and the intersections are transverse.
They are DIFFERENT embedded links, even though either can
be assigned the IDENTICAL C3 x binary Cantor address
hierarchy and its clopen masses.

The determinant+1 cyclic rotation R(x,y,z)=(z,x,y)
copies this local link into three satellite charts
centred 9e_x,9e_y,9e_z. Each comparison curve fits
inside radius sqrt(30)<6 around its centre. Pairwise
satellite-centre squared separation is 162>4*36
and central distance^2 is 81>(6+1)^2, so the
three satellite charts are disjoint and C3-equivariant.
Local finite signed-intersection and mass calculations
were executed in Python and passed.

**Scope:** a local Hopf/unlinked clasp pair is not itself
Hatcher's wild 3-ball! This is a finite source-defined
LINKING DATUM required by the larger construction,
not a proof of the infinite Alexander exterior group.
Indeed the eventual perfect horned group has no nonzero
abelianization, so global H1/linking of an individual
meridian cannot substitute for its nonabelian commutator
tower. The actual collars and van Kampen step are
independent and still needed.

## Constructive central-tree gluing scaffold

Previously `C3SatellitePlacementExact.agda` has
the exact centre 0 and satellite positions 9e_i.

New `scripts/alexander_horned_clopen_tree_handle_scaffold.py`
checks that the three radial handle cores

    H_i = {t e_i: 1 <= t <= 8}, i=x,y,z

with radius epsilon=1/4 have disjoint interiors outside
the central unit ball. For different axes, closest
core distance squared is >=2>(2eps)^2.
Off-axis satellite separation is >=9; unit scaffold
balls and other tubes are disjoint by strict rational
inequalities. The connection graph has 4 vertices
(central and three satellites) and 3 edges, is a TREE,
and its full geometry is C3-cyclically symmetric.

Standard 3-manifold fact: given topological 3-balls,
TAME collared attaching disks and disjoint 1-handles
joined along a tree, their boundary connected sum is
again a topological B3. The fact is classical/conditional:
our finite separation calculation DOES NOT furnish
a collared wild satellite, a homeomorphism B3->union,
or any exterior homotopy / pi1 isomorphism.

Invariance is handled by the **existing orbit-solid
owner**, not a speculative free rotation of an arbitrary
fixed embedding. Wildness and pi1 same-object are the
actual outstanding construction gates.

## Primary sources with role separation

- J. W. Alexander, *An Example of a Simply Connected
  Surface Bounding a Region Which Is Not Simply Connected*,
  PNAS 10 (1924), 8–10: original pathological embedding.
- Allen Hatcher, *Algebraic Topology*, Example 2B.2:
  https://pi.math.cornell.edu/~hatcher/AT/AT.pdf .
  Hatcher's exact open-exterior free-stage commutator
  van Kampen calculation IS THE pi1 target.
- F. Pugh, *Real Mathematical Analysis*, Cantor Set Lore,
  source discussion on the failure of 'ball dyadic
  partition lemma' for wild Cantor embeddings.
  https://www.lehman.edu/faculty/rbettiol/lehman_teaching/2020mat320/Pugh_Real_Mathematical_Analysis.pdf
- R. Sher, *On the space of Cantor subsets of R3*,
  topology paper: distinction between intrinsic Cantor
  and ambient embedding, and finite cover by balls
  versus higher-genus tori.
  https://www.sciencedirect.com/science/article/pii/S016686411300117X
- Source details/provenance of related Antoine's necklace:
  https://d-scholarship.pitt.edu/downloads/226bd505-2a2a-4f22-8d1b-3df94e521b?locale=en
  It is a comparison example, NOT the actual Alexander
  horned ball or its own complement group.

## What is mathematically finished vs open

FINISHED AND LOCALLY CHECKED:
- 3*2^n clopen cylinder mass normalization n<=10,
  mass subdivision and address refinements;
- explicit difference between linked/unlinked finite
  3D embeddings with IDENTICAL clopen endpoint spaces;
- orientation-preserving threefold rotation of disjoint
  rational satellite charts;
- rational disjointness and C3 invariance of star handle
  centreline scaffold, tree graph (4 vertices,3 edges).

NEW SOURCE-WRITTEN AGDA (no typecheck claim):
- actual Cantor cylinder transport, sector-normalized
  mass, child splitting, prefix membership/complement.

ALREADY PROVED IN PREVIOUS AGDA SOURCES (source-level):
- abstract orbit-union invariance and induced
  complement C3 point-action;
- binary p-adic cylinder projection consistency;
- symbolic perfect torsion-free horned group tower
  conditional on correct geometric same-object.

STILL OPEN; CRITICAL:
1. A SOURCE-SPECIFIED single wild horned satellite
   embedding fitting the unit satellite ball,
   with genuine tame collared attachment disk.
2. Three disjoint cyclic copies attached by THREE
   actual 1-handles (not only centerline).
3. Prove the resulting union is B3 and that its
   boundary embeds as a wild S2.
4. Geometric Y_n open covers, contractible overlaps,
   stage-meridian commutator and INJECTIVE pi1 maps,
   then colimit identifies the exterior group.
5. Only then promote spin Dirac action to this actual
   connected exterior. A nonzero physical Dirac kernel
   remains separately unproved.

The decisive shift: not 'can we find another clopen
ball theorem?', and not 'can we prove R(B)=B once more?',
but 'can our EXISTING cylinder tree be equipped with
source-defined ambient 3D linkage plus collared
handle/gluing geometry that yields Hatcher's pi1?'.
