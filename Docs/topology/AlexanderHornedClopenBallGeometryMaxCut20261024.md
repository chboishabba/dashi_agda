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

    H_i = {t e_i: 1/2 <= t <= 17/2}, i=x,y,z

with radius epsilon=1/4 overlap their incident UNIT
balls through positive-volume cross-sectional disks,
since 1/4+1/16=5/16<1 at BOTH endpoints.
The older [1,8] cores were tangent at isolated points
and therefore did NOT define proper topological handles.
Outside the central ball, distinct tubes cannot
intersect because each axis coordinate must exceed
3/4 on its own tube while the other tube bounds that
coordinate by 1/4. Nonincident satellite balls also
remain separate. The connection graph has 4 vertices
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

## 2026-10-24 exact-head geometric/free-product correction

The previous `t=1..8` tube geometry is INVALID as a
boundary-connected sum: tangency is not a collared
attachment. The corrected original Python scaffold uses
`t=1/2..17/2` and proves positive-volume overlaps,
disjointness of tube portions exposed outside the central
ball, and separation from off-axis satellite balls.

The new `alexander_horned_three_sector_geometric_vankampen_probe.py`
proves by an all-stage free-word NORMAL-FORM argument that
the disjoint two-child commutator substitutions are injective:
for ANY reduced source word w,
`|expand(w)| = 4 |w|`. Independent local Python checked
18,112 reduced examples and exact C3 naturality.
Categorically the resulting group is
`G_three = G_A * G_A * G_A`, NOT `G_A^3`:
the previous nonabelian finite `(2I)^3` actor is a QUOTIENT
of the free product, not a presentation of its source.

A further NEW theorem: the abstract sector cycle has
exact order 3 in `Out(G_three)`, since the retraction
onto sector 0 annihilates rotated sector-0 meridians
but never annihilates conjugates of a nontrivial
sector-0 meridian. The literal SL2(F5) witness checks
120/120 conjugates. The outer-action claim does NOT
yet promote to the actual geometric exterior.

`alexander_horned_tame_cantor_ball_cylinders.py`
also supplies GENUINE nested Euclidean balls for the
tame symbolic `C3×Z2` comparator. The depth-n children
fit strictly inside parents with explicit margin
`L_n/15` and have gap `4L_n/15`. All 511
finite cylinders through depth 8 were locally checked.
They fit inside satellite unit balls, away from the
corrected spoke collars and scaled linked curves.

Finally the Hopf/unlinked comparison loops were translated
radially outward by 1/4 and uniformly scaled by 1/8,
so both entire local link pairs really FIT inside
each satellite unit ball (maximum squared radius 53/64).
These loops remain a source-defined local linking
comparison, not Hatcher's horned attaching loops.

Full source/proof/geometry report:
`Docs/topology/AlexanderHornedThreeSectorGeometricVanKampenMaxCut20261024.md`.
A collared tame disk in each actual Hatcher satellite
and simply-connected overlap for the exterior van Kampen
remain the decisive SAME-OBJECT geometric suppliers.


## 2026-10-25 source-supported inward cap + literal separator sphere breakthrough

**Primary-source progress:** Franca Lippert, *The Alexander Horned
Sphere and Bing's Hooked Rug*, §2.1–§2.2 (Figure 2, pp. 2–4),
https://www.maths.gla.ac.uk/~mpowell/WriteUp_Franca.pdf,
describes horn-stage homeomorphisms becoming the identity
away from shrinking attachment support; the wild sphere is
locally flat off its Cantor ends. Hatcher, *Algebraic Topology*,
Example 2B.2, pp. 170–172 gives the genuine individual
exterior meridian/commutator van Kampen group.

Consequently we can choose a classical supported Alexander
construction that leaves an initial round B0 inward cap
unchanged. New
`scripts/alexander_horned_supported_stable_cap_certificate.py`
checks explicit coordinates for B0 radius 3/4 in a unit
reference satellite:
  Phi(u,v,s)=(-sqrt((3/4)^2-u²-v²)+s,u,v),
  u²+v²<=1/16, |s|<=1/8.
It is a genuine local TWO-SIDED collar with an inverse
chart, not a symbolic `ClopenWitness` label.
The corrected spoke endpoint t=8.5 with disk radius
1/4 has squared satellite-centred norm 5/16<9/16,
so overlaps the ACTUAL cap-preserved wild B0, not
merely the outer reference unit container.
The local exact script passed 797 rational chart tests.
The source-supported infinite horn attachments still
have to be instantiated to declare an executable
infinite-coordinate embedding.

A much sharper geometric van Kampen separator is now
available: three literal disjoint spheres
  S_i={|x-9e_i|=4}.
Their *only* contact with the constructed solid is the
respective straight spoke, and on each sphere the
intersection is the single transverse disk GRAPH
  t=9-sqrt(16-u²-v²),   u²+v²<=1/16.
Its near axial range is 5<=t<8.5. The far root
is outside the tube; all other reference balls/tubes
lie beyond the sphere. Radius-1/4 collars around the
three S_i are disjoint. New
`scripts/alexander_horned_three_sector_separator_spheres.py`
and an independent exact-Fraction local equivalent
passed 197 rational cross-sectional checks; all-radius
claims follow from exact monotone square-root bounds.

Thus `S_i∩E=S²\closed(D²)`, an OPEN DISK, so the
exterior open-cover overlap is simply connected.
This is the proper geometric van Kampen cut; a PLANE
minus disk would instead have pi1=Z and must not
be used as though it were simply connected.

New comprehensive source-attributed proof note:
`Docs/topology/AlexanderHornedSupportedCapSeparatorVanKampen20261025.md`.
It spells out how a threefold collared boundary
connected sum can yield B3 and, using the standard
unknotted-tree-neighbourhood/side-cap equivalences,
`pi1(E)=G_A*G_A*G_A` with outer C3.
This is a **paper-level source-supported geometric
proof scheme** with exact local geometry; the native
infinite horn support map and all ambient deformation
retractions are NOT machine-proved or explicitly
coordinate-constructed in the repo.

This discharges the earlier vague *existence of a tame
cap as an unexplained input* by pointing to and using the
actual supported original horn construction. The
remaining max-cut is no longer 'find separating spheres',
but instantiate its *supported infinite attachment*
and the complement-piece homeomorphisms as concrete
same-object maps. No Agda/CI work per user request.

## 2026-10-26 maximal clopen spatial-realisation cut and newest-PR cross-check

### New positive result: actual embedded Cantor end-control (NOT wild ends)

The existing `scripts/alexander_horned_tame_cantor_ball_cylinders.py`
already gives closed Euclidean balls at each *chronological* word
`w=(b_0,...,b_(n-1))`:
`L_n=3^(-n-1)`,
`a(w)=1/6+sum_{j<n} 2b_j/3^(j+2)`,
`center(w)=(a(w)+L_n/2,1/2,0)`, and radius `3L_n/5`.
All balls are strictly nested inside their parents, with child
containment margin `L_n/15` and sibling gap `4L_n/15`.
This is source-existing geometry, not invented for the current cut.

Taking the inverse limit **on these actual balls** gives the explicit
map (after applying the sector affine rotation/translation)
```text
F(c,b) = 9 e_c + R^c ( 1/6 + Σ[j>=0] 2 b_j / 3^(j+2), 1/2, 0 )
R(x,y,z) = (z,x,y).
```
Indeed the infinite tail after the first n bits lies in
`[0,L_n]`, so the resulting point lies in every corresponding
ball; diameters `6L_n/5` tend to 0. Distinct words first
disagreeing at bit n land in strictly separated sibling balls.
The map is continuous in the cylinder/product topology, injective,
and therefore a homeomorphism to its image by compactness of
`C3 × {0,1}^N` and Hausdorffness of R³. Its image is literally
three rotated/transplanted **affine middle-thirds Cantor sets on
straight lines**, an explicit **tame comparator**. The inverse
images of level-n balls restrict to clopen subsets of that
Cantor image, NOT ambient-clopen subsets of connected R³/E.
`R F(c,b)=F(c+1 mod3,b)` exactly.

This is an actual embedded endpoint realisation, not merely the
symbolic `ClopenWitness` status constructor in SSP369, and it
still does NOT identify the Cantor **wild-point image** of
Hatcher's embedded sphere or compute its complement π₁.

The new exact-head standalone executable
`scripts/alexander_horned_c3_clopen_spatial_realization.py`
has been independently executed, with Python `py_compile` PASS,
511 checked binary prefixes at depths 0..8 and 1533
sector-prefix ball checks. The exact local Git blob SHA
`32cad631dbf679c90a8af717a618c0dd14d41363`
MATCHES the repository's fetched file blob, not just a
locally equivalent prototype. The mathematical all-depth statements
are supported by the displayed formulas and standard topology
theorems; finite runs do not prove the latter in Lean/Agda.

### The newest PR #1254 paid a genuine *address-orientation* defect

Latest stacked [#1254](https://github.com/chboishabba/dashi_agda/pull/1254)
adds `ExoticCantorCylinderOrientationExact.agda`, using
the **existing** `CantorProjectiveCylinderMeasureExact` and
explicitly proving the difference between *PREPEND* storage
and *APPEND* chronological stream-cylinder events.
It gives a real counterexample: chronological parent `[true]`
is NOT an event containing the old prepended child
`[false,true]`. Although both child words have the
expected dyadic mass, event inclusion is false without
the orientation reversal. The new parent Python bridge
uses `chronologyOfStack(b :: reverse(w)) = w ++ [b]`;
it does not duplicate or silently import #1254's source-written
Agda theorem. This parent-to-child dependency direction matters
because #1254 is STACKED on this PR, currently unmerged.

[PR #1266](https://github.com/chboishabba/dashi_agda/pull/1266)
offers a consumer-relative collision criterion; [#1267](https://github.com/chboishabba/dashi_agda/pull/1267)
sets severe-test/provenance discipline. Neither is a
kernel receipt for the present geometry. The existing
`alexander_horned_clopen_linking_impasse_probe.py`
already supplies a linked versus unlinked comparison with
the SAME abstract cylinder events/masses; do not duplicate
that finite linking witness or claim it alone realises Hatcher's
punctured-torus attachments.

### Source genealogy and remaining high-payoff supplier

**Original roots:** J. W. Alexander (1924), wild sphere;
A. Hatcher, *Algebraic Topology*, Ex. 2B.2, supported
horn/handlebody stages and van Kampen commutator tower;
F. Lippert, *The Alexander Horned Sphere and Bing's Hooked
Rug*, a separate support and wild-point exposition;
standard middle-thirds Cantor construction and the classical
compact-to-Hausdorff embedding theorem. **Existing code owners:**
DASHI `CantorProjectiveCylinderMeasureExact`, binary horn-address
and `SSP369ClopenBallBridge`, the already-created Euclidean tame
ball script, plus the #1254 orientation correction.
**New contribution this cut:** the explicit endpoint limit map,
same-object C3 affine transport and regression verifying the
chronological/stack/ball commuting square.

**P0 remaining:** an actual *wild* pillbox/linked-handle
realisation of Hatcher `X_n` for every n, with a
source-defined collared cap, ambient inclusion
`X_(n+1) ⊂ X_n`, and inclusion-induced meridian map
`x_w ↦ [x_w0,x_w1]` proved by the corresponding
punctured-torus geometry. The group injection then uses
the ALREADY EXISTING algebraic proof; do not treat the
tame embedded `F` above as the wild one. **P1:** actual
satellite-relative collar map and based `C3` naturality
into the existing Lean `ThreeArmCentralPi1Reduction`.
**P2:** physical gauge/Dirac observables remain independent.

The epistemic stop rule is exact: positive clopen/cylinder
results establish a tame end image and cylinder-event topology;
an abstract homeomorphism between Cantor end spaces does not
transport ambient linking, a handlebody complement, local
wildness, exterior group or physical nonabelian holonomy.
No Agda or Lean kernel check or hardware measurement is claimed.
