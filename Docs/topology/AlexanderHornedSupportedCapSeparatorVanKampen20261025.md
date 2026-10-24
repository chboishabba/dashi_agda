# Supported Alexander satellite + exact C3 separator spheres: van Kampen max-cut

Date: 2026-10-25 (Australia/Brisbane), PR #1244, branch
`alexander-horned-c3-equivariant-20261024`.
This is a *mathematical construction and finite geometry certificate*, not a
machine-verified geometric proof or a claim of physical Dirac zero modes.

## Original roots, not new inventions

**J. W. Alexander (1924)** built the wild embedded sphere.

**Allen Hatcher**, *Algebraic Topology*, Example 2B.2, printed pp. 170–172,
https://pi.math.cornell.edu/~hatcher/AT/AT.pdf, derives the actual one-root
exterior group as an injective direct limit of F_(2^n), sending each parent
meridian to a commutator of two new child meridians. Proof source:
punctured torus, honest geometric van Kampen, compactness.

**Franca Lippert**, *The Alexander Horned Sphere and Bing's Hooked Rug*,
§§2.1–2.2, especially pp. 2 and 4,
https://www.maths.gla.ac.uk/~mpowell/WriteUp_Franca.pdf,
explains the *support of the stage homeomorphisms*:
the homeomorphisms between nested B_n are identity away from shrinking
horn-attachment neighbourhoods. See her Figure 2. In §2.3 she confirms
local flatness off the Cantor wild set. This supports selecting a cap
on the untouched initial B0 boundary that survives every stage.

Neither Hatcher nor Lippert claims OUR three-sector geometry or exact
rational satellite coordinates; this report makes that new gluing
argument explicit.

## 1. A tame cap from actual Hatcher/Lippert support

Model the initial round B0 with radius a=3/4, centred at origin, and
concentrate every Hatcher horn attachment in its OUTWARD hemisphere.
The cap on the inward hemisphere is disjoint from all attachment
supports and is therefore unchanged under every stage map h_n and
its uniformly convergent limit f. This is a direct support consequence,
not a new axiom that all wild spheres have globally collared boundary.

Choose normal coordinates x along the inward-to-outward axis, with
the inward hemisphere at negative x; u,v are orthogonal.

For (u²+v² <= (1/4)², |s|<=1/8), define

  Phi(u,v,s) = (-sqrt(a²-u²-v²)+s, u, v).

This is an explicit local collar of the ROUND sphere at s=0:
the inverse on the image is

  (x,u,v) -> (u,v,s=x+sqrt(a²-u²-v²)).

The supported wild ball agrees with B0 in this chart. s>0 is the
interior side, s<0 exterior; the sign statement follows directly from
norm²= a²-2s sqrt(a²-u²-v²)+s², and |s| is sufficiently small.

Crucial identity:

  a²-(1/4)² = 9/16-1/16 = 1/2 > (1/8)².

Thus the inward local graph and its collar are well-defined and
separated from all horn support chosen in x>=0.

**Source-specific geometry supplier:** choose the standard horn
construction to fit inside the ambient unit reference ball while
leaving this a=3/4 inward cap stationary. Classical horn stages
can be placed in arbitrarily small upper-side support and each
subsequent stage in shrinking horn neighbourhoods. The exact
shrink/attachment homeomorphisms are **not yet coded** as a
coordinate-by-coordinate infinite embedding in DASHI, but
existence follows from the cited supported construction and
elementary ambient scaling/isotopy.

New `scripts/alexander_horned_supported_stable_cap_certificate.py`
checks the rational inequalities and 797 finite collar samples.
Finite sampling is not claimed to prove the limit-source support.

## 2. Place three supported copies and truly attach the tube

Let e_0,e_1,e_2 be standard coordinate axes and

  C_i = 9 e_i,     R(x,y,z)=(z,x,y).

Place three congruent copies B_i of the supported wild ball inside
the unit reference ball centred C_i, rotating each by R.
Their inward tame caps face the origin.

Let B_c be the standard central unit ball. Define actual 3D
radius-1/4 tubes (solid cylinders)

  T_i = { t e_i+v: 1/2<=t<=17/2,
                    v perpendicular to e_i,
                    |v|<=1/4 }.

At t=17/2, relative to C_i, the full endpoint disk satisfies

  |-1/2 e_i+v|² <= 1/4+1/16=5/16 < a²=9/16.

It lies in B0 and hence in the unchanged region of the WILD ball.
Thus the tube REALLY overlaps the chosen wild satellite in positive
volume. At t=1/2 it likewise overlaps B_c. This corrects the original
[1,8] tangent-only failure, and is stronger than showing intersection
with the outer unit reference ball.

The existing corrected scaffold proves pairwise exposed-tube
separation and disjointness from all other satellites. Because the
local cap is standard and the connector is a product tube, both
attaching disks are bicollared/tame.

Boundary connect-summing four topological 3-balls along this
three-edge TREE produces a topological B3. A proof by induction
uses the fact that D3 union (D2×I) union D3 along two collared
disks is D3, preserving another pair of disjoint attachment disks.
This classical gluing theorem requires the actual support/collar
model above and is not inferred just from the 4-vertex graph.

The resulting compact B is C3-invariant: R permutes the three
satellite copies, all tubes, and fixes B_c. The wild end set is the
disjoint union of three cyclic images of the classical Cantor wild
set, hence intrinsic C3×Z2. This does NOT make E=S3\B clopen.

## 3. Three EXPLICIT separating spheres, not guessed overlaps

For each i define

    S_i = {x in R3: |x-C_i| = 4}.

Each S_i contains its entire satellite B_i since B_i is inside
radius 1. It avoids the central B_c (distance 9>4+1), every
other satellite (centre distance sqrt(162)>5), and every
off-axis tube (coordinate distance >=9-1/4>4).

It intersects ONLY the incident tube T_i. Write points of this
tube as (t,u,v) in sector-aligned coordinates. On S_i,

    (t-9)²+u²+v²=16.

For u²+v²<=1/16, precisely one axial branch lies in the tube:

    t(u,v) = 9 - sqrt(16-u²-v²),

with t between 5 and 9-sqrt(255)/4 < 8.5. The OTHER root is
>9>8.5 and hence outside T_i.

So S_i∩B is **exactly the embedded closed disk** which is
the graph over u²+v²<=1/16. Its boundary is transverse to
the tube side because t-9!=0.

The three S_i are mutually disjoint since sqrt(162)>8.
Even their radius-1/4 ambient collars are disjoint.
The new
`scripts/alexander_horned_three_sector_separator_spheres.py`
checks the exact rational inequalities and 197 sampled
cross-sections; the all-r result uses monotonicity of sqrt,
not bounded enumeration.

A sphere S_i with a single closed disk removed is an OPEN
2-disk. Thus

    S_i∩E = S²\D²  ~=  R²

is simply connected, and a small product collar in E has
simply connected overlap. **This is the correct van Kampen
interface.** A transverse Euclidean PLANE minus a disk would
instead be annular, with pi1=Z, so using that plane as the
van Kampen overlap would be a substantive error.

## 4. Van Kampen gluing — exact theorem and remaining proof granularity

Let E=S3\B. Cutting E along the three S_i separates
the central exterior region from three satellite regions.

- The central region consists of an unknotted tree handlebody
  complement with three trivially collared boundary mouths.
  Its pi1 is trivial: the regular neighbourhood of a planar
  embedded tree is an unknotted B3; truncating at separating
  spheres through its three standard spokes removes only
  boundary collar pieces.
- Each satellite region has pi1 equal to that of the chosen
  Hatcher satellite exterior E_A. Extending a standard
  tame collar/unknotted tube to a separating sphere changes
  neither the complement's homotopy type nor its pi1.
- The overlaps are simply connected open disks times intervals
  by §3, and the graph of region adjacencies is a STAR, so
  repeated van Kampen gives

    pi1(E) ~= G_A * G_A * G_A.

- At finite horn stage n, the same splitting spheres and
  SAME external tube geometry separate three copies of
  Hatcher's stage E_{A,n}. Thus

    pi1(E_n) ~= F_(2^n) * F_(2^n) * F_(2^n)
              ~= F_(3*2^n).

- The bonding maps are independent blockwise meridian
  commutator maps, so each map is injective, as was proved
  algebraically in
  `scripts/alexander_horned_three_sector_geometric_vankampen_probe.py`.
  Compactness of loops and homotopies in the increasing
  exterior-stage union gives the colimit.

Caveat: the central-piece and satellite-piece homotopy
comparisons above use conventional tame collar/unknotted
tree neighbourhood facts. This report gives the key
separating spheres and explicit charts, but DOES NOT
formalize the whole ambient homeomorphism or every
open-cover deformation retraction in Agda or Python.
It is therefore a **source-supported paper-level proof
outline**, not a kernel-certified geometric theorem.

The support condition on the chosen actual Alexander
satellites (not on the reference unit balls) is decisive.
The new stable-cap calculation pays its LOCAL chart,
while Hatcher/Lippert pay the ORIGINAL infinite
horned-ball existence and wild exterior pi1. Keep those
different attribution/proof statuses.

## 5. The geometric rotation can now carry the outer action

Use a basepoint on the fixed diagonal R-axis far outside
B, e.g. x0=(20,20,20). Cyclically transport connector
paths through the ordinary central exterior.

Under the source-supported gluing identifications the
spatial rotation sends each satellite's meridian tower
to the next tower without changing its internal
commutator pattern. Hence on

    G_A * G_A * G_A

it is the factor permutation automorphism (up to
inner conjugation from path choices).

The previous retraction argument proves its image in
Out(G_A*G_A*G_A) has exact order THREE: no nontrivial
factor permutation can be inner.

This is useful positivity, distinct from the statement
that every central C2 extension of C3 splits.

The compatible finite spin quotient remains
`(2I)^3 rtimes C3`, with faithful GL12(F7) actor,
and the stable open exterior admits a coherent
discrete C3 action on compactly supported spinors.
No physical Dirac zero mode or Monster VOA identity
follows from this topological construction.

## 6. Deliverables and remaining Pareto set

IMPLEMENTED now:
- supported round a=3/4 inward cap and explicit
  boundary collar source/geometry certificate;
- full disk overlap with the ACTUAL preserved cap of
  a supported classical wild satellite;
- 3 exact radius-4 separating sphere disks and a
  certified transverse collar, all C3-related;
- corrected source group free product and
  geometric outer C3 action transport plan.

Previously implemented:
- all-stage source commutator injection by literal
  reduced-word normal form;
- finite 2I/A5 quotient and spin4/spin12 representations;
- binary/C3 Cantor cylinders, finite mass, tame comparator;
- local linking and true positive-volume star handles.

Remaining **machine-independent topology**:
1. Write an explicit supported-stage coordinate map for
   ONE chosen Hatcher horn/pillbox model showing that
   every upper horn stays inside its satellite outer
   radius-1 container without touching the inward cap.
   The cited construction assures this can be arranged,
   but current scripts encode only its support contract.
2. Supply explicit ambient homeomorphisms/retractions
   for central and satellite complement pieces after
   cutting along the S_i (rather than relying on
   standard collar/regular-neighbourhood results).
3. Write the actual equivariant stagewise open-cover
   gluing as a native topology development if
   kernel certification becomes a priority.

Per user instruction, Agda typechecking and CI are
not pursued here. No result is promoted to kernel
certification from local finite checks.
