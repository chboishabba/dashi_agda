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


## 7. A NEW genuine interpretation of external C3: orbifold isotropy

The previous symbolic `G_three rtimes C3` is not an
unexplained second fundamental group. Once the supported
threefold-invariant wild-ball construction is realized,
take E=S3\\B and a fixed R-basepoint well outside the
compact solid, e.g. x0=(20,20,20). This point is fixed by
R(x,y,z)=(z,x,y) and lies outside the central ball,
all tubes and the satellite unit containers.

Consider the global quotient orbifold `[E/C3]`, not
the ORDINARY topological quotient space `E/C3`.
Its classifying space is the Borel homotopy quotient
  E_hC3 = EC3 ×_(C3) E.

Because E is connected, the fibre sequence
  E -> E_hC3 -> BC3
gives a fundamental group extension
  1 -> pi1(E,x0) -> pi1(E_hC3,[x0])
      -> C3 -> 1.
Since x0 is a C3-fixed point, its constant inclusion
induces a SECTION `BC3 -> E_hC3`. Thus this exact
sequence splits naturally, with the specified action:

  pi1^orb([E/C3],[x0])
      ~= pi1(E,x0) rtimes C3.

After the geometric equivariant van Kampen identification
in §4, this becomes
  (G_A * G_A * G_A) rtimes C3.

THIS IS A POSITIVE TOPOLOGICAL ANSWER to the old
'how can horns twist if their exterior pi1 is torsion-free?'
The ordinary loop group of E remains torsion-free;
the true external C3 is isotropy/automorphism data
in the ORBIFOLD quotient, not an element of pi1(E).
The chosen spin3 lift of the spatial C3 is separately
a splitting of the pulled-back Spin3 cover; it is
compatible with, but not the same group as, the
orbifold pi1.

The distinction between orbifold π1 and ordinary quotient
π1 matters here: the isotropy at a fixed point can be
forgotten by taking the underlying coarse quotient.
Do not call either group simply `pi1(E/C3)` without
specifying which topology/stack is intended.

Primary/survey source on global quotient orbifolds and
their fundamental groups:
Francisco C. Caramello Jr., *Introduction to Orbifolds*,
arXiv:1909.08699, §§1.1,2.2, and Borel construction;
https://arxiv.org/pdf/1909.08699.

New independent finite instance:
`scripts/alexander_horned_orbifold_split_c3.py`
certifies the concrete fixed x0 and the compatible
120-element SL2(F5) quotient semidirect law and section.
The Borel-fibration theorem is classical proof input;
the script does not construct the infinite topological
covering space.


## 2026-10-25 roadmap reset: FINITE vs INFINITE physical observables

New source-audited decision report:
`Docs/topology/AlexanderHornedRoadmapRealWorldImplications20261025.md`.

**Critical Hatcher object discriminator:** `B_n` is a
locally-flat/tame finite horned BALL with simply connected
exterior (Schoenflies), whereas Hatcher's stage enclosure
`X_n` is a genus-`2^n` handlebody with nontrivial
exterior `Y_n` and `pi1(Y_n)=F_(2^n)`.
For three independent sectors, stage group rank is
`3*2^n`. The ideal limit `B=intersection X_n` is
the source of the perfect but nontrivial exterior group.
Do NOT use a finite printed B_n and falsely advertise
the complement group of X_n or the ideal limit.
Original: Hatcher Example 2B.2 (printed pp171-172)
and locally-flat Schoenflies.

**Essential noncommutation of limit/abelianization:**
Each source meridian becomes a child commutator, so
H1(Y_n)->H1(Y_(n+1)) is the ZERO map despite each
H1(Y_n)=Z^(3*2^n). Thus H1(E)=0 while
pi1(E) is nontrivial. In R3 the exterior also has
H2(E)=Z from the sphere at infinity; in S3 the
complement of the compact contractible ball is
reduced-acyclic. Do not call R3 exterior fully acyclic.

**Flat U1 vs nonabelian holonomy**:
Hom(perfect G,U1)=1; each isolated finite free stage
has nontrivial U1 characters that cannot be carried
compatibly through all commutator refinements.
In contrast existing 2I=SL2(F5) perfect quotient
has an order-six root q with q^3=-I, recursively
compatible child commutators and spin-character
Wilson trace -2. Nonflat Maxwell connections can
still have Wilson loops on contractible paths.
A one-level Q8 commutator [i,j]=-I works, but
Q8 cannot extend recursively: [Q8,Q8]=C2.
The perfect 2I target is essential for ALL scales.
Executable finite audit:
`scripts/alexander_horned_scale_holonomy_maxcut.py`.

**Actual experiment/control roadmap:** finite sculpture,
finite X_n handlebody, and unlinked/tame controls must be
labelled DIFFERENT specimens. A synthetic SU2/optical
control circuit may implement recursive commutator
identities and observe relative Wilson phases; this is
not direct observation of the infinite wild pi1.
Prior published physical feasibility roots: Lucien
Grillet's FOUR-level 20cm PLA/PVA horned sculpture,
Bridges 2022; Q. Liang et al. Nature Physics
(2024), DOI 10.1038/s41567-024-02644-4
synthetic SU2 nonabelian AB in a 1D ladder, and
Sugawa et al. npj Quantum Information (2021)
nonabelian Wilson-loop measurements.
No original DASHI experiment currently exists.

**Quantitative synthetic signature:**
`scripts/alexander_horned_su2_controls_noise_probe.py`
verifies exact quaternion algebra
`tr([A,B]) = 2-4 sin²(alpha) sin²(beta)` for
orthogonal-axis SU2 controls; at alpha=beta=pi/2
this is -2 versus commuting U1 +2. Angular control
errors change the trace; a lone global -1 spinor sign
must be measured against a reference. One SU2
commutator does not prove the whole tower's perfectness.

**Hard acceptance gates:** actual supported Hatcher
infinite horn coordinates and cap, the three piecewise
open-cover/van Kampen homotopy maps, CAD models with
known finite stage group, calibration/flatness controls,
specified Maxwell/Dirac operator and boundary data.
No implication of gravity anomalies, free energy,
superluminal communication, quantum consciousness or
new physical zero modes.

The work priority is a dual track: geometry source
same-object closure plus practical finite nonabelian
control experiment; defer Agda typecheck/CI by request.


## 2026-10-25 dual-track implementation max-cut — GEOMETRIC PAPER THEOREM + EXECUTED GAUGE SIMULATOR

**GEOMETRY:** New `Docs/topology/AlexanderHornedC3SameObjectGluingTheorem20261025.md` supplies the full source-attributed paper-level existence argument for a 3-sector equivariant wild B3: choose the Hatcher/Lippert horn seed with an unchanged inward tame disk, attach three rotated supported copies to the central unit ball with actual tame radius-1/4 collars, cut by three radius-4 spheres and use classical boundary-connected sum and van Kampen. The NEW explicit stereographic coordinates
  sigma(t,u,v)=(u/(t-5),v/(t-5))
map each geometric cut-sphere exterior overlap homeomorphically to the OPEN disk `|y|<16+sqrt(255)`; inverse
  t=(13+5|y|²)/(1+|y|²), u=8y1/(1+|y|²), v=8y2/(1+|y|²).
It contracts by `H_s(y)=(1-s)y`, so a collar overlap is simply connected. That removes a vague topological-overlap assumption and uses actual source-defined tubes/caps. The usual tame-collar replacement argument identifies satellite-side pi1 with original Hatcher `G_A`; the round-star control establishes central-side pi1 trivial. The cut-and-paste theorem then yields `pi1(E)=G_A*G_A*G_A` and outer C3 at a fixed basepoint. Original wild embedding / its stage theorem and standard 3-manifold lemmas remain EXTERNAL CLASSICAL theorem inputs, and an indexed infinite coordinate map / kernel proof is STILL NOT coded. Code: `scripts/alexander_horned_C3_same_object_separator_atlas.py`. Locally validated 2601 stereographic and 797 cap-chart samples, with exact rational identities and explicit inverse.

**EXECUTED SYNTHETIC SU2 GAUGE MODEL:** New `scripts/alexander_horned_c3_finite_SU2_gauge_simulator.py` constructs all 120 binary-icosahedral unit quaternions over Q(phi), checks all group products, finds exact commutator witnesses for ALL 120, selects `q=(1+i+j+k)/2` whose cube is `-1`, and assigns Hatcher child meridians compatibly through selectable finite depth. Ideal selected root-cube Wilson halftrace is `-1` for all depths; matched commuting U1 halftrace `+1`; Q8 yields central `-1` at ONE level but cannot maintain full recursion. Model applies independent gate-axis-angle noise and Bernoulli controlled-U readout shots. A locally executed source-equivalent 50-trial/300-shot/1.5deg simulation returned depth-0..5 observed halftraces `[-0.9999,-0.9995,-0.9955,-0.9828,-0.9437,-0.8032]` with gate costs `3*4^n`. They are **synthetic** predicted readouts, not laboratory measurements. Added six `test_alexander_horned_C3_gauge_simulator.py` tests for C3 factors, commutator compatibility, gauge conjugacy invariance, Wilson orientation limitation and reproducibility; equivalent local test suite PASS 6/6.

**TRUE C3-UNITARY LAB ACTOR:** New `scripts/alexander_horned_C3_three_channel_SU2_actor.py` realizes `(2I)^3 rtimes C3` faithfully on THREE complex SU2 spin doublets, so `(2I)^3 rtimes C3 -> U(6)` by 2x2 quaternion matrices and C3 block permutation. It carries the selected cube as `diag(-I2,I2,I2)`, which disappears in A5 quotient. Independent equivalent local test PASS all 120 SU2 matrices, 300 products and sampled actor associativity. This complements the earlier minimal GL4(F7)/full GL12(F7) arithmetic actors but is more experimentally actionable.

**TRUE PHYSICAL BRIDGE, NOT AUTOMATIC SPIN CURVATURE:** a homomorphism `rho:pi1(E)->2I->SU2` supplies an AUXILIARY flat SU2 local system `(E_tilde x SU2)/pi1(E)`, by standard flat-bundle/holonomy reconstruction (Goldman-Millson 1988; standard Riemann–Hilbert). This proves mathematical existence of a specified flat nonabelian connection on the ideal wild exterior, but NOT a physically realized connection or an effect of the Euclidean Levi-Civita spin connection. Wilson trace alone is invariant under conjugation and cannot distinguish q from q^-1; additional matrix tomography is gauge-frame-dependent. A graph circuit has its OWN finite free-group topology and must not be advertised as a measurement of the infinite horned complement.

**PHASE GATES NOW:** (0) source/provenance — done; (1) abstract free group/C3/2I/spin — mathematical and finite done; (2) geometric existence — classical paper-level gluing proof supplied, entire infinite ambient map code still open; (3) geometric van Kampen — explicit cut atlas complete, standard source collar/round-star homeomorphism invoked rather than kernel-certified; (4) runnable finite synthetic gauge emulator — DONE / locally executed; (5) full three-channel C3 complex actor — DONE / finite locally verified; (6) physical apparatus/actual gauge measurement — NOT DONE; (7) specified PDE spectral experiment — NOT DONE. No Agda or CI work by user request. Full technical protocol `Docs/topology/AlexanderHornedC3GaugeSimulatorExperimentProtocol20261025.md`.
