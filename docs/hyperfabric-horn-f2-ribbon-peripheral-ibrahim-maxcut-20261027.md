# Hatcher F₂ peripheral source: actual finite straight-tube meridians and ribbon boundary discriminator
Date: 2026-10-27 Australia/Brisbane.
Work lanes: Agda hyperfabric PR #1249; Lean conditional mirror PR #84.
Original horned C3 relative satellite geometry remains PR #1244.

## Attribution / original sources / exactly what is being proved

* Allen Hatcher, *Algebraic Topology*, Example 2B.2
  pp171–172, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf:
  original local F₂ group on two exterior meridians,
  and crucially a once-punctured torus whose incoming
  annulus class represents NONTRIVIAL [alpha1,alpha2].
  The text was independently inspected in the actual
  author-PDF page images, not inferred from cartoons.
* Classical oriented ribbon-graph / rotation-system
  surface construction: vertex cyclic order sigma,
  dart flip alpha, boundary permutation phi=sigma∘alpha.
  SageMath `Ribbon Graphs` manual
  https://doc.sagemath.org/html/en/reference/discrete_geometry/sage/geometry/ribbon_graph.html
  is a later source/implementation of the standard
  topological thickening, not its original inventor.
* Agda exotic topology #1254 already owns constructive
  finite PL pairs-of-pants and genus/boundary checks.
  Our four-dart ribbon-source **specialisation** does
  NOT reassign or reproduce the #1254 PL triangulations.
* Agda horn #1244 owns C3 satellite embedding,
  three-arm Euclidean ambient cover and newly sourced
  Hatcher-at homotopy-equivalence / based-path transports.
  It does NOT currently provide the actual wild
  satellite relative homeomorphism/equivalence or
  the marked Hatcher meridian metric chart.
* Earlier Agda #1249 and Lean #84 own selected W spectral
  norm²>517/250 and conditional child operator gap
  >781/1000. Original W selected in neutrino #1247.
* New user-directed formal implementation attributed
  to Johl Brown with OpenAI ChatGPT assistance;
  original group/ribbon topology belongs to its
  mathematicians, not software contributors.

## Correct SOURCE TYPE: straight-two-tube open local model

Define the explicit 3D straight-tube complement

    U = (D²_radius3 \ (D̄_{1/8}((-1,0))
                      ∪ D̄_{1/8}((1,0)))) × (-1,1).

This is an open 3-manifold homotopy equivalent
to a planar twice-punctured disk, with
π₁(U) ≅ F₂, not the Hopf ℤ².

Take local meridian circles of radius b=1/4
about the two solid vertical tube cross-section
centres (−1,0),(1,0) in plane z=0.

* Both are actually in U: positive own solid
  clearance b−a=1/8 and foreign core solid
  clearance >=2−b−a=13/8.
* Both lie in radial disk radius3 and are
  the two standard free generators up to
  coherent basepoint whiskers.
* Under the already-owned #1244 affine source
  satellite scale 1/8, both meridians have
  actual finite MODEL Euclidean length

      L=2π(1/4)(1/8)=π/16<11/56≈0.19643,

  hence are much smaller than selected-source
  norm gap threshold 781/1000 for the **synthetic
  model bound M=1**. This is NOT a source-W
  flat connection: any actual representation with
  large child gap must pay a correspondingly
  larger compatible M or different geometry.
* Original C3 rotation transports this model's
  lengths and all strict inequalities to three
  satellite REFERENCE envelopes.

These are REAL finite embedded local source-model
loops of the right ABSTRACT group type F₂.
The model still does not establish that its
loops inhabit Hatcher's *actual wild-linked*
relative Z region, avoid the entire true stage,
or correspond to the source annulus.

## A second, independent acceptance criterion: peripheral ribbon order

Use the bouquet with one vertex and two oriented
loop edges a,b (four darts a,A,b,B, with
A=a⁻¹, B=b⁻¹). The edge-reversal involution
alpha=(a A)(b B) is FIXED for both models.
Only the cyclic ribbon rotation sigma changes.

**Hatcher-compatible abstract positive**:
cyclic vertex order sigma=(a B A b).
Define boundary successor phi=sigma∘alpha.
Its one orbit is

     a -> b -> A -> B -> a.

This is one boundary component with actual
word a b a⁻¹ b⁻¹=[a,b].
A connected ribbon thickening retracts to
one vertex and two edges, so χ=V−E=−1.
For an orientable compact surface with
b_boundary=1, 2−2g−1=−1 => g=1:
the ONCE-PUNCTURED TORUS corresponding to
Hatcher's incoming annulus commutator.

**Severe opposite on the EXACT SAME free graph**:
cyclic vertex order sigma=(a A b B).
Then boundary successor phi has three cycles:

     (a b), (A), (B).

It STILL retracts to the same abstract F₂
and has the same χ=−1, but
b_boundary=3 =>g=0: a THREE-HOLED SPHERE
(pair of pants), not the specified once-
punctured-torus annulus with its one
nonzero boundary commutator.

Therefore neither a correctly typed F₂
group nor the two Euclidean local meridian
length bounds automatically pays the
**PERIPHERAL** Hatcher parent generator:
the cyclic ribbon/relative annulus map
must also be source-certified.

The previously added Hopf link comparator is
an even earlier wrong-source negative:
it has excellent two-core linking, C3,
shorter local meridians (π/32<11/112),
but the entirely wrong group π₁=ℤ²,
so its parent commutator vanishes under
EVERY flat receiver representation.

These THREE tests form a strict source ladder:

| Comparator | Actual finite local group | Ribbon boundary/parent relation | Actual local metric | Valid Hatcher infinite source? |
| --- | --- | --- | --- | --- |
| Original-owner Hopf two closed linked cores | ℤ² | all meridian commutators zero | π/32 short and clear | NO |
| Two straight deleted cores with nonalternating ribbon | F₂ | three pants boundaries, not one annulus [a,b] | π/16 short and clear | NO |
| Same two straight deleted cores, alternating ribbon | F₂ | one punctured-torus boundary [a,b] | π/16 short and clear | FINITE LOCAL MODEL ONLY |

The final row passes the original *abstract local*
word/topology/peripheral/metric shape, but still
lacks the actual Hatcher Z-to-satellite ambient
embedding and WHOLE-STAGE avoidance with controlled
distortion across depth. Do not treat finite
topological models as same-object claims.

## Implementation and exact check status

New `scripts/check_horn_local_f2_ribbon_boundary_source_cut.py`
is committed on Agda #1249. It computes the exact
straight-tube local geometry, length, full 4-dart
permutation boundary cycles, orientable genus from
Euler characteristic, free reduced commutator
nonzero and abelianized zero, and original C3
satellite transport. A separately implemented
local Fraction model reproduces the 1-boundary
genus1 commutator / 3-boundary genus0 difference
and exact metric inequalities: PASS. The
committed Python file was fetched from GitHub,
but its exact bytes were NOT replayed in local
Python, so don't promote that specific status.

New source-written Lean #84
`Integration/DASHITOE/HornHatcherRibbonPeripheralOrderCut.lean`
proves by finite enumeration the four boundary
successors for both rotations, the edge flip
involution, the genus/Euler integer arithmetic,
and the rational metric acceptance.
The classical ribbon graph realisation into
oriented surfaces and the actually EMBEDDED
Hatcher relative wild source remain EXTERNAL.
No Lean/Lake/Agda kernel verified proof,
CI receipt, 3D infinite linked wild stage
or physical Wilson measurement was produced.

## Pareto snowball / Ibrahim STOP: precise wall after paying all finite types

P0 source original: provide the actual supported
wild Hatcher satellite W_i and a true relative
homotopy equivalence to the canonical
`ThreeArmHatcherHomotopyTransport.lean`/
`ThreeArmHatcherPathTransport.lean`
owner interfaces on #1244, preserving the
named two F₂ meridians and **punctured-torus
one-boundary peripheral class**.
A group isomorphism without marked-peripheral
data is INSUFFICIENT: the same F₂ can carry
the different pants ribbon.
The topological marked annulus must be
constructed IN THE ACTUAL EMBEDDED STAGE,
not assumed by a model diagram.

P1 SAME SOURCE Euclidean metric: transport
one actual Hatcher source first-stage
meridian local rectifiable representative
with entire finite X_n exclusion and a
Lipschitz/arclength budget. Only THEN consume
the existing exact source-selected W flat
M L<=781/1000 contradiction or every-branch
systole test (31/60M). The finite straight-tube
L<11/56 model has no right to instantiate
this wild-source physical premise.

P2 genuinely BASED Hatcher curved
punctured-torus/commutator homotopy,
transported curvature integral eta
(the earlier accepted selected-W window
child<=3/4 and eta<=23/500 applies).
The ribbon's Euler characteristic does
not supply an extrinsic surface area.

P3 native Agda/Lean kernel execution and
an actual source-selected anomaly-free
gauge/matter action; no selection of lepton
properties from abstract group data.

Attributions remain independent:
source document existing ≠ source statement
≠ topological proof ≠ source-written code
≠ exact test receipt ≠ kernel theorem
≠ gauge action or experimental measurement.
No invented QID/Dewey data or duplicate
claims of original mathematical priority.


## Same-object refinement of finite positive comparison

The two short meridians are ACTUAL curves in the stated
straight-tube complement U. The alternating cyclic
order is an ACTUAL four-dart ribbon-graph thickening
type with a single commutator boundary. The current
certificate does NOT construct an EXPLICIT EMBEDDING
of that precise orientable punctured-torus ribbon
into the SAME Euclidean U, with the ribbon core
curves identified pointwise with the two metric
meridians and one peripheral attaching annulus.
Thus even at the finite positive-model level,
group + length + abstract ribbon data are
individually proved but their JOINT AMBIENT
geometric realization is a named unfulfilled
same-object source obligation. Do NOT count it
as an actual Hatcher local Z matching theorem.

This is the next meaningful micro-Pareto problem
inside P0: an embedded marked punctured-torus
surface with explicit boundary loop, genuine
U inclusion, and a based word computation,
before source-relative extension to the wild
satellite and all stages. It is still distinct
from constructing the actual infinite wild
Hatcher stage, and no physical source can
consume the isolated model yet.

New additional Agda exact finite half-edge
source `DASHI/Mathematics/Topology/HatcherRibbonPeripheralBoundaryExact.agda`
has by-reflexivity the positive one-cycle and
negative three-cycle source successor tables,
without duplicating #1254's real PL mesh.
No Agda kernel run. All mathematical
source/original and implementation
attribution remains unchanged.
