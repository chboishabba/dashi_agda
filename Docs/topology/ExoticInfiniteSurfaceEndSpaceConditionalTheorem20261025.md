# Conditional end-space realisation theorem for the three PL towers

**Dated working theorem, 2026-10-25 — mathematical proof architecture, NOT an
Agda/Lean kernel certificate.** Source roots: H. R. Brahana (1921), compact
bordered classification; B. Kerékjártó (1923), ideal ends predecessor;
Ian Richards, *On the Classification of Noncompact Surfaces* (1963),
Transactions AMS 106, 259–269, DOI 10.2307/1993768. Richards is the
source for Definition 1/2 of ideal boundary and his theorem realising
decorated end spaces. Authorship and proof responsibility remain distinct.

## Precise topological hypotheses

Let `K_0 -> K_1 -> ...` be an increasing sequence of **finite**
connected orientable triangulated compact PL 2-manifolds with nonempty
polygonal boundary, with specified PL collar embeddings at every
attachment such that:

(H1) every old `K_n` is identified with a **closed** embedded
subsurface of `K_(n+1)`, with `K_n ⊂ int(K_(n+1))`;
the map restricts injectively on old points, not just vertices;

(H2) each boundary component in the **full old** outgoing frontier
receives exactly one collar/cobordism; all fresh outgoing boundaries
are explicitly labelled, and there are no extra attachments or
unaccounted complementary components;

(H3) the collar inclusion of each old frontier circle and its
new glued component is topologically compatible with the *disjoint*
triangulated pieces, and no unexpected intersections are introduced;

(H4) the final/direct-limit topology on
`S := union_n K_n` agrees with the locally inherited PL topology
on these collared pieces; in particular every point has a connected
2-disk neighbourhood inside some `int(K_m)`;

(H5) outgoing infinite subtrees at each stage are unbounded connected
regions with compact boundaries, and no proper end travels through
anything except an outgoing old-frontier component.

The new `exotic_topology_pl_surface_gluings.py` checks finite
triangulations, vertex links and face orientations. The new
`exotic_topology_pl_frontier_lineage.py` transports each **actual
boundary-vertex set** across the finite gluing and checks exact
parent/child incidence (H2 at tested stages). The optional transport
also checks that neither input's distinct vertices are merged within
that input. This is strong finite evidence for H1/H3 but does NOT by
itself prove the **point-set embedding** and infinite compatibility
clauses H1/H3/H4/H5. None of those unsupplied geometric obligations
is disguised as a Boolean `verified` theorem.

## Conditional theorem

Assume H1–H5 uniformly over all natural numbers, and give every
cobordism the exact surface type below.

**Cantor tree.** `K_0` is a disk. Every outgoing boundary circle
gets a genus-zero three-boundary pair of pants at the next stage;
the two fresh circles are labelled `p0`, `p1`.

**Loch Ness monster.** `K_0` is a disk. Its unique outgoing
circle receives a genus-one two-boundary collar at every stage.

**Jacob's ladder.** `K_0` is an annulus. Its two outgoing
circles L/R EACH receive a genus-one two-boundary collar at
every stage.

Then under these hypotheses:

(T1) Each `S` is a connected orientable boundaryless
Hausdorff second-countable noncompact topological 2-manifold.

(T2) The Richards ideal boundary for the Cantor tree is homeomorphic
to the binary product Cantor space `{0,1}^N`, and every end is
planar. The ideal boundary of Loch Ness is a singleton and that
end is nonplanar. The ideal boundary of Jacob's ladder is two
discrete points and both ends are nonplanar.

(T3) Their genus is respectively zero, infinite, infinite; hence,
by Richards' classification and its original source hypotheses,
the resulting surfaces have the respective canonical topological
types.

## Proof dependencies and justification

1. **Finite geometry and Euler:** A disk is (g,b)=(0,1);
a pair of pants (0,3); a genus-one cobordism (1,2);
an annulus (0,2). Orientability is preserved because
gluing identifies the induced boundary orientations
oppositely. `chi(A union_S1 B)=chi(A)+chi(B)` since
`chi(S1)=0`. The existing finite PL audit computes
the full `V-E+F`, checks all vertex links and the oriented
edge incidences rather than merely quoting this identity.
The user-specified labels supply the exact child incidence.

2. **Manifold topology:** Every point of S belongs to the
interior of some later K_m by H1. A PL triangle-interior,
edge or vertex-link chart there supplies a disk
neighbourhood, and the collars in H4 make it a chart in
the final topology. Two distinct points lie in a common
K_m and admit disjoint metric open neighbourhoods whose
collared continuations remain disjoint by H3/H4.
A countable union of finite triangulation chart bases
gives second-countability. S is connected because the
K_m are nested, nonempty and connected. Boundarylessness
follows because each old boundary is eventually collared.

3. **Proper compact exhaustion:** The sets `int_S(K_n)`
form an increasing open cover of S. Every compact subset
Q is contained in finitely many of those interiors by
compactness, hence in some K_N. Each K_N is compact and
proper in S since it has an unbounded outgoing tail.
This is the cofinality bridge needed in Richards'
Definition 1: no end can avoid the finite-stage tail
decomposition yet remain proper.

4. **Cantor ideal-boundary bijection:** H2/H5 identify
the unbounded connected components of `S\K_n`
with length-n binary prefix codes. Their nesting
maps are precisely `p b -> p`. Every infinite binary
stream selects a compatible nested tail sequence
with compact boundary. Conversely any Richards end
has, by compact cofinality, a unique outgoing tail
at each level. Richards equivalence of nested region
sequences identifies exactly equal eventual selections;
distinct binary streams differ at a finite level and
thus determine inequivalent ends.

5. **Topology of the ideal boundary:** For a length-n
prefix p, the end-set of the corresponding outgoing
region is a basic open `U_p^*` under Richards'
Definition 2, and its complement is a finite union of
other level-n cylinders. Thus these are clopen.
Since compact cofinality makes every Richards
basic neighbourhood contain a deep enough prefix
neighbourhood, the cylinders form a basis.
The identification is a homeomorphism to the ordinary
Cantor product topology (not an identification of
uniform Bernoulli measures). The literal tower-to-stream
equivalence is source-written in the separate Lean
`ExoticTopologyCantorInverseLimit.lean`; translating
it to the Richards topology is STILL a separate
kernel-geometric statement.

6. **Finite discrete ideal boundaries:** At every
Loch level only one unbounded complementary component
exists; at every Jacob level exactly two labelled
unbounded tails remain, with no later bridge between
them. They give respectively one and two ideal ends.
In Jacob, the two tail-end sets are clopen/discrete.

7. **End genus:** Every Cantor subtree is made entirely
from genus-zero oriented pants, so each connected tail
is planar. In Loch and both Jacob tails there is a
genus-one handle beyond every finite compact K_N.
The handle cannot be confined to a compact source
neighbourhood; hence no end-tail is eventually planar.
Every end in the latter two spaces lies in Richards'
closed nonplanar-end subset.

8. **Classification:** With connectedness, orientability,
global genus and decorated ideal-boundary
homeomorphisms paid, Richards' theorem identifies
each S up to homeomorphism with the named canonical
noncompact surface. The theorem does not follow
solely from `chi`, `g` and `b` stage counts.

## Formal acceptance boundary / next kernel lemmas

The finite pieces above are already represented in Python, the finite
prefix/tower equivalence is newly source-written in Lean, and the
source/provenance ledger in Agda preserves Brahana/Kerékjártó/Richards.
To promote T1–T3 from a conventional paper argument to a **verified
DASHI theorem**, a Lean owner still must supply:
- genuine PL collar/glue topological embeddings and compatible
  direct-limit topology, not just injective vertex maps;
- compact exhaustion and unbounded-tail decomposition over the
  constructed *same* topological space;
- the homeomorphism from those Freudenthal/Richards ends to the
  existing `CompatibleCantorTower`;
- the planar/nonplanar end characterisations and a kernel-recognised
  classification theorem on that carrier;
- exact version-pinned imports/typechecks, not Python execution.

No assertion is made that these conditional hypotheses have already
been discharged, that Richards' classification is currently in
Mathlib, or that kernel typechecks were run.


## 26 October: actual finite complementary-component weld

A stronger geometry-specific prerequisite is now implemented, not just
suggested. Original existing triangulation and labelled collar owners
are IMPORTED by
`scripts/exotic_topology_pl_complement_components.py`:

1. Use `attach(..., with_transport=True)` to track the simplexwise
   injection of EVERY old-stage vertex across the sequence of finite
   collar attachments. The exact map is composed across all old
   frontier components, not reconstructed by matching labels later.
2. Verify that all old **triangles** occur as distinct, embedded
   triangles in the next finite PL manifold.
3. Form the set of added triangles by literal difference of simplex
   sets. Partition it into full-edge-connected dual components.
4. Compare the set of edges where a new triangle meets an old
   triangle to the **entire actual old boundary**, including every
   edge of every boundary circle. Each such interface edge must
   have exactly one newly attached triangle.
5. Verify a bijection between old boundary components and new
   complementary dual components. No two old outgoing boundaries
   can share one component, and no old boundary may remain
   unattached.
6. Check that **every** fresh outgoing boundary edge belongs to
   the expected component: `p -> p0,p1` for Cantor,
   one continuing tail for Loch Ness, and separate L/R continuations
   for Jacob's ladder.

These are genuine finite same-**triangulation** incidence tests;
they supersede relying on abstract finite boundary-word counts.
Existing `MarkedSurface.verify` and `inspect` still independently
test the triangle-level orientable-manifold property. Three
new complement-focused tests cover depths 1--3, a collapsed
old-vertex inclusion, and an otherwise legal two-boundary
surface with false lineage labels.

**Proof-status discipline:** these new tests are committed but
still require actual execution on the exact pushed source.
Even all their passing conditions would only establish the
finite-stage *combinatorial* analogue of hypothesis H5.
A locally finite collared infinite PL colimit is NOT constructed
by this script; properness/compact cofinality, openness and
connectedness of the actual infinite tail regions, and topology
of Richards' ideal boundary remain independent hypotheses.
A purely finite simplex-component count does not prove their
infinite analogue or classify actual 2-manifolds.

**Latest PR reuse, 26 October:** independent observer #1266
has a separate consumer-factorisation treatment. This
document does not import it across an unmerged branch;
#1254 already imports canonical
`QueryIndexedProjectionAdequacyExact` and
`IntersectionalNonFactorability` for the relevant information
loss. Independent source-evidence revisions in #1268
suggest a better provenance ledger, but are not evidence
about the geometry of any exotic surface.


## 26 October orientation-sensitive event-basis correction

The mathematical proof above uses *chronological* depth-n prefixes
`p=(s_0,...,s_(n-1))` and cylinder refinement
`p -> p0,p1`. We now know explicitly that this convention
is NOT the unqualified `Cantor.leftChild` implementation
of the earlier DASHI premeasure: its `leftChild` **prepends**
a bit instead. Because its mass is only a function of word
length, the parent-mass-splitting lemma is still correct,
but is insufficient to prove the underlying EVENT inclusion.

The new `ExoticCantorCylinderOrientationExact.agda`
provides chronological `MatchesAt`, correctly appended
children and exact *all-prefix* event-refinement theorems,
with an explicit two-digit counterexample to the old
non-refining interpretation. Combined with the new
finite PL complementary-component verifier, this
ensures the FINITE part of steps 4--5 in the conditional
argument uses one consistent old-to-new frontier
order and one literal cylinder event basis.

Step 5 is still conditional on actual compact cofinality
and the open end-neighbourhood basis in the constructed
infinite surface. In particular, finite word reversal
conjugates the two finite address-tree conventions,
but one must not casually assert an **infinite sequence**
has a terminal-bit reverse or that dyadic finite mass
is a Borel probability measure before its extension.


## 26 October — balanced ternary realisation is a new *presentation*, not a fourth surface type

**Actual finite geometric payment:** In
`scripts/exotic_topology_balanced_ternary_pl.py` an ordinary
pair of pants has THREE total boundary circles and supports
one incoming/two outgoing. A balanced 1→3 branch has FOUR
total boundary circles and is realised by TWO sequential
source-owned pants. The intermediate circle is sewn shut
and is never a new end. The temporary first split's
continuation is not a representation of the balanced
`zero` branch: that branch is one of the THREE final
outgoing circles. This preserves the signed-zero fibre.

Through finite depth three, independent actually executed
PL geometry gave genuine orientable genus-zero triangulations
with 1,3,9,27 boundary circles and exact connected
new complementary components 1,3,9. The *same*
old-simplex/dual-component checks from binary case were reused,
only its child-label alphabet was extended. No forked
PL component theorem or new topological-space type.

**Conditional end identification:** Assume analogues H1–H5
for this all-n 3-ary collared tower. Then its nested proper
tail components are indexed by infinite balanced streams
`{-1,0,+1}^ℕ` with the product/cylinder topology.
It is a Cantor space (perfect, nonempty, totally disconnected,
compact metric); the genus is zero and each end planar.
Richards' theorem therefore classifies this as **the same
topological Cantor-tree surface type** as the binary pants
exhaustion, not a fourth exotic-surface homeomorphism type.

**Explicit end-space homeomorphism:** the EXISTING original
prefix-free code `3→0, 6→10, 9→11`, with chosen balanced
labels `neg→3, zero→6, pos→9`, concatenates each infinite
balanced stream into an infinite binary stream. Every
infinite binary stream is uniquely parsed by reading
one bit if it is 0 and a second bit if it is 1.
Continuity of the encoding: first n balanced symbols
fix at least n binary output bits. Continuity of
decoding: first 2n binary input bits determine at least
n complete balanced symbols. Thus both maps are
uniformly continuous for standard prefix metrics,
hence homeomorphisms. This is a conventional mathematical
argument, NOT an Agda/Lean kernel-verified infinite-stream
equivalence in the current repo. The EXISTING finite
Agda codec/roundtrip and balance-to-SSP369/pants
naturality proofs are the producer inputs.

**Non-equivalences:** this code is not level-preserving
because digit words have variable binary length.
Haar/fair binary measure gives signed weights
`(1/2,1/4,1/4)`, not uniform ternary `(1/3,1/3,1/3)`;
in fact no measure-preserving HOMEOMORPHISM of these
specified product measures exists because dyadic clopen
masses cannot equal 1/3. Nor does this homeomorphism
conjugate the natural 2-adic and 3-adic compact
TOPOLOGICAL-GROUP structures. And neither balanced
sign inversion (`neg↔pos,zero↦zero`) nor the
`C3` rotation of the 369 slots is the ordinary
boundary-orientation reversing map used when gluing
the finite PL pants.

**Still missing for kernel promotion:** a point-set
locally finite infinite PL colimit, its actual
topological Freudenthal/Richards compact-end
neighbourhood basis, same-object homeomorphism to
the balanced prefix streams and the formal Richards
classification. The finite 27-frontier fixture does
not discharge these infinite theorems.
