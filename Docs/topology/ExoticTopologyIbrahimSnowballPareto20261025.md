# Exotic topology: Ibrahim first-link / snowball / Pareto max-cut — 2026-10-25

Companion work: [Agda #1254](https://github.com/chboishabba/dashi_agda/pull/1254) stacked on horned-sphere [#1244](https://github.com/chboishabba/dashi_agda/pull/1244);
native Lean [#86](https://github.com/chboishabba/dashi_lean4/pull/86).
This document is a source-genealogy and exact-residual ledger, not a claim
that twenty difficult geometric classifications were formalised.

## Method (reuse existing source provenance owners)

- **Ibrahim first-link**: begin at the original named mathematical object
  or consumer proof obligation; traverse the shortest documented
  predecessor/implementation links. A link is a retrieval route, not evidence
  of theorem correctness. Neither approximate match nor "same terminology"
  is a proof edge.
- **Snowball**: original article -> explicitly cited predecessor ->
  verified implementation donor -> actual same-object construction ->
  independent contrary/negative discriminator. Keep authors, publication
  context, DOI, venue, exact version and unresolved identifiers.
- **Pareto**: order actions by dependency fan-out, concrete reduction of the
  current residual, cost and incompatibilities. Rankings do not transfer
  citation authority, rewrite original authorship or imply proof completion.
- **Typed owner**:
  `DASHI/Core/AttributedSourceCore.agda` +
  `SnowballAttributionProvenanceInvariantExact.agda`. New
  `ExoticSourceGenealogyParetoExact.agda` imports both and uses their
  source records and nonpromoting receipt. There is no competing source
  ontology. Uninspected QID and Dewey numbers explicitly remain unresolved.

## Source roots and actual genealogy

| Source | Original status / dates | Stable identifier | Consumer and graph-edge meaning |
| --- | --- | --- | --- |
| H. R. Brahana, *Systems of Circuits on Two-Dimensional Manifolds* | Ann. Math. 23 (1921), 144–168 | DOI [10.2307/1968030](https://doi.org/10.2307/1968030) | Richards **explicitly credits** the compact bordered-surface Euler/boundary/orientability classification to Brahana; source for our finite PL checks |
| B. Kerékjártó, *Vorlesungen über Topologie, I: Flächentopologie* | **1923 printed work**, 2013 electronic edition | eBook DOI [10.1007/978-3-642-50825-7](https://doi.org/10.1007/978-3-642-50825-7) | Richards credits earlier ideal-boundary approach, notes gaps, provides later argument. The DOI belongs to the reissue, not the original print object |
| Ian Richards, *On the Classification of Noncompact Surfaces* | Trans. AMS 106 (1963), 259–269 | DOI [10.2307/1993768](https://doi.org/10.2307/1993768) | Original 1963 proof/completion and realisation of decorated end spaces; not a finite mesh theorem. [Primary PDF](https://people.dm.unipi.it/benedett/Richards.pdf) |
| Ralph H. Fox and Emil Artin, *Some Wild Cells and Spheres in Three-Dimensional Space* | Ann. Math. 49 (1948), 979–990 | DOI [10.2307/1969408](https://doi.org/10.2307/1969408) | Exact source-selected wild arcs. Paper **explicitly notes cases where global complement fundamental group cannot detect wildness**. [Primary PDF](https://www.maths.gla.ac.uk/~mpowell/fox-artin.pdf) |
| Kunizô Yoneyama, *Theory of Continuous Set of Points (not finished)* | Tohoku Math. J. 12 (1917), 43–158 | [J-STAGE original](https://www.jstage.jst.go.jp/article/tmj1911/12/0/12_0_43/_article) | Historical publication carrying Wada's common-boundary lakes example. Publisher records 1918 continuation in vol. 13. No DOI claimed |
| Sibe Mardešić, *Shape Theory* | ICM Helsinki (1978), survey | [Scanned survey](https://citeseerx.ist.psu.edu/document?doi=1689fd7674a0d927b89aad5f68c1cfa6456d01d4&repid=rep1&type=pdf) | Historical survey explaining Warsaw-circle weak homotopy vs noncontractibility; **not** falsely attributed as originator of Borsuk's shape theory |
| E. Bombieri, E. De Giorgi, E. Giusti, *Minimal Cones and the Bernstein Problem* | Invent. Math. 7 (1969), 243–268 | DOI [10.1007/BF01404309](https://doi.org/10.1007/BF01404309) | The GMT area-minimisation result; the algebraic cone/gradient/link checks do not import its proof |
| Allen Hatcher, *Algebraic Topology* | Textbook (2002) | [Author PDF](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf) | Source of CW, van Kampen and sphere background; source text does not supply a Lean theorem |
| Jack McCarthy, `Hatcher/Sphere/Homology.lean` | Hatcher-at implementation, inspected 2026-10-25 | [Original Lean module](https://github.com/Deicyde/hatcher-at/blob/main/Hatcher/Sphere/Homology.lean) | Genuine reduced sphere homology on literal `TopCat.sphere`, but external Lean/Mathlib v4.34.1 source not directly importable into DASHI's pinned Mathlib v4.28.0 without a compatible exact-graph build |

Cross-links **known from original text**, not invented: Richards -> Brahana;
Richards -> Kerékjártó; Fox–Artin -> Alexander/Antoine historical context;
current Hatcher-at -> Hatcher and Mathlib. Other juxtaposed sources above
are investigative cousins, **not** mutually citing papers or evidence of
mathematical equivalence.

## Largest concrete geometric payment this round

New source:
`scripts/exotic_topology_pl_surface_gluings.py`.

It constructs **actual finite oriented simplicial complexes**:
- an oriented subdivided-cube sphere with two holes (annulus) or three
  separated holes (pair of pants);
- a periodic 6×6 triangulated torus with two separated triangular holes
  (one-handle, two-boundary collar);
- a triangulated disk;
- gluing through full matched boundary cycles by **orientation reversal**,
  using a disjoint-set quotient of vertices and recomputed faces.

It verifies at every constructed stage:
1. all triangles have distinct vertices and every edge has one or two
   incident faces;
2. every interior shared edge has opposite induced orientations;
3. triangle adjacency is connected via the one-skeleton;
4. **every vertex link** is connected and has degree 2 (interior circle)
   or exactly two degree-1 endpoints (boundary interval);
5. each boundary edge belongs to precisely one oriented boundary loop;
6. `chi=V−E+F=2−2g−b` for an integer nonnegative genus.

Distinctive new result: up to stage **4**, not merely numerical profile
consistency, the actual finite PL manifold tests pass:

| Family | Stages 0–4 genus | Stages 0–4 boundary circles |
| --- | --- | --- |
| Cantor-tree | 0,0,0,0,0 | 1,2,4,8,16 |
| Loch Ness monster | 0,1,2,3,4 | 1,1,1,1,1 |
| Jacob's ladder | 0,2,4,6,8 | 2,2,2,2,2 |

Independent local Python implementation passed these finite manifold
tests, plus a **negative control**: two triangles with the same induced
shared-edge orientation are correctly rejected. The new GitHub file
and two regression tests are committed. This is NOT Agda or Lean
kernel certification; the pushed script still requires exact-head
execution to be called a passing GitHub receipt.

## What the finite PL result *does* and *does not* settle

Each finite mesh is a triangulated connected orientable compact surface
with boundary (using the standard PL link criterion), so we have now
provided substantially more than `g,b,chi` numerology.

To construct the ACTUAL infinite surfaces, still prove all of:
- compatible choice of PL collars along each outgoing boundary circle,
  ensuring old frontier circles become interior in the next stage;
- existence, Hausdorffness, second-countability, connectedness,
  orientability and boundarylessness of the resulting direct-limit
  topological 2-manifold;
- that each tail component of the complements of compact exhaustion
  stages agrees exactly with the corresponding nested binary prefix
  for Cantor, the unique Loch Ness tail, and the two Jacob tails;
- the decorated end space equals Cantor with no nonplanar ends, a
  singleton accumulated by genus, and a two-point discrete space with
  both ends accumulated by genus, respectively;
- THEN apply a correctly formalised version of Richards, retaining
  Brahana/Kerékjártó attribution to the older component theorems.

The bare assertion that Euler/genus data agree cannot replace any of
these global topology obligations.

## Recursive Pareto frontier after constructive payment

| Rank | Supplier/root | Current accepted state | Remaining exact object |
| --- | --- | --- | --- |
| 1 | McCarthy/Hatcher + native CP¹/S² | Actual homeomorphism & categorical transport already owned; external reduced sphere H₂ found | One mathlib-revision-matched reduced/ordinary rational H₂ object and kernel receipt |
| 2 | Brahana -> Kerékjártó -> Richards | **Finite PL stages actual geometry verified locally** | Collared direct-limit surface and homeomorphic decorated end spaces |
| 3 | Fox–Artin + horned #1244 | Horn address/linking finite source machinery | Literal source-selected Fox–Artin nested embedding and non-1-LCC/local wildness witness |
| 4 | Borsuk/Mardešić | Literal Warsaw sine-closure subset in Lean #86 | Vertical closure, local topology, all homotopy groups and noncontractibility/shape distinction |
| 5 | Wada/Yoneyama | Literal Wada frontier predicate and C3 non-go | Real three planar connected disjoint domains with the same frontier |
| 6 | Bombieri/De Giorgi/Giusti | Literal Simons cone/link and gradient algebra | Geometric-measure area-minimality and calibrated/varifold theorem |

The ranking measures tractable dependency fan-out, not importance,
citation volume, historical priority, or confidence. Follow the first
remaining exact primary object at each leaf; stop literature snowballing
when further derivatives add no independent theorem, construction,
negative control or compatible proof source.

## Validation boundary

- Local SymPy and finite PL calculations have been executed;
  the latter includes 15 tested surface stages plus four independent
  starter pieces and an orientation-rejection negative control.
- GitHub source files were written/read by connector; the new
  Agda/Lean modules remain UNTYPECHECKED, as does the canonical PL
  script at the exact pushed SHA.
- No entire twenty-object theorem bundle is promoted complete.
- DOI is source identity, QID/DDC may be unknown, citation is not a
  mathematical proof, and Pareto rank is not a proof-status certificate.


## Fox–Artin original example disambiguation — decisive negative control

Read the 1948 primary paper directly, not secondary summaries or figure labels.

- **Example 1.1\***, pp. 982–983: the arc pictured in the original
  user's prompt. Fox–Artin explicitly says its complement is
  **NOT simply connected**. Its source-specific iterated *chain
  stitch* and nontrivial group relations are the proper positive
  construction target; do not misattribute the simply-connected
  contrast to this exact diagram.
- **Example 1.2**, pp. 983–985: a **wild** arc whose complement **IS
  an open 3-cell**. Consequently the entire ambient complement's
  homeomorphism type, not just its global fundamental group, is
  insufficient to decide tameness. The paper instead uses a
  **local inverse system of punctured neighborhoods at the endpoint**.
- **Example 1.3**, pp. 985–987: the complement is simply connected,
  yet is **NOT an open 3-cell**. The proof uses an additional
  disjoint closed curve and a nontrivial fundamental group of its
  complement with the arc; global `pi1(S3 - arc)` alone again fails.

This gives a **three-way source-derived acceptance discriminator**,
rather than one generic "wild arc" Boolean:
`nontrivial global pi1` / `global complement is an open cell but local
wildness remains` / `global pi1 trivial yet complement not an open cell`.

The existing horned-complement finite group pipeline may address the
first case, but **cannot by itself** settle the other two. Next
source-specific proof must formalise the actual nested local
complement inclusions and tameness test from Example 1.2,
then its Example 1.3 witness. Do not call the subject of Figure 6
an Example 1.3 simply-connected arc.

Primary source: Fox and Artin, Annals of Mathematics 49 (1948),
979–990, DOI 10.2307/1969408;
https://www.maths.gla.ac.uk/~mpowell/fox-artin.pdf


### Positive finite group payment for Figure 6 / Example 1.1*

The companion native Lean
`Synthesis/ExoticTopologyFoxArtinS5Witness.lean`
and independent script
`scripts/exotic_topology_fox_artin_s5.py`
in **dashi_lean4 PR #86** reconstruct Fox--Artin's exact page-983
equation (2_n*) and its three-periodic 5-cycle representations.
The independently executed Python solver checks all three
residue classes (and 603 consecutive integer indices including
negative n); every relation holds, and each source cycle is
nontrivial of order 5.

Accepted status: **actual finite S5-valued model of the source
group presentation**, plus source-written Lean `by decide`
statements. This strictly improves the prior-art audit for the
user's specific figure. It is not yet a homomorphism out of the
ACTUAL topological complement `pi1` without the geometric
colimit/VK theorem. Nor does it decide the local endpoint
wildness of source Examples 1.2 and 1.3.


## 2026-10-25 lineage correction: finite manifold != Cantor end construction

A subtle implementation defect in the earlier `exotic_topology_pl_surface_gluings.py`
was uncovered: its Cantor scheduler iterated
`range(len(boundary_loops(mesh)[0]))` but repeatedly called
`glue(mesh, pants)` on **boundary index zero**. After the first
attachment that index can denote a NEWBORN frontier circle.
Therefore its passed genus/Euler/vertex-link and `2^n` boundary
count fixtures did **not** certify that every PREVIOUS stage
branch had split exactly once. The old `audit` is retained as
a mesh-integrity audit, but its end-lineage inference is superseded.

Repairs committed:
- `exotic_topology_pl_surface_gluings.py:glue(...,with_transport=True)`
  now optionally returns **actual vertex maps** from both input
  triangulations through the orientation-reversing quotient.
  Original callers and mathematical triangulation are unchanged.
- `exotic_topology_pl_frontier_lineage.py` reuses the original
  disk, three-holed sphere/pants, punctured torus/handle, gluing,
  link validator and boundary-cycle detector. It labels every
  live geometric boundary circle and transports all labels through
  vertex identifications; at a new stage it snapshots the full old
  frontier, attaches to each old label **once only**, and compares
  resulting labels against the exact binary child set.
  Cantor: prefix `p -> p0,p1`; Loch: sole label persists after
  one handle; Jacob: each of L/R persists after its own handle.
  Every live label must match exactly one actual geometric boundary
  loop, not merely an address in a separate registry.
- Three additional unit tests check exact labelled stages, a
  count-only false-positive, and an **actual legal oriented
  4-boundary triangulated surface** obtained by repeatedly
  splitting the same left branch while leaving the right one
  unsplit. Thus topology stage integrity, Euler/genus and b=4
  do not imply correct Cantor-tree ancestry.
- `dashi_lean4` #86 adds
  `Synthesis/ExoticTopologyCantorInverseLimit.lean`, sourcing
  finite stage functions from **existing** `Integration.Address.Addr`.
  It defines coherent infinite towers and a two-sided stream/tower
  equivalence. This is not yet kernel-checked or a claim about the
  Freudenthal/Richards end topology of the literal 2-manifold.

**Important outstanding bridge:** the infinite collared union and
its actual space of proper nested unbounded-region classes must be
identified with this coherent prefix space, including continuity
in the Richards ideal-boundary topology. The 1963 paper defines
ends by nested connected unbounded regions with compact frontier
and the properness condition, not simply by arbitrarily labelled
triangular boundary circles (Richards pp.261--262).
The PL lineage repair supplies the correct **finite incidence
input** for this global theorem and no more.

Fresh execution at the exact pushed SHA: NOT YET AVAILABLE.
The tests and construction are source-written and committed;
the earlier 8/8 + mesh receipts predate the lineage repair and
must not be cited as having executed these new tests.


## 2026-10-25 newest-PR snowball and stronger clopen discriminator

### Relevant latest branch owners, not a bibliography popularity poll

| Donor PR / original root | Reuse paid | What is *not* promoted |
| --- | --- | --- |
| [#1244](https://github.com/chboishabba/dashi_agda/pull/1244), Alexander (1924), Hatcher Example 2B.2 | Existing `ThreeArmCollarCoverAssembly.lean` derives path-connected cover and van Kampen free-product consumer from source-specific **central region / satellite** hypotheses; `AlexanderHornedBinaryTernaryExistingCodecWeldExact` already uses two older DASHI digit codecs and mixed 2/3 resolution | Horn symbolic addresses or one typed conditional collar contract do NOT identify the actual Fox--Artin arc complement; no geometric wildness or unproven smooth equivariant embedding |
| [#1239](https://github.com/chboishabba/dashi_agda/pull/1239), Artin (1925, 1947) | Actual existing finite modular `B3→SL2(Z)` calculations and punctured T9 shadow, plus separate `C3BraidFramingInformationLossExact` | (S_3) endpoints, (SL_2(ℤ)) monodromy, (B_3) isotopy and ribbon framing are *four different objects*; their kernels are not interchangeable |
| [#1259](https://github.com/chboishabba/dashi_agda/pull/1259), canonical `QueryIndexedProjectionAdequacyExact` | Existing `IntersectionalNonFactorability` and query-dependent adequacy let the horn-address no-go reuse the *general proof* of nonfactorability and survival under all downstream recharts | Blackwell (1953) and Crenshaw (1991) are conceptual precedents; they did not prove any mathematical Fox--Artin embedding/wildness fact. PR #1259 is an application, not source root |
| [Lean #86](https://github.com/chboishabba/dashi_lean4/pull/86) | Actual `CantorStage = Integration.Address.Addr n Bool`, coherent tower–stream equivalence source-written; new `ExoticTopologyCantorClopenMeasureNoGo.lean` isolates the universal all-depth divisibility obstruction | Neither finite state equivalence nor the divisibility theorem is the actual Freudenthal end-space homeomorphism or a kernel-certified measure-space classification |

### The braid counterexample with three successive forgetful quotients

The exact original (B_3) generators (sigma_1,sigma_2) have endpoint
projection to the adjacent transpositions in (S_3). PR #1239 already
records the modular representation
(ho(sigma_1)=\begin{pmatrix}1&1\\0&1\end{pmatrix}),
(ho(sigma_2)=\begin{pmatrix}1&0\\-1&1\end{pmatrix}).
For (z=(sigma_1sigma_2)^3), its *endpoint permutation* is the
identity, but (ho(z)=-I), and its braid exponent sum is (6).
For (z^2), both endpoint and modular images are identities while
the exponent sum is (12\ne0). This exhibits nonfaithfulness of
both projections, with no unproved knot isotopy assertion.
The PR #1239 sample word ((sigma_1^{-1}sigma_2)^3) has exponent
sum zero but modular image
(egin{pmatrix}13&-8\\-8&5\end{pmatrix}) of trace 18,
so the exponent-sum invariant alone is not complete either.

A new source-scoped Python consumer
`scripts/exotic_topology_braid_crosspr_discriminator.py`
was committed with a regression test. An independent local SymPy
replication passed the braid relation, central image, strand
projection and sample matrix/trace; exact pushed-SHA Python workflow
execution is NOT claimed.

**Historical attribution:** the original braid source is Artin,
*Theorie der Zöpfe* (1925), DOI
[10.1007/BF02950718](https://doi.org/10.1007/BF02950718).
Artin's *Theory of Braids* (1947), DOI
[10.2307/1969218](https://doi.org/10.2307/1969218), explicitly
acknowledges his 1925 work and strengthens the rigorous
braid-coordinate approach. PR #1239 is a later repository
*implementation/selected computational donor*, not original
authorship. `ExoticSourceGenealogyParetoExact.agda` now
records BOTH sources and a seventh braid/Seifert consumer leaf;
the source atlas holds eleven independent cited items, without
fabricated QIDs or library classification numbers.

### New stronger topological measure theorem (mathematical, not kernel claim)

The pre-existing variable-length prefix code `3→0,6→10,9→11`
already gave one binary/ternary Cantor homeomorphism with nonmatching
Bernoulli weights. The new source `scripts/exotic_topology_cantor_measure_obstruction.py`
upgrades the mathematical result: **NO** measure-preserving
homeomorphism exists between the *fair binary* and *uniform ternary*
Cantor product measures.

The first ternary-digit cylinder is clopen of measure (1/3).
The pullback of this cylinder by a homeomorphism must be clopen
in binary Cantor space. A clopen subset of the compact product
space is a finite union of prefix cylinders, refinable to a
single depth (n), and therefore has fair-bit measure (k/2^n).
If the homeomorphism were measure-preserving,
(3k=2^n). But (3\nmid 2^n) for every (nge0).
Contradiction. This does **not** preclude a non-measure-preserving
homeomorphism, as our codec provides.

Independent local exact rational regression over all binary levels
0–12 passed; Lean #86 now source-writes the universal
prime-divisibility theorem `noDyadicClopenMassEqualsOneThird`
using Mathlib's existing `Nat.Prime.dvd_of_dvd_pow`.
Neither Lean source has a fresh kernel receipt. This claim is
about these **specified measures** and these **product topologies**,
not about arbitrary full-support measures on homeomorphic Cantor spaces.

### Claim-relative projection adequacy, not intrinsic adequacy

`ExoticAmbientLinkingNoGoExact.agda` now imports the EXISTING
`QueryIndexedProjectionAdequacyExact` and
`IntersectionalNonFactorability` owners. It supplies:
- a question about the C3 sector, which *does* factor through the
  symbolic horn address;
- a question about a separately marked linking bit, whose two
  states have the *same* symbolic horn address and different answers;
- a canonical query defect and general factorisation prohibition;
- the **all-postrechart obstruction**: any function of only the
  old symbolic address remains inadequate for the linked-bit query.

This is a reusable exact non-descent proof about marked information,
NOT a pair of realised tame/wild embeddings and NOT proof of linking
in Euclidean three-space.

### Updated operational frontier

P0: exact-head Python workflow results and Agda/Lean typecheck
receipts. The new focused workflow
`.github/workflows/exotic-topology-focused.yml` follows the
parent's narrow-test pattern; installation and collection of actual
run output are separate from adding a YAML file.

P1: locally finite PL surface colimit and actual Freudenthal/Richards
end homeomorphism (including the corrected parent-child lineage).
P2: actual Fox--Artin embedded arc, local fundamental group tower,
and same-object van Kampen certificate using #1244's existing
three-arm assembly.
P3: compatible external sphere (H_2) from Hatcher/McCarthy.
P4: Warsaw, Wada, and geometric Seifert/braid construction.
The newest whale, media-source and monster PRs supply no proven
new same-object geometric data for these P0–P4 topology consumers.
Do not add them merely to make the bibliography large.


## Second restack: parent horned exact-cover result changes the true topology Pareto cut

Rebased by NONDESTRUCTIVE MERGE (not a force push) onto inspected
horned parent #1244 head `34c7ae2741c7849530c4cffba4daa0444f02d9c0`
in merge commit `f1b1c097767bf085535e48795e49b5e515792c0e`.
At that snapshot the child was 53 commits ahead, zero behind,
and all 21 child paths were disjoint from the parent's 5 new
geometry/collar paths. This source is a merge receipt, NOT a
successful exact-head kernel or CI run. Future parent commits may
again advance the base.

NEW source-owned geometric donors now accessible on this branch:

- `proofs/horned_c3_lean/HornedC3/ThreeArmCentralPi1Reduction.lean`.
  Using already-existing `ThreeArmCollarCoverAssembly` and based
  `OverlapGroup`, the source-written theorem reduces all off-diagonal
  overlap fundamental groups to **ONE** trivial-central-`pi1` input.
  It does not construct an actual wild solid nor discharge that input.
- `scripts/alexander_horned_c3_explicit_open_cover.py` records
  rational centres `9e_i`, cut radii `15/4<17/4` and exact
  separation margins, yielding actual relatively open C,S_i,U_i
  in a *supplied* chosen exterior E. Open-cover disjointness and
  coverage follow mathematically from those inequalities.
- `scripts/alexander_horned_c3_pierced_shell_product.py` already
  implements the stereographic annular shell coordinate identities
  for a source-selected straight pierced tube. It has an
  **867-point** rational finite acceptance audit; it does NOT
  certify the entire geometric wild exterior or a based `pi1`
  isomorphism.
- `Docs/topology/AlexanderHornedC3ExplicitExteriorOpenCover20261025.md`
  gives the PAPER-LEVEL argument: the common central exterior
  is the complement of a tame 3-ball *IF* the wild satellites are
  contained in the original selected unit reference balls and
  the outside spoke geometry satisfies those exact envelopes.
  It explicitly does not claim C is contractible in R3:
  its H2 can be nonzero while pi1(C) is trivial.

The child now has two tests **importing these exact parent scripts**;
it no longer duplicates the 867-point stereographic fixture or
silently treats a radius inequality as a direct wild-embedding proof.

**Revised P2 for Alexander:** the explicit three-arm OPEN COVER
is no longer the blocker at the paper-geometric level. The
surviving same-object obligations are an actual Lean realisation
of the open-set/central `pi1` argument on E, the satellite
homotopy equivalences to the selected Hatcher G_A,
the induced based maps, and compatible infinite limit.

**Revised P2 for Fox–Artin remains SEPARATE:** the selected arc
in Figure 6 is Fox–Artin 1.1*, with its own nested arc-complement
group. The parent Alexander horned solid is NOT that arc; matching
one (S_5) presentation witness or the same source Hatcher
commutator recursion does not make their ambient complements
homeomorphic or identify their fundamental groups.
Do not promote the parent geometric cover as closing Fox–Artin.


## 26 October — actually paid old/new complement incidence + cylinder orientation

This is a second step beyond the 25 October fixed frontier-label counts.

### Exact finite complementary geometry

NEW: `scripts/exotic_topology_pl_complement_components.py` imports
the **canonical existing** PL geometry and marked-frontier
implementations. It composes the literal injective vertex maps
of each old stage through every pair-of-pants or handle attachment.
It verifies that **each old oriented simplex persists**,
computes added triangles as a set difference, and computes
their actual shared-edge dual connected components. Then it
checks that the interface includes every old boundary edge
and identifies **precisely one** complementary component for
each old boundary, with all new outgoing boundary edges in
the correct component. Cantor: p→p0,p1; Loch: one persistent
tail; Jacob: two persistent tails.

Independent local reimplementation of the underlying algorithms
executed and PASSED depths 1–3:
- Cantor: 1,2,4 new components; surfaces have 2,4,8 outgoing
  boundary circles, genus zero;
- Loch: 1,1,1; new genus 1,2,3;
- Jacob: 2,2,2; new genus 2,4,6;
- adversarial collapsed old-vertex map and false lineage both
  rejected, although the false-lineage mesh itself is legal.

This establishes the *finite combinatorial analogue* of
component-by-boundary compatibility. It does NOT construct
a proper infinite locally finite PL exhaustion or prove
homeomorphism of the actual Freudenthal/Richards end spaces.
The exact pushed GitHub code has newly written tests; no
executed exact-head check receipt is yet claimed.

### Chronological Cantor cylinder interpretation: nontrivial correction

The PRE-EXISTING
`DASHI.Foundations.CantorProjectiveCylinderMeasureExact` defines
`leftChild (cylinder prefix) = cylinder (false :: prefix)`.
This is an honest reverse-stack word convention: the child
mass splits exactly because `cylinderMass` depends only on
word LENGTH. But it is NOT a refinement of the ordinary
chronological stream-prefix event where list head means
stream index zero. Example: parent prefix `[true]`, old
prepended left child `[false,true]`, and stream
`[false,true,false,...]`: the child matches and its
supposed parent does not. Thus mass equality is not an
event-inclusion proof; we must not silently identify those
two word-order conventions.

NEW: `ExoticCantorCylinderOrientationExact.agda` reuses
**the actual existing Cantor.BitStream and Cantor.Cylinder**,
defines stream-prefix event semantics, supplies correctly
APPENDED children, and proves `appendChildRefines`
by induction on arbitrary finite prefixes for every stream.
It also produces an explicit counterexample that blocks
claiming the original prepended child refines a conventional
prefix event.

NEW `scripts/exotic_topology_cantor_cylinder_orientation.py`
independently audits all 2046 prefix-child pairs at depths
0–9, tests `reverse(p ++ [b]) = b :: reverse(p)` and checks
the explicit failed old-prepend inclusion. Independent local
Python mathematical replication PASSED the corresponding
finite identities; the actual new GitHub script remains
unexecuted at its pushed SHA. The two finite tree systems
are related by **finite-word reversal**, but there is no
claim of a literal terminal-bit reversal operator on
an infinite sequence.

The original source code and attribution owner are
preserved unchanged. The new orientation bridge and its
negative control are implementation-specific DASHI results;
they are not historical theorems assigned to Richards or Cantor.

### Latest-PR Pareto and same-object boundary

26 October #1266 adds a standalone revisable-observer
consumer-factorisation file on a separate branch. This
is useful inspiration, but #1254 already uses the
canonical `QueryIndexedProjectionAdequacyExact` and
`IntersectionalNonFactorability`. We therefore do NOT
import an unmerged branch or duplicate its mathematical
framework. #1268 models source revision and independence
for another investigation; it is an attribution workflow
reference, NOT a topology theorem or primary surface source.
#1261 provides genuine crystallographic group actions,
but not a Fox–Artin geometric embedding or Richards
surface quotient. No unrelated PR is promoted by analogy.

REVISED geometric Pareto:
P0 run exact-head seven Agda kernel checks and now 22
Python regression tests (including component/word-order
negative controls), collect source-specific receipts.
P1 proper locally finite infinite collared union and
actual compact-cofinality/connected unbounded complementary
region theorem for the PL construction.
P2 identify the genuine Richards end-space topology via
the now explicit *chronological* prefix cylinder system.
P3 named Fox–Artin/Whitehead/van Kampen same-object wild
embedding, Hatcher sphere H₂ supplier, Wada/Warsaw deep
topology as independently scoped residuals.

No kernel theorem, source attribution, homotopy status
or geometric reality is auto-promoted by these scripts.
