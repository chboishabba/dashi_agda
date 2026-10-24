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
