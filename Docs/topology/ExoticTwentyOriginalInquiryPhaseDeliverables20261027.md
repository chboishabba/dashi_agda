# Twenty exotic spaces — original inquiry, phase gates and deliverables (27 October 2026)

**Scope:** the original user-requested twenty-object investigation. This is an
acceptance ledger, not a claim that all objects have been formalised. The
canonical inventory is `Docs/topology/ExoticTwentySpacePriorArtMaxCut20261025.md`;
the source roots and seven dependency-ranked leaves remain in
`ExoticSourceGenealogyParetoExact.agda`. This file makes the **remaining
original question** and its integration sequence explicit.

## What did we actually seek to find/prove?

For each of the twenty named objects, distinguish four logically different
propositions:

1. **Source identity:** is the construction exactly the object of its
   original paper, not a similarly shaped coordinate tuple or finite code?
2. **Same-object realisation:** does the claimed actual topological space,
   embedding, map or analytic parametrisation exist on a precisely defined
   carrier, with the required topology and domain?
3. **Discriminating theorem:** does it prove its source-specific hallmark
   (three equal lake frontiers, wildness, ends/genus, weak vs actual
   contractibility, true rank, GMT minimisation, etc.)?
4. **Kernel/paper proof receipt:** can an exact pinned proof checker verify it,
   or does a clearly dated conventional mathematical proof discharge every
   condition? Finite tests and source-written uncompiled code must not be
   confused with that last proposition.

A correct general-purpose symbolic representation of *wild*, *CW*, *C3*,
*balanced*, *ternary*, or *surface* is not automatically the source-selected
mathematical instance, much less an answer to all four questions.

## Claim-relative status on this branch

Legend: **F** = substantial finite/exact local checked example; **S** =
source-written formal statements with **no exact-head kernel receipt**; **R**
= realised carrier or geometry is conditional/partial; **OPEN** = original
hallmark theorem on the actual carrier not yet proved. Several statuses can
hold simultaneously. These are *deliverable dimensions*, not scores of
mathematical truth.

| # | Source-selected object | What is genuinely available | Essential missing acceptance |
|---|---|---|---|
| 1 | Lakes of Wada | S: exact three-common-frontier acceptance predicate; C3 incidence negative control | Construct three **connected disjoint open planar regions** with proved identical nonempty frontiers |
| 2 | Wild knot | F/S: genuine braid-group quotient negative discriminators, finite linked-marker no-go | An actual embedded S¹ with a source-specific non-local-flat point and isotopy/wildness obstruction |
| 3 | Wild arc | F/S: horn address/collar source and separate local-vs-global invariants | Actual interval embedding and local punctured-neighbourhood/wildness certificate |
| 4 | Fox–Artin wild arc | F/S: ORIGINAL Example 1.1* finite S₅ nontrivial group-presentation witness | Identify its **actual** geometric complement fundamental group by van Kampen/limit; then separate examples 1.2 and 1.3 local tests |
| 5 | Cantor-tree surface | F: finite oriented binary and balanced-ternary PL stages, 1/2/3-way boundary ancestry, complement incidence and stable stars; S: abstract all-depth star implication | Uniform collared countable simplicial realisation and **actual Richards end-homeomorphism**, all planar ends |
| 6 | Jacob’s ladder | F: genus 2n, two geometric outgoing tails and stable stars | Infinite two-ended surface, both ends nonplanar, genuine genus/end classification |
| 7 | Loch Ness monster | F: genus n, one geometric outgoing tail and stable stars | Infinite one-ended nonplanar surface and its genuine classified homeomorphism type |
| 8 | Warsaw circle | F/S: literal sine-curve closure plus polygonal joining arc, source written literal Lean carrier | Compactum topology with vanishing homotopy groups and **noncontractibility** / shape obstruction on the same space |
| 9 | Whitehead theorem | D: existing cochain/CW donors, real Mathlib CW class | Weak homotopy equivalence between actual CW carriers implies genuine homotopy equivalence; no substitution of cochain equality |
| 10 | CW complex | D/S: native Mathlib classical/abstract CW, CP¹ finite 0+2-cell H² model | Source-specific characteristic disk attachments and actual CW topology for required nontrivial targets, cellular-to-singular comparison |
| 11 | Schoenflies problem | D: Alexander/Hatcher collar evidence and conditional van Kampen cover | Actual locally flat source-selected codimension-one embedding and complementary n-ball theorem; wild counterexamples typed separately |
| 12 | Ida surface | F: source parametrisation/trigonometric identification and denominator positivity | Exact global immersion/rank and Klein quotient theorem on the original domain |
| 13 | Riemann surface | D/S: actual native CP¹ projective space, atlas, sphere homeomorphism and singular-chain transports | General surface definition and complex analytic chart glue for requested instances; CP¹ degree-two ordinary singular result from source-compatible kernel import |
| 14 | Morin surface | Source/formula donor identified | Genuine immersion of sphere, rank two everywhere and regular homotopy realising a sphere eversion |
| 15 | Nielsen–Thurston | Finite braid/permutation shadow and selected modular representation | Actual surface mapping classes and full periodic/reducible/pseudo-Anosov trichotomy with dynamical invariants |
| 16 | Pinched torus | F/S: finite CW quotient/homology and source-written Lean pinching | Actual torus quotient topology, local singularity and a justified comparison to the combinatorial model |
| 17 | Simons cone | F/S: real polynomial/image/link algebra, gradient singular set | Original Bombieri–De Giorgi–Giusti geometric measure theory **area-minimality** theorem on the actual cone |
| 18 | Seifert surface | F: finite Euler data, braid-information-loss witnesses | A genuine oriented diagram-to-embedded band/disk surface, whose boundary is the specified link |
| 19 | Seashell surface | F/S: source-specific analytic parametrisation and seam identities | Complete original domain, embedding/singularity chart and boundary theorem |
| 20 | Whitney umbrella | F/S: real semialgebraic image is precisely `x²=y²z, z≥0`, polynomial and differential checks | Kernel typecheck and global singular/double-locus stratification on the exact parametrised carrier |

**None of these twenty source-specific hallmark tasks has an exact pinned
Agda/Lean kernel receipt discharging its complete acceptance specification
in this tranche.** A later compiler receipt must identify the checked theorem,
actual source SHA, imports, toolchain and which geometric hypotheses it uses.

## Dependency phases, gates, deliverables, stop conditions

| Phase | Priority | Deliverables | Acceptance gate / what can actually be promoted |
|---|---|---|---|
| **0 — Evidence and pins** | Immediate, highest fanout | Exact-head Agda and Lean module-build results; full source-specific Python regression; source atlas and reproducible receipts | Each result bound to commit SHA/toolchain/source text; *no* claim of proof merely because CI YAML exists |
| **1 — Reusable finite geometry** | Substantially paid, still check | Correct finite oriented pants/handles; triangulation orientation, vertex links, old-stage inclusion, descendant genealogy, exterior-component bijection, stable vertex stars, signed-zero preserving ternary 1→3 two-pants; finite sphere caps | Actual tested simplices on same mesh; distinguish bounded check from induction. Whole-graph Maxwell equalities alone never imply all-subgraph sparsity |
| **2 — All-n geometry → actual space** | **Decisive next cut** | Instantiate `ExoticSimplicialStarTransportExact.StarChain` with *real* recursively generated K_n; construct injective simplicial direct union; weak geometric realisation and local-finiteness theorem | Countable, Hausdorff, connected, orientable, second-countable **boundaryless 2-manifold** and compact-cofinal exhaustion, not just compatible words |
| **3 — Genuine end invariant** | Depends on phase 2 | Finite frontier/component maps → unbounded complementary regions, proper nested rays/tails, chronological product-cylinder basis, end genus | An actual homeomorphism from Richards ideal-boundary topology of **that same surface** to binary/balanced streams, with planar/nonplanar subsets; Richards classification of the three surfaces |
| **4 — Source-specific hard examples** | Parallel once donors exist | Fox–Artin local/ambient group transports; Alexander based group iso; Wada domain interleaving; Warsaw shape; genuine homotopy/CW; source-selected embeddings, immersions, analytic and GMT | No promotion of group presentation to geometric \(\pi_1\), symmetry to wildness, algebra to minimality, or homotopy shadow to homeomorphism |
| **5 — Integration and communication** | Last | One claim-evidence-gate matrix per all 20 objects, exact theorem references, passing kernel receipts, source-root bibliography, unresolved counterexamples, and reproducible replay instructions | Every claimed closed object has a proof-checkable actual carrier + hallmark and no remaining admitted geometric interface |

**Cross-cut:** Power's 2025 theorem gives existence of some special countable
(3,6)-tight triangulation of each noncompact surface, not an automatic
property of the current genus-positive DASHI meshes. Power's 2024 preprint
and 2025 journal article are **one** intellectual source with a publication
history. The Euler–Maxwell necessary whole-graph boundary budget

\[
3V-E=6-6g-3b+L,\qquad L_{\mathrm{necessary}}=3b+6g
\]

is source-written in Lean #86 and numerically checked on finite DASHI
meshes. A selected genus-one/one-tail stage needs boundary length 9
(rather than 3); a genus-two/two-tail stage needs 18 (rather than 6).
**Merely subdividing enough boundary edges is insufficient**:
the source mesh retains a dense induced old-vertex core violating the
(3,6)-sparse subgraph condition. The new negative-control script
`scripts/exotic_topology_power_boundary_surgery_counterexample.py`
exhibits the actual counterexamples, so future construction must reuse
Power's interior-vertex-splitting, Henneberg 0-extension and carefully
selected rigid subgraph substitutions.

## Pareto recommendation in terms of the original question

**First** acquire at least one exact-head successful kernel receipt, then
instantiate the actual `StarChain` of phase 2. **Second** derive the Richards
end-topology comparison, which retires **three requested object families**
and the binary/balanced ternary same-type question at once. **Third** keep
Alexander/Hatcher and Fox–Artin source-geometric complement proof obligations
separate. The remaining one-off hard theorem owners (Wada, Warsaw,
Nielsen–Thurston, GMT, Morin) are not cheaply closed by adding finite
decorative examples.

Avoid a false milestone: finite stage genus/boundary counts, literal
prefix bijections and even exact finite PL star checks do **not** construct
the infinite surface or its Freudenthal/Richards end space.

## Attribution and evidence hierarchy

Original theorem/construction authors retain their claims:
Brahana (1921), Kerékjártó (1923), Richards (1963),
Fox and Artin (1948), Alexander (1924), Yoneyama/Wada
(1917 onward), Whitney, Seifert, Simons and
Bombieri–De Giorgi–Giusti (1969), Artin's braid papers
(1925/1947), Hatcher (2002), Atiyah (1988) and Power (2025).
The source atlas records dated original roots, versioned
reprints and original-contributor implementations separately.
Jack McCarthy owns the relevant external Hatcher-at Lean sphere
homology implementation; source code is not an in-repo kernel receipt
unless version-compatible compilation is established.

The specific DASHI finite PL algorithms, proof interfaces,
signed 369↔balanced choices and regression harness are
user-directed, AI-assisted repository developments;
they do not transfer original discovery credit.
A source citation, DOI, cross-link, Power theorem or
successful bounded Python run is **not** a proof of a source
object on a different carrier.

For executable evidence, see the existing
`tests/test_exotic_topology_maxcut.py`,
`scripts/exotic_topology_power_36_tight_nonpromotion.py`,
`scripts/exotic_topology_power_boundary_surgery_counterexample.py`,
`scripts/exotic_topology_pl_stable_stars.py`
and the two focused CI workflow files in Agda #1254 and Lean #86.
