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


## 27 October integration receipt and latest parent prior art

At this cut, original twenty-space topology PR #1254 is stacked on
horned-sphere #1244, not against an arbitrary older `master`.
The inspected #1244 head
`e4567d7f2402c0e392d2d74fa9da0581d8fa168f` was
integrated by NONDESTRUCTIVE merge
`302502a746bd85b3d806a6c90956d9255cdc9092`,
with six disjoint parent source paths and no force push.
The parent now owns
`Docs/topology/AlexanderHornedC3OriginalInquiryRoadmapPhaseDeliverables20261027.md`,
`ThreeArmRadiusConnectedAssembly.lean`,
`ThreeArmRadiusConnectedHatcherTransport.lean`, and
`alexander_horned_c3_radius_overlap_witness.py`.
The child consumes that original rational-overlap script
rather than vendoring its results: each P_i=13e_i
is in the candidate C ∩ S_i, with squared
own-centre distance 16, other-centre 250 and
basepoint clearance 921. This supplies an
explicit nonempty intersection input but
NOT the required central fundamental-group
certificate, satellite path-connectedness,
source Hatcher exterior-group same-object map,
or an actual wild embedding.

**Proof/tooling receipt at this head:** 43 focused
Python test methods, 11 Agda focused kernel module
targets, and the companion Lean #86 native source
build specification. No successful exact-head
workflow execution exists in the inspected connector
state and Agda/Lean binaries were absent from the
available local container. The executed independent
local triangulation receipts are mathematical
finite checks, not source-blob/Agda/Lean kernel receipts.

**Original research priority remains** the geometric
realisation and Richards end-space comparison of the
already-built binary/ternary PL exhaustions. Power's
rigidity result and the radius-cut wild-geometry
transport are important but orthogonal consumers;
neither can substitute for the original
three-surface classification or close all twenty
source-specific hallmark problems.


## 27 October Lean v4.28.0 symbolic Cantor topology donor (not Richards actual ends)

Companion `dashi_lean4` #86 now source-writes
`Synthesis/ExoticTopologyCantorInverseLimitHomeomorph.lean`,
using the **original native** `Integration.Address.Addr n Bool`,
`CompatibleCantorTower` and its two previously implemented
inverse functions. It installs the genuine stagewise
product-induced topology on those compatible finite towers
and attempts an actual `Homeomorph` to `ℕ→Bool`
via stage evaluation, then to the literal Mathlib real
middle-thirds `cantorSet` via the preexisting source
`cantorSetHomeomorphNatToBool`. The original theorem
and continuous-product API were inspected in the
**pinned** `Mathlib v4.28.0`, not inferred from newer
unlocked documentation.

Original Mathlib source is
`Mathlib/Topology/Instances/CantorSet.lean`, header authors
Artur Szafarczyk, Suraj Krishna M S, Jean-Baptiste
Stiegler, Isabelle Dubois, Tomáš Jakl, Lorenzo Zanichelli,
Alina Yan, Emilie Uthaiwat, Jana Göken and
Filippo A. E. Nuccio, copyright (c) Jana Göken 2024.
The user-directed DASHI equivalence is a NEW
source-specific consumer, not another origin attribution.

A P0 **toolchain mismatch** was identified and addressed
*only in the focused Lean CI*: project root
`lean-toolchain=v4.35.0-rc3`, but locked
Mathlib `v4.28.0` has
`lean-toolchain=v4.28.0`. The job-local
`LEAN_TOOLCHAIN=leanprover/lean4:v4.28.0`
override and post-download assertion make
the intended source-compatible experiment
reproducible without rewriting any global
pin, manifest or unrelated theorem source.

Crucial status separation: this is a
**source-written proof of a topological homeomorphism
of symbolic coherent frontiers**, with no
successful Lean kernel receipt yet. It
is NOT a homeomorphism from the ACTUAL
topological Richards end space of a
noncompact infinite PL manifold. Thus the
original question's surface families
#5/6/7 retain the geometry/end-space
OPEN flag. This result is a same-object
stage-prefix inverse-limit advance rather
than all-surface classification.


## 27 October late: a two-link topology proof cut instead of another finite fixture

**First link — actual symbolic topology:** companion
Lean #86 source-writes
`Synthesis/ExoticTopologyCantorInverseLimitHomeomorph.lean`.
The EXISTING source `CompatibleCantorTower` (binary
coherent Fin-n-addresses from `Integration.Address`)
is equipped with the actual induced topology from
the product of all finite stage spaces.
The file uses **pinned Mathlib v4.28.0**
`continuous_pi`, `continuous_apply`,
`continuous_induced_rng`, and the original
`cantorSetHomeomorphNatToBool`, giving
a source-written homeomorphism from coherent
symbolic frontiers to both binary streams and
the literal real middle-thirds Cantor set.
Actual individual stage cylinders are
source-written **clopen** using pinned
`isClopen_discrete` and `IsClopen.preimage`,
and their child-event nesting uses the
original tower compatibility proof.
These source-written Lean results are not
yet kernel-compiled. They do not establish
anything about open/closed subsets of
the connected infinite PL surface itself.

**Second link — topology compact-cofinality:**
latest parent #1244 has a genuine consumer of
`Mathlib.IsCompact.elim_directed_cover`
in `HatcherOpenExhaustionCompactAbsorption.lean`.
After non-destructive parent merge
`0a9f434589bf494624835ed86d0c1b2af0efa51b`,
the child directly tests the original script
`alexander_horned_c3_open_exhaustion_severe_controls.py`:
increasing-but-closed and open-but-nondirected
negative examples, and a positive directed-open
cover. The source-specific Hatcher group/direct
limit inputs remain open.

The companion new native Lean #86 module
`Synthesis/ExoticTopologyCollaredCompactCofinality.lean`
proves *conditionally on actual topological stages*
that monotonic exhaustive `K_n` with
`K_n⊆interior(K_(n+1))` absorb EVERY compact
subset of X into some K_N, as well as images
of compact parametrised loops/homotopies.
It uses the SAME original Mathlib directed-open
compact absorption theorem rather than
duplicating the formal donor from #1244.

**Revised P2/P3 critical path:** construct one
actual countable locally finite oriented PL
surface X, with genuine compact stages `K_n`,
all-n collar inclusions, and source-owner
triangulation/gluing; then instantiate this
compact cofinality bridge automatically.
Next prove the actual unbounded connected
complement regions represent the unique
ends and have the compatible symbolic
cylinder basis. The genuine end homeomorphism
then factors through the already source-written
topological compatible-tower ↔ real Cantor
homeomorphism. Decorated genus still requires
the selected nonplanar-end proof at Jacob/Loch
tails.

**Clear work/status split:** actual upstream
Mathlib theorem source inspected at v4.28;
new Lean source code committed; no passing
exact-head Lean kernel or Agda module receipt;
underlying infinite PL geometric X still
unbuilt in Lean/Agda. No classical theorem
or user-authored mathematical claim is
rewritten as an AI discovery.


## Pinned geometric-realisation library selection (27 October)

The missing ALL-n actual surface carrier is no longer
to be delegated to unspecified "some Mathlib complex".

The **exact locked** Mathlib v4.28.0 contains original
`Mathlib/AlgebraicTopology/SingularSet.lean`
with `SSet.toTop : SSet ⥤ TopCat` and adjunction
`sSetTopAdj`, author header
**Johan Commelin, Kim Morrison and Adam Topaz**.
It provides REAL geometric realisation of a simplicial
set. The current-docs
`Mathlib/AlgebraicTopology/SimplicialComplex/Basic`
abstract-complex API was NOT present in that
v4.28.0 repository tree. An ITP 2026 paper
(doi:10.4230/LIPIcs.ITP.2026.21) describes
newer abstract-complex formalisation but is
not a pinned import or proof receipt.

**Preferred exact version-compatible deliverable:**
construct an actual simplicial-set carrier
`S_n` from source-owned oriented PL triangles,
all faces/degeneracies and strictly compatible
inclusion maps; take their filtered colimit
`S∞`, use ORIGINAL Mathlib `SSet.toTop.obj S∞`
and PROVE the source vertex-link circles,
local finiteness and genus/end properties
on that carrier. No existing finite Python
mesh function alone proves the simplicial
identities or the topology of its realisation.
This is the actual P2 wall: a same-object
PL→simplicial-set bridge plus a kernel
realisation theorem, not more ternary
address tests.

The Hatcher #1244 latest directed-open compact
absorption and Lean #86 collared compact
cofinality source can then be consumed on
that actual `TopCat` space. Real Cantor
source end cylinders and clopen proofs
already have a separate pinned Mathlib
supplier, but **genuine Richards end
neighbourhoods still require their own
same-object homeomorphism proof**.


## Source-first correction: REAL pinned Mathlib compact exhaustion already exists

Late 27 October exact `Mathlib v4.28.0`
audit revealed `Mathlib/Topology/Compactness/SigmaCompact.lean`
was overlooked. It already supplies an ORIGINAL
`CompactExhaustion X` with compact stages,
`K_n ⊆ interior(K_(n+1))`, full space
coverage, and its OWN
`exists_superset_of_isCompact` and
`exists_mem_nhds` theorems.
Original implementation authors:
**Johannes Hölzl, Mario Carneiro, Yury Kudryashov**
(copyright Hölzl 2017). The original topological
result remains theirs/the classical prior art,
NOT a novel DASHI compactness theorem.

Lean #86 therefore REPLACED the earlier
source-written duplicate compact-open-cover
argument in
`ExoticTopologyCollaredCompactCofinality.lean`
with the exact source-specific adapter
`sourceCollaredCompactExhaustion`.
It requires proof of the actual three fields
on our true infinite PL carrier X:
`IsCompact(K_n)` for every n,
`K_n⊆interior(K_(n+1))`, and
`⋃_n K_n = X`. This creates original
Mathlib `CompactExhaustion X`; original
Mathlib theorems now directly discharge
compact cofinality and neighbourhood stages.
The early source-written generic proof is
superseded, not treated as independent
discovery or separately attributed mathematics.

**Precise P2 critical path** is hence:
original oriented finite triangles →
compatible source simplicial-set S_n data →
filtered colimit S∞ →
pinned `SSet.toTop.obj S∞` actual TopCat X →
original Mathlib `CompactExhaustion X` →
genuine Richards ideal boundary and genus
subset identifications. Existing finite
Python fixtures and abstract StarChain
have not yet built this X or its topology.
No Agda or Lean kernel proof receipt has
been retrieved for these adapter modules.


## 27 October latest Hatcher RELATIVE exterior compactness refinement

The actual Alexander parent #1244 advanced again to
`490ef60e9c0ab355f45a2a71e6a32e8e13f165c3`.
After confirming disjoint changed paths,
#1254 was restacked by a NONDESTRUCTIVE
two-parent merge
`9d39fe2be58714484dee55623adccf998244455b`.

This newest original parent contains
`HatcherOpenExhaustionCompactAbsorption.lean`
with `compactMapAbsorbedByOpenStagesRelative`
and `compactMapFactorsThroughNestedClosedExteriors`:
for actual nested closed Hatcher handlebodies
`H_n`, a compact-image map avoiding
`⋂_n H_n` factors via some ONE open
complement `(H_N)ᶜ`, **even though**
`⋃_n (H_n)ᶜ` covers only the Hatcher
EXTERIOR and emphatically NOT the
whole ambient 3-space. This uses ORIGINAL
Mathlib `IsCompact.elim_directed_cover`,
with no fabricated full-ambient-space
surjectivity assumption. Original Hatcher
group identification and selected wild
linked embeddings remain separate.

The child now imports the owner's
`alexander_horned_c3_relative_exterior_absorption.py`
in its focused regression. The source
uses rational `H_n=[-1/(n+1),1/(n+1)]`
and compact image `[1/3,1/2]`, whose
least witnessed escaping stage is N=3;
it checks that the ambient origin remains
in every H_n, and negative cases for
noncompact domains and maps meeting
the limiting intersection. This is a
1D SOURCE-BOUNDED topological control,
not a 3D Alexander embedded wild horn
or a kernel proof of its `π₁`.

**Do not conflate the two applications:**
- Hatcher: decreasing CLOSED H_n in ambient Y,
  increasing OPEN relative exteriors Y\H_n,
  compact maps avoiding the source limit;
- Richards: increasing actual COMPACT surface
  K_n in actual X, with nested COLLAR interiors,
  whose original pinned Mathlib
  `CompactExhaustion X` gives cofinality.

Both use original Mathlib compactness,
but neither constructs the other actual
geometric carrier or its fundamental group/end
topology. Source attribution and the
source-/carrier-specific acceptance gates
remain distinct.
