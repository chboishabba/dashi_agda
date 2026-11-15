# Proof world: scalable semantic joins and revision-delta compatibility (11 Nov 2026)

## Correct the architecture, don't build a 21k-repository all-pairs join

The validated source pilot is 9,577 real Lean files / 104,842,666 original bytes
from three immutable repositories. Those source records are a durable substrate,
not a theorem-index census or a proof of global semantic admission.

This plan reconciles the existing original PR #1483 W01–W10/K01–K02/I01
fibre roadmap, #1484 exact canonical statement byte identity, and the Agda
`DASHI/Core/ProjectionFibre.agda`,
`DASHI/Core/FibreRestrictionCore.agda`,
`DASHI/Interop/PNFHyperfabric369.agda`,
`DASHI/Interop/UnifiedMathLanguageSpine.agda` and PNF residual disciplines.

The ten-theorem conjunction compiler is an acceptance fixture for actual Lean
proof reuse, **not** the general semantic graph expansion strategy.
Avoid manufacturing a gigantic set of conjunction theorems merely because
donors coexist in one context. Compose only against explicit goals or meaningful
typed theorem patterns.

## Data tiers and proof obligations

* **O / Original:** immutable (repository, revision, path, bytes, Git blob,
  sha256, license/attribution), declaration name, original proof occurrence,
  precise dependency and environment/toolchain closure.
* **E / Elaborated:** Lean kernel-level expressions: type, value (if present),
  universe parameters and binder structure. A source regex, theorem title,
  natural-language embedding, textual variable name, or type-head projection
  alone never manufactures E.
* **N / Canonical within a foundation:** serialise Lean expression DAGs
  including fully qualified constants, universe constraints and de Bruijn bound
  variable indices, with validated source-to-expression mapping. Alpha-equivalent
  bound-variable renamings should not change identity. Do not erase constant
  identity, typeclass assumptions, coercions or mathematical universes.
  Definitional equality is a Lean checking operation, not arbitrary Python
  structural-string rewriting.
* **F / Fibres:** bounded materialised indices by foundation, proposition
  head, Pi/binder arity, typed skeleton, subterm features, target/hypothesis
  polarity, mathematical domain and context. Exact type buckets and fibres
  retain ALL source/proof occurrences. A fibre match generates a **candidate**,
  never an equality certificate.
* **T / Transport:** explicit certificates for type unification, parameter
  renaming/permutation, definitional equality, proved iff, one-way implication,
  type isomorphism and cross-foundation functors. Every transport keeps its
  orientation and original proof/source attribution. Never quotient a one-way
  implication into equality.
* **H / Hyperfabric:** context-indexed incidence, typed restriction/transport
  interfaces and residual obligations. Preserve mismatch witnesses and separate
  projection coincidences from actual commuting diagrams. Do not expand the
  full fabric into a global Cartesian product.

These layers are not interchangeable. The installed PR #1483 index only
partially implements F (exact dedup and bounded type-head/universe lookup).
The declared Agda carrier/projection infrastructure does not yet pay all
Lean semantic unification or cross-foundation transport obligations.

## Incremental bounded algorithm

1. Ingest bytes and immutable occurrence provenance once (already paid in
   three-repository pilot). Reuse identical blob bytes across occurrences.
2. Elaborate **only a requested dependency cone or changed source closure**,
   respecting its original toolchain and package manifest. Persist original
   expression/type/proof DAG and reverse edges.
3. Add exact source-preserving type indices and typed structural feature
   postings (not repository-pair indexes). Sparse, selective posting retrieval;
   popularity-limited generic features and approximate semantic retrieval are
   OPTIONAL ranking hints only.
4. On a user goal or newly admitted theorem, compute its typing constraints
   and retrieve at most a declared k candidates from each relevant fibre;
   prioritize exact matches, syntactic unification, reusable known transport
   rules and previously admitted proof edges.
5. Check only those candidate compositions with Lean; cache attempts,
   successful term hashes, counterexamples/errors, theory profiles and failed
   transport obligations. Bounded depth/time/output and explicit truncation
   receipts, no completeness claim on truncation.
6. Materialise certified implication/iff/transport edges and the small
   hyperfabric neighbourhood needed by the current goal. Incrementally
   invalidate only affected reverse dependency cones on revision updates.

Costs should track source bytes, indexed declarations, actual dependency
edges and selected candidate checks, **not O(repos²)** or O(theorems²)
global pair enumeration. An index budget controls output candidates, not
total elaboration time, recall or mathematical completeness. Record those
remaining costs separately.

## Version compatibility is a measured change relation, not an unconditional wall

Treat upstream versions as versioned original worlds linked by deltas:

* Exact same bytes and unchanged elaborated dependency closure:
  reuse prior source/type/proof receipts under a checked compatible profile.
* Changed source bytes but unchanged checked declarations/types:
  preserve both original occurrences and link them by a validated statement
  identity and proof lineage; do not pretend the source revision is unchanged.
* Renames/moves: candidate mapping first, exact checked declaration/type and
  dependencies before claiming equivalence.
* Changed theorem type, universe, imported constant, instance or semantics:
  invalidate dependent proof-closure receipts and attempt targeted re-elaboration
  or an explicit transport certificate.
* Changed Lean/toolchain/package ABI: test parsing, elaboration, kernel
  compatibility and compiled OLean reuse separately; a source file working
  under two versions does not imply OLean binary compatibility.
* Toolchain migration succeeds only if the selected original theorem and its
  dependencies recheck in the target environment; record the resulting new
  evidence, not overwrite the original proof owner.

For diff work use immutable Git tree comparisons, changed blob inventories,
declaration identity/proof-expr diffs and reverse dependency closures. Prefer
a per-file or per-declaration delta over downloading or recompiling a full
repository revision when the unchanged content is already present.

## Immediate maximum cut, not another conceptual rewrite

**C0** Build a revision delta inventory against the ALREADY ingested Batteries
and mathlib snapshots. Inspect actual changed source paths and dependency
closures; don't ingest the entire v4.28.0 tags just because their tags match
the current compiler.

**C1** Produce an exact canonical Lean declaration/type DAG for a real
selected module, binder-safe across renaming and distinct from type-head F.
Retain original source/proof occurrences from PostgreSQL.

**C2** Establish conservative typed feature postings and goal-directed
bounded retrieval over existing exact/fibre indices; tests must include
alpha-renamed equality, renamed constants that are NOT identified, changed
universe constraints, altered assumptions, permutation/isomorphism requiring
transport and truncation.

**C3** Connect the retrieved candidate to Lean proof construction through
unification/proof-derived edges. The ten-donor conjunction is merely a
compiler roundtrip/SQL-closure smoke; benchmark more meaningful rewrite,
implication, iff and theorem-reuse chains.

**C4** Persist version-delta edges, certified transports, failure residuals
and invalidation dependencies without replacing earlier immutable owners.

Source world and semantic admission remain separate. Independent Nanoda
verification is deferred by operator instruction; Lean must still check
any proof claimed as elaborated/valid in its indicated original environment.

## Acceptance and operational measurements

Report actual input bytes, changed files/decls, untouched reused source bytes,
re-elaborated dependency nodes, exact matches, typed candidate recall on
labelled regression fixtures, top-k omissions, checked transports,
certified newly composed proofs, cache hits, peak process RSS, PostgreSQL
growth and worker time. Never claim global semantic completeness or automatic
21k-repository equivalence on these local receipts.


## 12 November 2026 — authoritative phased consolidation

**This is a supersession pointer, not a blanket claim of implementation.**
The authoritative cross-project roadmap is
[`docs/roadmaps/LeanWorldProofSearchCompressionMaxCut20261112.md`](roadmaps/LeanWorldProofSearchCompressionMaxCut20261112.md),
with machine-readable status, acceptance, exact **proposed** lemma names and
dependencies in
[`docs/roadmaps/LeanWorldProofSearchCompressionObligations20261112.json`](roadmaps/LeanWorldProofSearchCompressionObligations20261112.json).

The new cross-owner maximum cut connects the already-owned Aristotle MCGS
hypergraph/residual search, Agda repository-intelligence similarity and proof
preflight, typed PNF fibre/hyperfabric, FRACDASH signed-IR/generative encoding,
the existing `StringMDLCore` strict-improvement contracts, and Lean source
PostgreSQL/canonical AST substrate. It does **not** create a duplicate
repository-intelligence database or authority layer.

The previously measured three-repository source pilot remains **operator
locally validated**, while genuine typed-Lean term admission, bounded
goal-directed proof joins, real-term grammar/FRACDASH program synthesis, exact
full-term reconstruction and physical MDL wins are **OPEN**. The newer
source-written big-proof-join tranche is not the global matching algorithm and
has no new local kernel-acceptance receipt at its later heads.

Independent Rust verification is explicitly deferred; local Lean and Agda
checking retain their respective formal authority. Preserve historical
owner, contributor/author, revision, licence and proof-lineage attribution.
