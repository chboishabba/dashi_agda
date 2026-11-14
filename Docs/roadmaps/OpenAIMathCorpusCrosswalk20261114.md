# OpenAI math corpus × DASHI: full crosswalk and exact remaining maximum-cut ledger

**14 November 2026.** Source-integrity snapshots copied byte-identically from the original Lean ingress **#78** (Git head `32a7c06f2795427680173a3e61ec00c55e2e21fe`) onto **the single Golden Agda Clay rollup #1499**. They are historic, explicitly untrusted research discovery data; not proof imports. Original OpenAI work retains its source, authorship, catalogue and previous authors' credits. The original Agda provenance donor is **#1212**.

## What '900 proofs' measures and what it does not

* The **immutable vendored** `openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a` has **719 manuscripts, 372 families, 200 catalogued main-result declaration references and 189 distinct comparator configurations**, `lean/formalization.yaml` Git blob `275eee8cfab7ce49d3a5e88f02cbb8f28fe6fee6`; upstream Lean **4.34.1**.
* The **later indexed upstream revision** `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` has **721 manuscripts, 373 families, 208 main-result declaration references and 192 comparators**; YAML blob `372bcd714cd3a186a9139ac8e0f3318961fb2df1`. The 208 rows belong to this **later** revision, not to the older immutable vendor pin.
* Exactly eight declarations appeared: **one CM-Hodge**, **six Fourier local-smoothing comparator declarations** and **one subexponential SAT exact machine-count theorem**. The old 200 declarations are a strict subset of the later 208. An upstream declaration reference is neither a manuscript count, independent theorem count, nor DASHI kernel acceptance.
* Historical lexical candidate scan: **101 of 208** with one or more filename/declaration-name candidate leads, **107 without**. It used 22,761 Agda source files and 4,661 Lean source files but its **Lean Git tree was truncated**. It is NOT a complete enumeration of DASHI's current source owners. It also returns false positives (e.g., "Bass trace" matches YM Wilson insertion trace; "Littlewood" matches unrelated RH minimal estimates).
* **Six source-read comparative assessments** exist; these pay specific *source review*, not same-object equivalence. All six have `same_object_transport_paid=false` and `dashi_kernel_paid=false`. **Zero** of the 208 are admitted DASHI theorem ports on the strength of these inventories.

## Imported byte-identical records

| Original Lean #78 source | Canonical Golden snapshot | Meaning |
|---|---|---|
| `corpus_declarations_source_index_20261101.json` | local identical name | 208 source-qualified declaration references |
| `corpus_families_source_index_20261101.json` | local identical name | 373 upstream result families |
| `corpus_manuscripts_source_index_20261101.json` | local identical name | 721 manuscript records |
| `corpus_candidate_owner_routes_20261101.json` | local identical name | 208 candidates/negative rows, including stale/truncated source refs |
| `reviewed_cross_corpus_same_object_boundaries_20261101.json` | local identical name | Six reviewed exact mathematical comparisons |

All five are stored in `Docs/roadmaps/OpenAIMathCorpusCrosswalk20261114/`. The original SHA-1 Git object identity is retained, rather than rewriting a new index. The executable self-test and optional *both YAML* comparison live in `scripts/check_openai_math_full_crosswalk_20261114.py`.

## Six source-read joins (no kernel/typed transport claims)

| Upstream result | Existing DASHI comparison | Actual result / next mathematical obligation |
|---|---|---|
| **SubexponentialSAT** `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` | original Agda Boolean DAG, Tseitin counts, original OAI 378 machine via Lean #78 | Complementary: satisfy M00–M05 original circuit→literal/Finset→upstream bits and true primitive runtime/visited-space identity |
| **OptimalMaxCut** `OAI.OptimalMaxCut.main` | 27-vertex native weighted `checkerMaximumCut`, Karp-21 | Distinct: a fixed graph's optimum cannot imply unrestricted graph-family hardness; need graph-model/cost/approximation gap route for useful transfer |
| **Quasi-RH** `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` | selected RH original zero-carrier / A2-G3 | Weaker: only region Re(s)>7/8; must port exact theorem type, not infer RH |
| **CM Hodge** `HodgeCM.hodge_conjecture_for_cm_abelian_varieties` | original Hodge generalized variety/cycle-carrier owner | Strict subclass: actual rational cycle-class comparison on smooth projective CM abelian varieties, not universal Hodge |
| **Vlasov–Maxwell** `OAI.RVM.global_classical_solution` | Yang–Mills physics/source OS | Adjacent physics: classical collisionless PDE existence is not Wilson interacting QFT or OS mass gap |
| **ExactFourier** `OAI.ExactFourier.main_theorem` | Fourier circuit versus NS frequency analysis | Lexical collision; correct mathematical target is finite circuit/Fourier complexity, not PDE Fourier transform |

Independent new **OpenAI 28 October Yang--Mills** proof source and review (Lean 4.32, external existence at its own definitions) is **separate from the openai/math corpus**. Its A1–A8 targeted original Wilson/OS crosswalk is already under `Docs/roadmaps/OpenAIYangMills2026SourceExactMaxCut20261114.md` and `DASHI.Research.OpenAIMath.OpenAIYangMills2026SourceIntakeExact`.

## A/B/C/D actual completion stages

**A — Inventory and source/version authority (now stored in same Golden PR).**
Exact 719/372/200 pinned vs 721/373/208 later; Git-blob identity for all five mirrored registries; 192 comparator IDs; **no automatic upgrade** of historical review source to pinned old vendor. Refresh source author chronology and source licences individually before proof publication.

**B — Complete mathematical owner review (not yet done).**
For **every** 208 later declaration, identify original DASHI owner, earliest commit, exact source type, selected statement relationship `EXACT / STRONGER / WEAKER / COMPLEMENTARY / INCOMPARABLE / NO_MATCH / UNKNOWN`, actual proof branch and trust status. Existing 101 fuzzy owner candidates are not verified links; manually resolve and test. For each of 373 families and 721 manuscripts, classify whether any verified headline result exists, and keep no-prover-result families separate.

**C — Maximum reusable theorem transports (still open).**
Prioritize OAI 378 literal machine on Karp/Cook, OAI MaxCut hardness vs native graph carriers, CM-Hodge cycle class, quasi-RH region (no overreach), Fourier-circuit/smoothing vs actual harmonic carriers, and the independent OAI YM E1 family/Wilson object. Formulate **original same-object typed bridge** and exact witness/source properties; the six current source-read comparisons are mostly *negative controls* rather than positive theorem imports. Do not create a parallel arbitrary theorem library merely for the corpus.

**D — Kernel and production admission (still open).**
Replay the external proof under its actual upstream toolchain (4.34.1; independent YM 4.32.0) and trusted axiom audit. Port or separately check original same-object theorem to DASHI Lean **4.28.0**; transport to Agda Golden without confusing a string/JSON receipt with a native Agda proof. Route through existing `#1494/#1495/#1484` source-world, semantic DAG/dep closure, and content-addressed hyperfabric canonicalization **only after** a genuine checker+kernel receipt. Source metadata must never be marked `world_admitted` or `Agda theorem` as a side effect.

## Why the existing 101 lexical hits must not be promoted

The scan uses a comparator subject anchor plus at least two overlapping tokens. It can find useful owners but does not compare normalized theorem types, binders, universes, quantifier scope, group representation, exact lattice law, original machine clock, choice of Fourier transform or ambient finite/infinite object. It also references older repo heads. The four separate states remain `DISCOVERY`, `SOURCE_READ`, `SAME_OBJECT_PROVED`, `KERNEL_ACCEPTED`; no transition without its own receipt.

**Status on this commit: A/source snapshot integrated; historical B has 101 lexical candidates and six source-reviewed relations, none positive; genuine same-object C and kernel D remain OPEN.** This is high-volume information integration, not 208 physical/formal theorem completions.


## 14 November late continuation: the missing ORIGINAL Agda proof owners are now co-located

The first October YM intake had transferred only four OAI **source atlas**
modules, not the original `openai/math` finite circuit/CNF proof modules.
This was a real source-integration omission, now repaired.

**Eight native Agda owner modules**, and **three original Python
regression/discovery scripts**, have been imported **byte-for-byte** from
Golden donor PR #1212 at
`b1357263c117a04a9cf963da57500e583b6d1108`
onto the single canonical Golden Clay PR #1499.
The eight: `Everything`, `CorpusRegression`,
`OpenAIMathCreationOrderSerializationExact`,
`OpenAIMathFiniteSupportedTseitinModelsExact`,
`OpenAIMathLiteralCodeTransportExact`,
`OpenAIMathSharedTseitinGateCNFExact`,
`OpenAIMathSharedTseitinOptimizedCNFExact`,
`OpenAIMathSharedTseitinUniqueExtensionExact`.
Original scripts:
`check_openai_shared_tseitin_parsimonious.py`,
`run_openai_math_symbol_snowball.py`,
`test_openai_math_symbol_snowball.py`.

Existing shared-semantic original owner
`DASHI/Mathematics/Complexity/PNotEqualsNPConcreteCircuitSharedSemanticsExact.agda`
was **NOT overwritten**: the donor and current sources are 1085-line
versions with the same 35 top-level declaration identifiers and one source
difference (line 243, donor names the `ProgramAssignmentRealizes`
argument `realization`; the receiver writes its type anonymously).
This is an alpha-binder/source diff, but equivalence of the *elaborated*
terms and all downstream proof checks remains for the Golden kernel.
We retain the receiver owner/chronology, not reintroduce a duplicate.

New isolated focused acceptance owner:
`DASHI/Research/OpenAIMath/OpenAIMathFullSourceRollup20261114.agda`.
It imports the actual original `Everything.agda` source proof chain,
the six reviewed cross-corpus boundary registry, and the separate
October YM formal-source receipt. This is a source dependency root,
**not a kernel result**. Suggested local Nix checks:

```bash
AGDA_JOBS=1 DASHI_NO_TMUX=1 bash scripts/run_agda29_parallel_check.sh DASHI/Research/OpenAIMath/OpenAIMathFullSourceRollup20261114.agda
python3 scripts/check_openai_shared_tseitin_parsimonious.py --help
python3 scripts/test_openai_math_symbol_snowball.py
python3 scripts/check_openai_math_full_crosswalk_20261114.py --self-test
```

The original Agda finite #SAT/CNF source types are now physically present
together, so **source co-location is no longer the first gate**. Actual
Golden Agda 2.9 elaboration, exact upstream OAI 378 bitstream and fixed
primitive-machine M00–M05 proofs, and universal scope math are still OPEN.


## 14 November primary source pass: exactly eight post-vendor theorem references

**Source-inspected** at `openai/math@7ef5c0cc...` (again, not the
older vendored 1581 commit):

1. **CM Hodge** in `lean/ComparatorChallenges/HodgeConjectureCMAbelianVarieties/Solution.lean`,
   Git blob `e9855a415328438d063f5f3f132473bf919595e3`.
   `HodgeCM.hodge_conjecture_for_cm_abelian_varieties` quantifies over a
   **smooth projective integral complex scheme with group-object structure and
   actual `HasComplexMultiplication X`** and asserts
   `Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p`.
   Its solution directly invokes
   `OAI.AlgebraicGeometry.HodgeConjecture.MainSolution.hodge_conjecture_for_cm_abelian_varieties`.
   Compare to original Golden
   `DASHI/Mathematics/AlgebraicGeometry/HodgePrizeBoundaryExact.agda`,
   whose theorem is **universal over all smooth projective complex
   varieties**, not just CM abelian varieties. Required: same-object
   smooth-projective/cycle map and CM subgroup instantiation, **not**
   general Hodge promotion.
2. **Six Fourier LocalSmoothing comparator declarations** share ONE source
   module, `lean/OAI/Analysis/Fourier/LocalSmoothing/Comparator.lean`,
   Git blob `6def181857b8148d9dbaed288876a225ca9ddbfb`.
   They are `euclidean_local_smoothing`, `bochner_riesz`,
   `spherical_restriction`, `kakeya_maximal`, `kakeya`,
   `stein_square`, each proving its displayed reference statement
   by direct application of **upstream native analytic declarations**
   `OAI.Analysis.Fourier.LocalSmoothing.euclidean_local_smoothing`,
   `BochnerRiesz.bochner_riesz_schwartz`,
   `Restriction.spherical_restriction`,
   `OAI.MeasureTheory.Kakeya.kakeya_maximal`,
   `OAI.MeasureTheory.Kakeya.kakeya`,
   `OAI.Analysis.Fourier.SquareFunction.stein_square_literal`.
   They are **six formal named theorem witnesses but not six
   independent DASHI proof ports**; six also share one review/source module.
   Potential original DASHI users: Bishop harmonic/analytic carriers,
   RH test functional geometry, NS Fourier/multiscale source, YM
   Wick/OS test spaces. Each requires exact `ℝⁿ` Fourier normalization,
   Schwartz/Lp measures, dimension/p/effective constant and quantified
   source identification, not a word-level `Fourier` similarity.
3. **SubexponentialSAT** in
   `lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean`,
   Git blob `a69635a2492e06a26f2e33d4251edd1e21ba3332`.
   `exact_count_and_sat` fixes a concrete
   `BitProgram.Program 80 1220`, **output stack 1216**, and the
   **count tape at position 256**, over an actual original
   `SAT.CNF (Fin n)` using `Encoding.encodeCNF`. It supplies a
   `Computation.Trace`, runtime bound, and every-prefix
   `visitedSpace` polynomial. Existing DASHI finite Tseitin source
   `originalGlobalCNFCountExact` does not automatically feed that
   machine; an **original count/bitstream-input ingress** and all-source
   runtime bounds (M00–M05) are still required.

These three upstream source files pay **exact theorem signature reading**,
not upstream local checker replay or a typed DASHI carrier transport.
The eight source references add no general RH, Hodge, P≠NP, NS or YM mass-gap
claim. This source comparison refines, but does not silently edit, the
original six historical review records.

**Historical 39-obligation ledger now copied byte-identically** from
Agda PR #1212:
`docs/superpowers/plans/2026-10-31-openai-math-exact-lemma-maxcut-ledger.md`.
Earlier source protocols and exact first-implementation history remain
separately identifiable; this fresh roadmap is a status addendum, not a
retroactive claim of the old tests having run.


## 14 November: exact full vendored source volume — NOT 208 files

**Major source-inventory correction.** The **immutable**
`openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`
source tree contains **122,876 distinct `.lean` source files** under
`lean/`:

* **122,458** inside `lean/OAI/`, split across **23** academic-domain
  Git trees;
* **416** inside `lean/ComparatorChallenges/`;
* **2** at `lean/OAI.lean` and `lean/lakefile.lean`.

The first whole-`lean/` recursive GitHub tree returned **59,790**
visible Lean files with `truncated=true` and was **incomplete**.
The 23 `OAI/<domain>` and separate Comparator tree lookups all returned
`truncated=false`; their independent counts sum to **122,876**.
All exact subtree SHA and counts are in
`Docs/roadmaps/OpenAIMathCorpusCrosswalk20261114/pinned_vendor_full_lean_tree_20261114.json`.
An offline Git-object-only verifier, implemented on the one Lean rollup
#108 as `scripts/check_openai_math_vendor_tree_20261114.py`, can stream
all source path/blob identities into optional NDJSON after the
original submodule is materialized. **Its local execution and complete
source-level semantic indexing have not been performed in this
connector-only audit.**

The **200** pinned and **208** later `formalization.yaml`
`main_results` references represent selected **headline theorem
declarations**, not a full theorem/lemma inventory. The number of
all actual Lean declarations and independently checked proof terms
was **not counted** here. Do not substitute 122,876 for a number
of *proofs*, or 208 for the total source tree.

**Implication for our DASHI crosswalk:** the previous 101/208
lexical theorem-to-owner discovery is a **headline-catalogue pilot**,
not a comprehensive map of the enormous vendored Lean module graph.
The full path/blobs and import/declaration DAG need streaming
content-addressed ingestion (existing #1495 world builder) and
semantic prioritization, ideally by source mathematical dependency
and original DASHI theorem consumer, not blind copying or compiling
122,876 files into the incompatible Lean 4.28 environment.
