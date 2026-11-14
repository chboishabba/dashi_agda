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
