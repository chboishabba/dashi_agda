# JMD formal world: deterministic execution contract

Date: 2026-11-09. Agda is the golden mathematical owner. There is **no LLM or
agent orchestration** anywhere in this pipeline. It uses existing DASHI
preflight, AO-related formal requirements and original Lean environments.

## Existing code reused (not duplicated)

- \`dashi-repo index\` -> \`.dashi/repository.sqlite3\` with
  \`repo_symbols\`, \`repo_symbol_signatures\`, \`repo_refs\`,
  \`repo_requirements\`, \`repo_files\`.
- \`ProofDebtRouterExact.agda\`, \`ProofArchaeologyCoarseFineAdapterExact.agda\`,
  \`DependencyDerivedMinimalInvalidationBidiExact.agda\` and
  \`HierarchicalSpectralParetoExact.agda\` own the formal status and
  search/priority/invalidation laws.
- \`JMDFormalWorldReconciliationExact.agda\` supplies the Agda proof firewall,
  checked-implication composition and attribution-preserving world pairs.
- OEIS/Wikidata source owners already reside in
  \`DASHI/Wikimedia/\` (including \`ModularFormAnalyticQidGateSnowballExact\`
  and \`JInvariantOEISExactPrefixSameObjectSnowballExact\`).
- Lean PR #78 owns existing OpenAI-math candidate comparisons and catalogue
  audits; this pipeline does not create another corpus search system.

## Repository-only P0–P3 pass

From a **clean, pinned** \`dashi_agda\` checkout with canonical preflight
installed and the independent GitHub corpus CSV present in a local
\`dashi_lean4\` checkout:

\`\`\`sh
dashi-repo index --root .

python scripts/jmd_formal_world_reconcile.py \
  --database .dashi/repository.sqlite3 \
  --global-csv ../dashi_lean4/docs/roadmap/jmd_lean_corpus/github_lean_repositories.csv \
  --agda-root . \
  --image-terms Docs/roadmap/JMDImageOwnerSymbolSnowballTerms.json \
  --native-gap-limit 200
\`\`\`

This **does not clone 21,481 repos**. It admits their numeric GitHub repository
identity set, reads the existing Agda symbol/type/requirement tables, attaches
QID/OEIS IDs appearing in **exact indexed declaration source spans**, and
writes candidate-only world/gap/image links into the same SQLite database.
There is no second persistent semantic index.

For all GitHub-data checks run the independent, committed Lean PR #105 auditor
from the Lean repository:

\`\`\`sh
python scripts/audit_jmd_formal_corpus.py
\`\`\`

The 21,481 global entries, 8,764 stars, 1,996 starred Lean entries and
partition/page receipts are corpus metadata, never kernel evidence.

## P1 selected external Lean declaration extraction

For any **locally checked-out, pinned** Lean repository and a selected JSONL
file (one record per declaration) such as:

\`\`\`json
{"repository_id":123,"repository":"owner/repo","commit":"<full 40-digit git SHA>","module":"Example.Basic","declaration":"Example.Basic.theoremName"}
\`\`\`

use the extractor in Lean PR #105:

\`\`\`sh
python ../dashi_lean4/scripts/extract_jmd_lean_declarations.py \
  --checkout /path/to/existing/lean-checkout \
  --shortlist /path/to/source-shortlist.jsonl \
  --out /tmp/jmd-selected-lean-declarations.jsonl
\`\`\`

The extractor executes **Lean itself**, with \`#check\` and
\`#print axioms\`, and fails closed on missing declarations, mismatched
checkout revision or ambiguous type printouts. It does not claim the source
theorem is an Agda theorem.

To admit this already-extracted selected corpus:

\`\`\`sh
python scripts/jmd_formal_world_reconcile.py \
  --database .dashi/repository.sqlite3 \
  --global-csv ../dashi_lean4/docs/roadmap/jmd_lean_corpus/github_lean_repositories.csv \
  --external-declarations /tmp/jmd-selected-lean-declarations.jsonl \
  --image-terms Docs/roadmap/JMDImageOwnerSymbolSnowballTerms.json
\`\`\`

**Do not run untrusted third-party Lean code outside an appropriate
local isolation boundary.** Lean metaprogramming and build hooks may execute
code. Neither script sends unpublished DASHI material to outside repositories.

## P4 opt-in proof-reuse attempt (Lean LOCAL, not cross-prover)

Supply an explicit JSONL goal list, e.g.:

\`\`\`json
{"goal_id":"selected-lemma","module":"Example.Basic","proposition":"Nat.succ 0 = 1"}
\`\`\`

With the selected source declarations imported into the same DB:

\`\`\`sh
python scripts/jmd_formal_world_reconcile.py \
  --database .dashi/repository.sqlite3 \
  --global-csv ../dashi_lean4/docs/roadmap/jmd_lean_corpus/github_lean_repositories.csv \
  --goals /path/to/selected-goals.jsonl \
  --verify-lean-root /path/to/existing/lean-checkout \
  --max-probes 8
\`\`\`

The script generates a temporary Lean \`example : goal := by exact donor\`,
executes \`lake env lean\` in the pinned checkout and records the actual return
status, source/goal hashes, checker revision and output. It rejects
\`sorryAx\` and text-injection-shaped goal strings. Only a passing, current
probe is counted as \`executed_kernel_passes\`. Checker acceptance may still
depend on permitted imported axioms; the extractor records \`#print axioms\`.

The generated proof demonstrates **a Lean-local proof of the supplied goal**.
It does **not** establish cross-prover translation from Lean to Agda, equality
between original source theorem types, an accepted Clay result, or a new
general theorem-discovery algorithm.

## P5/P6 worlding and selective reopening

- \`jmd_world_sources\` keeps independent source/proof identities, revisions and
  original types; candidate links never merge source identities.
- \`worlded_goal_proofs\` groups **multiple actual accepted donor proofs of one
  identical supplied Lean goal** without claiming the donor source
  propositions themselves are equivalent.
- \`JMDFormalWorldReconciliationExact.agda\` requires proof-term-bearing
  implication/equivalence certificates to world distinct mathematical claims.
- \`jmd_world_affected\` uses the existing directed \`repo_refs\` graph to
  propagate changes to affected consumers only. Reopening is not refutation
  or a newly generated proof.
- QID and OEIS records are **discovery coordinates**, not mathematical
  deductions. Numerical collisions never promote a candidate.
- This makes progress with zero LLM calls; it may leave infinitely many goals
  unresolved because arbitrary formal theoremhood is undecidable.

## Executable local regressions

\`\`\`sh
python -m unittest discover -s scripts \
  -p 'test_jmd_formal_world_reconcile.py' -v
python -m unittest discover -s ../dashi_lean4/scripts \
  -p 'test_extract_jmd_lean_declarations.py' -v
python -m unittest discover -s ../dashi_lean4/scripts \
  -p 'test_audit_jmd_formal_corpus.py' -v
\`\`\`

Agda acceptance (from the repository's pinned Agda 2.9 environment):

\`\`\`sh
agda -i . -i DCHoTT-Agda -i cubical -l standard-library \
  DASHI/Interop/JMDFormalWorldReconciliationExact.agda
\`\`\`

**Verification status on creation:** source-written and committed; there is no
Agda/Lake executable available in the assistant's container, and the
full external 21,481-row audit and end-to-end local checkout tests have NOT
been executed here. Code source and test fixtures are not kernel receipts.

## Remaining mathematical maximum cut

1. Runtime acceptance: run the tests and full corpus audit, then execute
   a P0 native \`dashi-repo\` world pass on a clean, fresh database.
2. Selected source-faithful proposition matching and actual paired
   Agda/Lean checker receipts. Use existing owner signatures before creating
   any new foreign bridge.
3. Establish *checked* inter-language representation/interpretation
   theorems for nontrivial cases where the source and target formal
   environments differ. This cannot be inferred from names or OEIS IDs.
4. Extend beyond selected on-demand external checkouts with a bounded
   resource/supply policy, stable source revisions, and negative controls.
5. Instantiate the existing AO gap Pareto selection and reopening theorems on
   the *actual* source-aware world; do not use its LLM orchestration layer.
