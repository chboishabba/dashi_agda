# Yang–Mills Round Canonical Extraction Design

Date: 2026-10-17
Branch: `chatgpt/ym-round-canonical-extraction`
Base commit: `d18fd30a4efce90fc3025bbc65cafa3d7ebc5300`
Repository: `chboishabba/dashi_agda`

## 1. Purpose

The Yang–Mills historical `RoundNNN` lineage contains a large amount of theorem-bearing research history that is intentionally non-authoritative by default. After merging the strongest direct YM/Balaban open-PR owners and re-indexing the repository, the unmatched YM count remained effectively unchanged: 1,123 `TRULY_UNMATCHED_NONROUND` declarations versus the prior 1,121 baseline. This establishes that the remaining semantic value is not primarily stranded in open PR heads; it is concentrated in historical Round lineages.

This tranche performs lossless semantic compaction of those Round lineages into a small non-Round canonical residual surface while preserving attribution, provenance, negative/no-go results, and fail-closed Clay promotion gates.

The design deliberately separates:

1. historical lineage reconstruction;
2. semantic equivalence / supersession detection;
3. package-level obligation classification;
4. canonical non-Round residual owners;
5. archival receipts.

No Round module becomes authoritative merely by being selected, clustered, copied, imported, or mentioned by the tooling.

## 2. Success criteria

The tranche is complete when all of the following hold:

- the nine priority YM historical families are clustered into dependency-aware semantic packages;
- repeated scheduler/status declarations are contracted rather than counted as independent mathematics;
- renamed/non-identical current non-Round equivalents are recognized where evidence supports that classification;
- existing non-Round compiler theorems are reused rather than duplicated;
- genuinely residual obligations receive exactly one non-Round canonical owner;
- negative/no-go results remain first-class and are not erased by consolidation;
- `sourceAttachmentCountIsEighteen`-style count/status receipts are not promoted as mathematical theorem authority;
- generated package receipts record Round ancestry, semantic matches, dispositions, and selected canonical owners;
- no Round files are deleted, moved, or quarantined in this tranche;
- all Clay/YM promotion gates remain false unless an actual theorem inhabitant independently proves the promoted claim;
- `DASHI.Physics.YangMills.PostulateInventory` / `BalabanRGLane` can eventually consume the compact canonical residual surface without depending on Round scheduler modules.

A reduction in the raw unmatched declaration count is useful but is not the primary success metric. The primary metric is contraction of 1,123 unmatched declarations into a much smaller set of theorem-bearing packages with explicit dispositions.

## 3. Scope

### 3.1 Priority historical families

The first extraction tranche targets these families:

1. `DASHI.Physics.YangMills.BalabanClayCanonicalBFrontier`
2. `DASHI.Physics.YangMills.YangMillsClayCriticalPath`
3. `DASHI.Physics.YangMills.BalabanPreferredSourceSemanticsFrontier`
4. `DASHI.Physics.YangMills.BalabanPreferredRawSourceFrontier`
5. `DASHI.Physics.YangMills.BalabanPreferredSourceFrontier`
6. `DASHI.Physics.YangMills.BalabanClayHighestAlpha`
7. `DASHI.Physics.YangMills.BalabanPreferredRowCFrontier`
8. `DASHI.Physics.YangMills.BalabanCMP116R409SelectedTermReplay`
9. `DASHI.Physics.YangMills.BalabanCMP116R429TraceEntropyBudget`

Representative terminal leaves include:

- `BalabanPreferredSourceFrontierRound236Exact.agda`
- `BalabanCMP116R409SelectedTermReplayRound410Exact.agda`
- `BalabanPreferredRawSourceFrontierRound216Exact.agda`
- `BalabanCMP116R429TraceEntropyBudgetRound442Exact.agda`
- `BalabanClayCanonicalBFrontierRound298Exact.agda`
- `BalabanPreferredSourceSemanticsFrontierRound213Exact.agda`
- `BalabanRound64AdversarialMassGapSourceBoundaryExact.agda`

### 3.2 Candidate obligation names

The initial high-value names are search anchors, not automatic promotion targets:

- `positiveTransferGap`
- `literalCMP109BetaDifferenceDecomposition`
- `literalCMP109GeneratedHistoryResponseProducer`
- `literalPhysicalCompositeD1ChainRule`
- `sourceAttachmentCountIsEighteen`

The extractor must determine whether each name denotes:

- a theorem already owned non-Round under another name;
- a compiler theorem whose selected physical/source inhabitant remains open;
- a true new theorem obligation;
- a negative/no-go receipt;
- or status/bookkeeping only.

## 4. Architectural rule: package semantics before promotion

The unit of extraction is a semantic package, not an individual declaration and not an entire Round file.

For each terminal Round leaf:

```text
terminal leaf
  -> Round-only ancestry
  -> declarations in ancestry
  -> declaration dependency/package closure
  -> historical mutations
  -> non-Round exact/signature/name/structural matches
  -> package classification
  -> optional canonical owner
```

This avoids three known failure modes:

1. copying historical scheduler noise into authority modules;
2. treating renamed canonical mathematics as novel because signature/name matching is too weak;
3. splitting one evolving obligation into dozens of pseudo-discoveries.

## 5. Tranche A: package clustering and classification tooling

### 5.1 Files

Add:

- `config/ym-round-extraction-targets.json`
- `scripts/cluster_ym_round_packages.py`
- `scripts/classify_ym_round_packages.py`
- `tests/test_ym_round_packages.py`

The tooling reuses the existing read-only SQLite index and shared stranded-analysis helpers. It must not modify `.dashi/repository.sqlite3`.

### 5.2 Target configuration

`config/ym-round-extraction-targets.json` will define:

- schema version;
- target domain prefix `DASHI.Physics.YangMills.`;
- Round regex;
- the nine seed families;
- candidate positive names;
- status/count names that must not be auto-promoted;
- semantic classification thresholds / evidence policy;
- generated-output locations.

The config is declarative so future extraction batches can extend the family set without changing clustering logic.

### 5.3 Cluster construction

`cluster_ym_round_packages.py` will:

1. open the repository SQLite database read-only;
2. load module paths and import graph;
3. identify Round modules in the target families;
4. identify terminal Round leaves within each family;
5. walk Round ancestry through direct Round imports;
6. collect declarations and signature/body histories;
7. group declarations by semantic role using normalized declaration identity, lineage mutation, dependency adjacency, and repeated frontier-enum membership;
8. emit deterministic package records.

Each package record must contain at least:

- `package_id`;
- `family`;
- `terminal_leaves`;
- `round_modules`;
- `ancestor_round_count`;
- `declarations`;
- `candidate_names`;
- `signature_hashes`;
- `body_hashes`;
- `historical_mutation_count`;
- `dependency_neighbors`;
- `status_only_evidence`;
- `negative_result_evidence`;
- `source_locations`.

The output is deterministic and stable-sorted.

### 5.4 Semantic classification

`classify_ym_round_packages.py` consumes package records and compares them against the complete non-Round semantic universe, not just canonical authority reachability.

Package dispositions:

- `SUPERSEDED_EXACT`
- `SUPERSEDED_RENAMED`
- `CANONICAL_COMPILER_EXISTS`
- `ALTERNATE_PROOF`
- `NEGATIVE_RESULT`
- `STATUS_ONLY`
- `GENUINE_OPEN_OBLIGATION`
- `UNRESOLVED`

Classification evidence must distinguish:

- exact signature+body equality;
- same signature with different proof body;
- same/similar theorem role under renamed declaration;
- non-Round compiler producing the same conclusion from an explicit residual premise;
- count/status/reflexivity declarations;
- explicit false/no-go/firewall declarations;
- genuinely absent same-object theorem inhabitants.

Body-only equality is never sufficient semantic evidence by itself.

### 5.5 Renamed supersession

`SUPERSEDED_RENAMED` is intentionally stronger than the existing exact/signature/name classifier.

It requires multiple pieces of evidence, for example:

- compatible normalized type shape;
- same imported theorem carrier or conclusion type;
- shared dependency neighborhood / producer-consumer position;
- explicit historical forwarding or legacy alias;
- or a current non-Round theorem that compiles the historical target from a strictly smaller residual premise.

The classifier must emit the evidence used for every renamed/superseded decision.

### 5.6 Known example: transfer-gap semantics

Historical `positiveTransferGap` declarations must not automatically create a new canonical theorem because current non-Round modules already provide transfer-gap compilers from OS4/clustering assumptions.

The classifier must distinguish:

- the generic theorem `clustering -> PositiveTransferGap`, which may already be canonical;
- from the selected physical/source attachment proving the required clustering/spectrum premise on the literal Balaban object, which may remain open.

If the generic compiler exists but the selected inhabitant does not, the package disposition is `CANONICAL_COMPILER_EXISTS`, with the residual same-object premise recorded as the genuine obligation.

### 5.7 Known example: CMP109 repeated source frontier

Round212–225 repeatedly carry variants of:

- `literalCMP109GeneratedHistoryResponseProducer`
- `literalCMP109BetaDifferenceDecomposition`
- `literalPhysicalCompositeD1ChainRule`

These are to be recognized as one evolving source-semantics package unless evidence establishes genuinely distinct theorem objects.

The package record must preserve historical state transitions such as `open`, `blocked`, `closed`, or forwarded proof-level receipts without turning those states into theorem inhabitants.

### 5.8 Known example: count/status declarations

`sourceAttachmentCountIsEighteen` and analogous reflexive count validations are `STATUS_ONLY` unless their underlying attachment types reveal unique residual mathematical obligations.

The numerical count itself must never be promoted as Clay/YM theorem authority.

## 6. Tranche B: canonical non-Round contraction

Only packages classified as genuine residual theorem obligations receive canonical non-Round owners.

### 6.1 Canonical owner modules

The intended canonical surface is:

- `DASHI/Physics/YangMills/BalabanCMP109CanonicalSourceSemanticsObligationsExact.agda`
- `DASHI/Physics/YangMills/BalabanCanonicalPhysicalTransferGapObligationExact.agda`
- `DASHI/Physics/YangMills/BalabanCMP116CanonicalSelectedTermReplayExact.agda`
- `DASHI/Physics/YangMills/BalabanCMP116CanonicalTraceEntropyBudgetExact.agda`
- `DASHI/Physics/YangMills/YangMillsCanonicalClayResidualExact.agda`
- `DASHI/Physics/YangMills/YangMillsRoundExtractionReceiptExact.agda`

These names describe ownership intent. During implementation, if current master already contains a stronger canonical owner for one package, the existing owner must be reused rather than duplicated.

### 6.2 CMP109 canonical source-semantics owner

This owner contracts the repeated source-frontier lineage into the strongest current theorem types for the residual same-object obligations.

It may expose obligations corresponding to:

- generated-history response production;
- beta-difference decomposition;
- physical composite D1 chain rule;

but only after checking existing non-Round owners for exact or stronger formulations.

The module must not manufacture inhabitants from Round status flags, proof-level labels, source citations, or Boolean scheduler state.

### 6.3 Physical transfer-gap obligation owner

This module must not duplicate existing `PositiveTransferGap` compiler mathematics.

Its role is to identify the residual selected physical/source premise required to apply the already-canonical clustering/OS4-to-gap theorem on the literal selected Balaban object.

The owner must make clear whether the remaining payment is clustering, spectrum identification, OS interpretation, selected-object attachment, or another source-specific seam.

### 6.4 CMP116 R409 selected-term replay owner

This package must separate:

- source transcription / provenance;
- literal selected-term identity;
- executable/numerical replay;
- proof-bearing theorem equality.

Execution or matching data must not be promoted to theorem authority without a typed equality/witness.

### 6.5 CMP116 R429 trace/entropy budget owner

This package must separate:

- exact algebra/compiler structure;
- quantitative analytic inequalities;
- source-specific measure/trace attachments;
- downstream physical interpretation.

Only the genuinely residual theorem inputs become canonical obligations.

### 6.6 Canonical Clay residual owner

`YangMillsCanonicalClayResidualExact.agda` is the terminal compact scheduler.

Its purpose is to answer:

> After historical contraction and reuse of current non-Round compiler theorems, what theorem/source obligations remain unpaid on the selected Yang–Mills object?

It must contain only non-Round typed obligations and explicit composition structure. It must not import Round scheduler modules for theorem authority.

This module should become the preferred future research surface for the YM max-cut.

### 6.7 Extraction receipt owner

`YangMillsRoundExtractionReceiptExact.agda` records formal non-authority/provenance facts for the extraction tranche, including:

- Round modules are historical by default;
- extraction does not create theorem truth;
- supersession does not erase negative/no-go provenance;
- status/count receipts are not Clay payments;
- no archive/delete operation occurred;
- Clay promotion remains false.

## 7. Generated package receipt

The tooling writes:

`.dashi/round-stranded/ym-packages.jsonl`

Each row records at least:

- package id;
- family;
- terminal leaves;
- Round ancestry;
- historical declaration names;
- semantic fingerprints;
- non-Round matches;
- disposition;
- evidence for disposition;
- selected canonical owner, if any;
- retained negative/no-go results;
- unresolved residuals;
- archive status.

Archive statuses for this tranche:

- `EXTRACTED`
- `SUPERSEDED`
- `NEGATIVE-RESULT`
- `HISTORICAL-ONLY`
- `UNRESOLVED`

The generated file is a receipt/artifact, not theorem authority.

## 8. Authority and attribution rules

The tranche follows the repository's existing attribution discipline:

- source-derived mathematics remains attributed to its source owner;
- DASHI owns only formal reconstruction, typed composition, package contraction, and new compiler results it actually proves;
- a citation or historical source label is not an Agda proof;
- a Round status flag is not a theorem inhabitant;
- a numerical/executable replay is not automatically a theorem;
- a Lean theorem/source receipt is not an Agda theorem unless separately reconstructed/ported;
- same name, same cardinality, same representation, or same consumer output does not imply same-object identity;
- negative/no-go results remain visible and must not be silently overwritten by later positive routes.

## 9. Clay promotion firewall

The extraction tranche is non-promotional by construction.

All canonical owners must preserve existing failure-closed Clay/YM gates. The tranche must not set any of the following to true solely because extraction completed:

- `clayYangMillsPromoted`
- `clayPromotion`
- any equivalent Clay-completion/status Boolean

If an existing gate is imported, regression surfaces should assert that extraction does not alter it.

A future theorem may independently inhabit a canonical residual obligation; that is outside the authority of the extraction process itself.

## 10. Tests and validation

### 10.1 Python tests

`tests/test_ym_round_packages.py` should cover:

- deterministic family/terminal clustering;
- stable package IDs;
- repeated Round declarations collapsing into one package;
- `STATUS_ONLY` classification for count/reflexivity fixtures;
- `NEGATIVE_RESULT` preservation;
- `CANONICAL_COMPILER_EXISTS` when a non-Round compiler exists but selected premise remains open;
- `SUPERSEDED_EXACT` and `SUPERSEDED_RENAMED` evidence requirements;
- refusal to treat body-only equality as semantic equivalence;
- read-only database handling.

### 10.2 Agda/static validation

New canonical owner modules must be suitable for focused `dashi-agda-preflight` execution by the local loop.

No implementation response may claim kernel-green status until the user's local environment reports it.

### 10.3 Regression expectations

The local verification loop should report:

- package count by disposition;
- package count by target family;
- number of historical declarations contracted;
- number of genuine open obligations;
- canonical owners selected/created;
- retained negative/no-go packages;
- status-only packages;
- unresolved packages;
- Clay promotion gates still false.

## 11. Non-goals

This tranche does not:

- prove the Yang–Mills mass gap;
- claim Clay completion;
- delete or move historical Round modules;
- archive directories physically;
- rewrite source attribution;
- mass-import Round modules into canonical `Everything` surfaces;
- treat raw unmatched-signature count as theorem count;
- promote Casimir/GRQFT/EM/GW consumer work into the YM Clay proof spine;
- merge unrelated open PRs.

## 12. Follow-up after this tranche

After local CI/preflight verifies the extraction branch:

1. merge the extraction PR;
2. re-index master;
3. rerun stranded/non-Round classification;
4. inspect the canonical YM residual owner rather than the historical Round corpus;
5. schedule mathematical work directly against the remaining residual packages;
6. only after every lineage has an archival disposition consider a separate quarantine/archive PR.

The expected end state is not “zero Round files.” It is a repository where Round files are auditable research history and the live Yang–Mills research programme is expressed by a compact, explicit, non-Round authority surface.
