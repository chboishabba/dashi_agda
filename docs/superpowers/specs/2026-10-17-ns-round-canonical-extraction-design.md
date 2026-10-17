# Navier–Stokes Round Canonical Extraction Design

Date: 2026-10-17
Branch: `chatgpt/ns-round-canonical-extraction`
Base commit: `2307adf73d29f825becd576673abc15573fe94f7`
Repository: `chboishabba/dashi_agda`

## 1. Purpose

The Navier–Stokes historical `RoundNNN` lineages contain a large amount of research history, scheduler state, source reconstruction, negative/no-go receipts, alternate proofs, and theorem-bearing analytic work. The current stranded-value inventory reports 2,236 Navier–Stokes declarations as `TRULY_UNMATCHED_NONROUND` under the existing broad comparison pass. That count is an upper bound on live mathematical novelty, not a proof that 2,236 independent obligations remain.

This tranche applies the semantic-contraction architecture proven on Yang–Mills to the Navier–Stokes domain, but does not mechanically copy the YM tranche. The NS authority surface has different structure and one known authority-root defect that would bias classification if left unresolved.

The target outcome is a lossless semantic contraction of historical NS Round research into:

1. corrected canonical authority roots;
2. deterministic dependency-aware historical packages;
3. evidence-backed semantic dispositions against the full current non-Round universe;
4. canonical non-Round owners only for genuinely live obligations;
5. one compact, failure-closed terminal NS residual scheduler;
6. machine-readable and typed provenance receipts preserving unresolved and negative results.

No Round declaration becomes theorem authority merely because it is discovered, clustered, classified, replayed, cited, or copied into an extraction receipt.

## 2. Observed current authority state

At base commit `2307adf73d29f825becd576673abc15573fe94f7`, `.dashi/canonical-roots.json` contains the stale NS root:

```text
DASHI.Physics.Closure.NSLiteralClayABCDCapstone
```

That module is not the current concrete terminal authority surface. The current canonical non-Round run target is:

```text
DASHI.Physics.Closure.NSConcreteLiteralClayABCDRunTargetExact
```

The user-approved intent was to replace the historical/stale NS root with this concrete non-Round authority root. The implementation must target the manifest actually present on the base commit rather than assume an older root spelling such as `NSConcreteRunTargetAuthorityRound406Exact`.

Two distinct authority roles must remain visible:

- `NSConcreteLiteralClayABCDRunTargetExact` — concrete canonical theorem/run-target surface;
- `NSClayOfficialSemanticPromotionBoundaryExact` — fail-closed official-semantic promotion boundary.

The first fixes the concrete Fefferman semantics used by the terminal run target. The second preserves the distinction between a theorem of a selected model and an official Clay-level realization.

## 3. Authority hygiene prerequisite

Authority hygiene is Tranche A and precedes any NS stranded-value measurement used for canonical promotion decisions.

### 3.1 Root manifest correction

Update `.dashi/canonical-roots.json` so the stale NS root is replaced with:

```text
DASHI.Physics.Closure.NSConcreteLiteralClayABCDRunTargetExact
```

The manifest must continue to preserve the existing policy:

- Round modules are non-authoritative by default;
- body-only equality is not semantic equivalence.

The implementation plan should also decide whether `NSClayOfficialSemanticPromotionBoundaryExact` should be added as a second explicit NS authority root or remain reachable/documented through the concrete authority surface. The design requirement is semantic preservation of the official-promotion firewall; the plan must not silently remove that distinction.

### 3.2 C/D Round provenance extraction

`NSClayLiteralABCDExact` currently imports the historical Round module:

```text
DASHI.Physics.Closure.NSTriadKNClayForcedBreakdownFormulationRound523Exact
```

for exact C/D source-coordinate audit facts. This is a provenance/coordinate dependency, not a license for Round modules to remain canonical theorem authority.

Create or reuse a non-Round owner for those coordinate facts. Preferred ownership intent:

```text
DASHI.Physics.Closure.NSClayForcedBreakdownSourceCoordinatesExact
```

The owner should preserve the source-coordinate distinctions needed by the literal C/D theorem surface, including the currently audited requirements such as positive viscosity, rapid initial/forcing decay, bounded-energy coordinates for C, and periodic initial datum / periodic solution / rapid forcing time-decay coordinates for D.

`NSClayLiteralABCDExact` should then import the non-Round owner rather than Round523. No A/B/C/D theorem type may change as a side effect of this extraction.

If the Round523 audit depends on unsafe or postulated infrastructure, the safe canonical owner must abstract over the relevant externally fixed coordinate facts and any concrete unsafe realization must live in an explicit non-safe bridge. The authority surface must not hide an axiom boundary.

### 3.3 Authority-clean success condition

After Tranche A, the canonical NS authority roots and newly extracted authority owners must have zero Round imports for theorem authority.

Historical Round modules remain in the repository and remain available as provenance/lineage evidence.

## 4. Architectural rule: authority closure and semantic universe are different

As established by the YM extraction work, two graphs must remain distinct:

```text
AUTHORITY CLOSURE
  = modules reachable from promoted canonical roots

SEMANTIC COMPARISON UNIVERSE
  = all current non-Round declarations eligible to show that historical
    Round content is exact, renamed, alternate, compiler-covered, or otherwise
    already represented outside the Round lineage
```

A non-authoritative non-Round theorem can still prove that a Round declaration is not novel. Conversely, a Round declaration does not become authoritative merely because no non-Round semantic match is found.

The NS classifier must compare historical packages against the complete non-Round semantic universe across the configured NS domains, while authority-root reachability remains a separate promotion concern.

## 5. Scope: full-domain multi-prefix discovery

The NS tranche must not rely on a restrictive hand-curated family seed list.

The discovery domain is the union of these prefixes:

```text
DASHI.Physics.Closure.
DASHI.Papers.NavierStokes.
```

All Round families under those prefixes are eligible for clustering.

The configuration may contain `priority_families` or ranking hints for review order, but such hints must not determine inclusion. Known high-volume families such as `DASHI.Papers.NavierStokes.TheoremInterface` and `DASHI.Physics.Closure.NSTriadKNClayFrontier` may be prioritized without excluding other NS lineages.

The full-domain design is intentional: the current 2,236 unmatched declarations span substantially more history than the first YM nine-family tranche, and preselecting families would recreate an artificial lower bound on stranded value.

## 6. Shared extraction engine

The stable package-extraction mechanics should be generalized into a domain-neutral shared engine rather than copy-pasted into NS-specific scripts.

Preferred shared module:

```text
scripts/_round_package_extraction.py
```

The existing YM command-line interfaces and generated outputs are compatibility surfaces and must remain behaviorally frozen by tests.

Wrappers:

```text
scripts/cluster_ym_round_packages.py
scripts/classify_ym_round_packages.py
scripts/cluster_ns_round_packages.py
scripts/classify_ns_round_packages.py
```

The shared engine should own generic logic such as:

- loading domain extraction configuration;
- multi-prefix module discovery;
- Round family identification;
- terminal-leaf detection;
- Round ancestry traversal;
- declaration/history collection;
- deterministic package IDs;
- full non-Round semantic indexes;
- evidence-capped match rendering with uncapped counts;
- deterministic receipt serialization;
- archive-status mapping.

Domain wrappers should supply configuration defaults and domain-specific classifier hints without duplicating engine logic.

The engine must open `.dashi/repository.sqlite3` read-only and must never mutate the index.

## 7. Package model

The extraction unit is a semantic package, not one declaration and not one entire Round file.

For each terminal Round leaf:

```text
terminal leaf
  -> same-family Round ancestry
  -> declarations in ancestry
  -> declaration mutation history
  -> dependency neighbours / package closure evidence
  -> complete non-Round semantic matches
  -> fail-closed disposition
  -> optional canonical owner
```

Each package should preserve at least:

- `package_id`;
- `domain`;
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
- `source_locations`;
- `status_only_evidence`;
- `negative_result_evidence`;
- semantic matches and match counts;
- disposition evidence;
- selected canonical owner, if any;
- unresolved residuals;
- archive status.

The package ID namespace must be domain-specific but engine-generated, for example `ns-round-package`, so YM and NS IDs cannot collide accidentally.

## 8. Semantic classification

The NS classifier must retain the proven YM disposition vocabulary:

- `SUPERSEDED_EXACT`
- `SUPERSEDED_RENAMED`
- `ALTERNATE_PROOF`
- `CANONICAL_COMPILER_EXISTS`
- `NEGATIVE_RESULT`
- `STATUS_ONLY`
- `GENUINE_OPEN_OBLIGATION`
- `UNRESOLVED`

Two additional dispositions are permitted where the evidence model benefits from them:

- `CANONICAL_ENDPOINT`
- `PROVENANCE_ONLY`

### 8.1 Meaning of new optional dispositions

`CANONICAL_ENDPOINT` means the historical package is already represented by a concrete current theorem/run-target surface, not merely by a same-signature declaration.

`PROVENANCE_ONLY` means the mathematical/content-bearing coordinates have already been extracted or otherwise represented canonically, while the historical package remains useful solely as source, chronology, or audit provenance.

Neither disposition may be inferred from filename similarity alone.

### 8.2 Evidence policy

Classification evidence may include:

- exact normalized signature + body equality;
- same normalized signature with distinct proof body;
- renamed declaration with strong type/dependency/forwarding evidence;
- explicit current compiler producing the historical conclusion from a smaller residual premise;
- current terminal theorem/run-target ownership;
- status/reflexivity/count declarations;
- explicit negative/no-go/firewall claims;
- provenance-only source/audit ownership.

Body-only equality is never sufficient semantic evidence by itself.

Name matching is never sufficient same-object evidence by itself.

A source citation, proof-level flag, Boolean scheduler coordinate, generated receipt, executable replay, or foreign proof hash is never an Agda theorem inhabitant.

### 8.3 Fail-closed unresolved state

`UNRESOLVED` is first-class and must remain fail-closed.

The final report must not summarize the 2,236 declarations as “reduced to N obligations” unless every other package has an evidence-backed non-open disposition. For example, if 20 packages are `GENUINE_OPEN_OBLIGATION` and 300 remain `UNRESOLVED`, the correct frontier is “20 identified live obligations plus 300 unresolved packages”, not “2,236 -> 20”.

## 9. Non-Round match evidence without JSON bloat

The uncapped YM receipt briefly demonstrated that common/trivial signatures can match tens of thousands of declarations. Capping the displayed match list is appropriate, but the cap must not erase evidence.

Every package receipt must therefore contain:

```text
nonround_match_count
nonround_matches
nonround_matches_truncated
```

where:

- `nonround_match_count` is the full exact count;
- `nonround_matches` is a deterministic bounded sample, default maximum 10 unless configured otherwise;
- `nonround_matches_truncated` is true exactly when the full count exceeds the rendered sample.

High-frequency trivial signature classes may be down-ranked or specially labeled for human review, but their existence/count may not be silently discarded.

The classifier may add evidence-quality metadata to distinguish high-information theorem matches from ubiquitous structural matches.

## 10. Tranche B: NS clustering/classification outputs

Add NS-specific configuration and wrappers, expected to include:

```text
config/ns-round-extraction-targets.json
scripts/cluster_ns_round_packages.py
scripts/classify_ns_round_packages.py
tests/test_ns_round_packages.py
```

Generated detailed receipt:

```text
.dashi/round-stranded/ns-packages.jsonl
```

The generated file is an evidence/provenance artifact, not theorem authority.

The classifier must run over the full configured NS prefixes after Tranche A authority hygiene, so the measured baseline is not contaminated by a stale/missing root or canonical theorem owner that still imports Round provenance as authority.

## 11. Tranche C: evidence-driven canonical owner extraction

Canonical owner modules are created package-by-package only after classification identifies surviving theorem-bearing obligations.

This tranche deliberately does not pre-authorize a long list of owner names before evidence exists.

Expected categories of surviving NS obligations include, but are not limited to:

- selected physical carrier / same-object welds;
- global commutator or spacetime-payment estimates;
- Combined-to-literal-R406 transport;
- literal R406 strict-margin production;
- continuation / literal Clay assembly;
- source or released-proof reconstruction;
- exact semantic carrier attachments;
- negative/no-go receipts that constrain future proof search.

These are expected categories, not proof claims and not automatic canonical owners.

### 11.1 Canonical-owner safety rules

Every newly extracted canonical owner must satisfy:

- `{-# OPTIONS --safe #-}` where the mathematical content permits;
- imports only builtins and verified-safe canonical interfaces;
- zero Round imports for theorem authority;
- zero `postulate` declarations;
- zero holes (`{!!}`);
- zero `--allow-unsolved-metas`;
- attachment predicates fixed externally rather than chosen as residual record fields;
- reference objects / target equalities fixed externally rather than chosen to make the residual reflexive;
- explicit separation of compiler structure from quantitative/source premises;
- no theorem inhabitant from receipts, citations, scheduler state, names, or replay data.

If an existing useful theorem sits on an unsafe or postulated base, use the established two-layer pattern:

```text
safe abstract canonical owner
        +
explicit non-safe realization bridge
        +
typed receipt recording "paid relative to X" rather than unconditionally
```

This is an authority boundary, not a stylistic preference.

## 12. Source attribution

The tranche follows `Docs/SourceAttributionPolicy.md`.

For the literal Clay statement surface, preserve the existing attribution to Charles L. Fefferman, “Existence and Smoothness of the Navier–Stokes Equation”, Clay Mathematics Institute Millennium Prize Problem description (2000). Do not invent a DOI.

For source-derived analytic packages, preserve their existing primary-source metadata and stable identifiers where already verified in the repository.

New package contraction, authority-root repair, blocker taxonomy, semantic adapters, and synthetic residual interfaces are DASHI extensions unless an external source explicitly states them.

Attribution never confers theorem authority.

## 13. Tranche D: terminal scheduler

Add the terminal canonical residual owner:

```text
DASHI/Physics/Closure/NSCanonicalClayResidualExact.agda
```

Its purpose is to answer:

> After historical Round contraction, canonical endpoint recognition, and reuse of existing non-Round compilers, what mathematical/source obligations remain unpaid on the concrete Navier–Stokes authority path?

The scheduler should consume only canonical non-Round residual owners and already-canonical concrete theorem surfaces.

Where imported owners expose overlapping names such as `clayPromotion`, use qualified-only imports (`as Alias using ()`) or equivalent non-polluting imports.

The scheduler must remain failure-closed:

```text
clayNavierStokesPromoted = false
clayPromotion = false
```

Extraction itself cannot set either flag to true.

An actual proof term may independently feed the existing concrete run target. That theorem work is outside the authority of the extraction process.

## 14. Typed extraction receipt

Add:

```text
DASHI/Physics/Closure/NSRoundExtractionReceiptExact.agda
```

The typed receipt must pin at least the following authority facts:

```text
roundsAuthoritativeByDefault = false
extractionCreatesTheoremTruth = false
statusCountsAreClayPayments = false
negativeResultsPreserved = true
unresolvedPackagesCountAsDischarged = false
roundFilesArchivedOrDeleted = false
clayPromotion = false
```

The typed receipt is repository-native DASHI bookkeeping. It records authority policy and does not replace the detailed JSONL lineage/evidence receipt.

## 15. Existing canonical endpoint preservation

The extraction tranche must preserve the distinction among:

- theorem-type ownership (`NSClayLiteralABCDExact`);
- canonical semantic carriers / concrete semantics;
- the concrete run target (`NSConcreteLiteralClayABCDRunTargetExact`);
- official semantic promotion (`NSClayOfficialSemanticPromotionBoundaryExact`);
- historical research coordinators and Round lineages.

No extraction refactor may collapse these roles into one catch-all module.

In particular:

- materializing literal A/B/C/D theorem types is not a Clay proof;
- selecting concrete semantic carriers is not a Clay proof;
- a model-level theorem does not automatically become an official Clay theorem;
- a foreign proof/hash/released receipt is not automatically an Agda proof term;
- the existing failure-closed official-promotion firewall must remain intact.

## 16. Archive/provenance policy

This tranche does not delete, move, or quarantine Round files.

Suggested archive statuses in `ns-packages.jsonl`:

- `EXTRACTED`
- `SUPERSEDED`
- `NEGATIVE-RESULT`
- `HISTORICAL-ONLY`
- `UNRESOLVED`

A later archival/quarantine tranche may act only after package dispositions are complete enough to justify it.

Historical negative/no-go results must remain discoverable even when a later positive route exists.

## 17. Tests and validation

### 17.1 Shared-engine regression tests

Tests must prove that engine generalization does not change established YM behavior. Existing YM CLI paths, package IDs, disposition semantics, deterministic sorting, and output schema remain compatible except for additive evidence-count fields intentionally introduced by this tranche.

### 17.2 NS package tests

Add `tests/test_ns_round_packages.py` covering at least:

- multi-prefix discovery;
- full family discovery without restrictive seed lists;
- deterministic terminal-leaf clustering;
- stable NS package IDs;
- package ancestry and mutation history;
- exact/signature/name evidence policies;
- body-only equality failing closed;
- status/reflexivity classification;
- negative/no-go preservation;
- `CANONICAL_COMPILER_EXISTS` residual behavior;
- `UNRESOLVED` fail-closed behavior;
- optional `CANONICAL_ENDPOINT` and `PROVENANCE_ONLY` evidence requirements;
- uncapped `nonround_match_count` with capped deterministic `nonround_matches`;
- correct `nonround_matches_truncated` flag;
- read-only SQLite access.

### 17.3 Canonical extraction tests

Add `tests/test_ns_canonical_extraction.py` covering at least:

- corrected canonical root exists and the stale root is absent;
- C/D canonical coordinate owner has no Round imports;
- `NSClayLiteralABCDExact` no longer imports Round523 for canonical coordinate facts;
- newly extracted canonical owners have no Round imports;
- safe owners have no postulates, holes, or unsolved-meta option;
- anti-vacuous attachment predicates/reference objects are parameters, not inhabitant-selected fields;
- non-safe bridges are not imported into safe canonical owners;
- terminal scheduler consumes canonical owners rather than Round scheduler state;
- qualified-only imports where overlapping authority names exist;
- `clayNavierStokesPromoted = false`;
- `clayPromotion = false`;
- typed extraction receipt preserves unresolved and negative-result semantics.

### 17.4 Local verification boundary

The connector environment may inspect source and Git state but does not substitute for the user’s local semantic preflight, pytest, or Agda/kernel execution.

No implementation response may claim pytest, preflight, or Agda success unless the corresponding command output is available from the executing environment.

## 18. Four-tranche execution model

### Tranche A — authority/root hygiene

- repair `.dashi/canonical-roots.json`;
- extract C/D Round523 source-coordinate ownership into a non-Round authority module;
- update `NSClayLiteralABCDExact` to consume the non-Round coordinate owner;
- pin authority/firewall tests.

### Tranche B — shared extraction engine + full NS classification

- factor generic extraction machinery into `_round_package_extraction.py`;
- preserve YM CLI/output behavior;
- add NS multi-prefix/full-family configuration and wrappers;
- add match-count/truncation receipt fields;
- generate and classify all NS packages from the full local SQLite index.

### Tranche C — evidence-driven canonical owner extraction

- inspect surviving `GENUINE_OPEN_OBLIGATION` and `UNRESOLVED` packages;
- create/reuse canonical owners only where evidence supports the theorem surface;
- preserve unsafe/postulated boundaries through explicit bridges and typed receipts;
- do not manufacture theorem inhabitants from historical artifacts.

### Tranche D — terminal scheduler + receipts

- add `NSCanonicalClayResidualExact.agda`;
- add `NSRoundExtractionReceiptExact.agda`;
- generate `.dashi/round-stranded/ns-packages.jsonl`;
- thread only canonical residual owners into the terminal scheduler;
- preserve all Clay promotion gates as false.

## 19. Success criteria

The NS canonical extraction milestone is complete when all of the following hold:

1. the stale NS authority root has been replaced by the concrete non-Round run-target authority root;
2. the literal A/B/C/D theorem owner no longer relies on Round523 for canonical coordinate ownership;
3. the extraction engine supports both NS prefixes and discovers all NS Round families without hand-selected inclusion seeds;
4. established YM behavior remains regression-compatible;
5. every discovered NS historical package receives an auditable evidence-backed disposition or remains explicitly `UNRESOLVED`;
6. evidence sampling cannot hide the full semantic match count;
7. negative/no-go results remain first-class;
8. every genuinely live theorem obligation selected for promotion has exactly one canonical non-Round owner;
9. newly extracted safe canonical owners have zero Round imports and do not hide postulated/unsafe dependencies;
10. `NSCanonicalClayResidualExact.agda` presents a small explicit residual surface rather than historical scheduler sprawl;
11. `NSRoundExtractionReceiptExact.agda` and `ns-packages.jsonl` preserve authority/provenance boundaries;
12. `clayNavierStokesPromoted` and `clayPromotion` remain false unless independently inhabited by actual theorem evidence.

The primary success metric is not a cosmetically low unmatched count. The primary metric is semantic accountability: every historical package is either evidenced as represented, retained as negative/provenance, owned as a live non-Round obligation, or explicitly left unresolved.

## 20. Non-goals

This tranche does not:

- prove the Navier–Stokes Millennium Prize Problem;
- claim an official Clay resolution;
- manufacture A/B/C/D proof terms;
- treat source citations, foreign receipts, hashes, executable replay, or status Booleans as theorem evidence;
- delete or physically archive Round modules;
- silently change the existing concrete Fefferman semantics;
- merge theorem-type ownership, concrete semantics, terminal run target, and official semantic promotion into one authority layer;
- classify `UNRESOLVED` packages as discharged merely to reduce headline counts;
- introduce new unsafe/postulated dependencies into safe canonical owners.

## 21. Implementation-plan gate

This document specifies architecture only.

After formal review and approval of this written specification, the next step is to invoke the implementation-planning workflow and write a task-by-task plan at:

```text
docs/superpowers/plans/2026-10-17-ns-round-canonical-extraction.md
```

No Tranche A–D implementation should begin before that implementation plan is separately reviewed and approved.
