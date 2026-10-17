# Navier–Stokes Round Canonical Extraction Design

Date: 2026-10-17
Branch: `chatgpt/ns-round-canonical-extraction`
Base commit: `2307adf73d29f825becd576673abc15573fe94f7`
Repository: `chboishabba/dashi_agda`

## 1. Purpose

The Navier–Stokes historical `RoundNNN` lineages contain theorem-bearing research history, scheduler state, source reconstruction, alternate proofs, negative/no-go receipts, and analytic dead ends. The current stranded-value inventory reports 2,236 Navier–Stokes declarations as `TRULY_UNMATCHED_NONROUND`. That is an upper bound on live mathematical novelty, not evidence of 2,236 independent open obligations.

This tranche reuses the semantic-contraction architecture proven on Yang–Mills while adapting it to the different NS authority topology. The result should be a lossless contraction into:

1. correct non-Round authority roots;
2. deterministic dependency-aware historical packages;
3. evidence-backed semantic dispositions against the full current non-Round universe;
4. canonical non-Round owners only for genuinely live obligations;
5. one compact failure-closed NS residual scheduler;
6. machine-readable and typed provenance receipts preserving unresolved and negative results.

No Round declaration becomes theorem authority because it is discovered, clustered, classified, replayed, cited, or copied into a receipt.

## 2. Observed authority state on the base commit

At base `2307adf73d29f825becd576673abc15573fe94f7`, `.dashi/canonical-roots.json` contains the stale NS entry:

```text
DASHI.Physics.Closure.NSLiteralClayABCDCapstone
```

The current concrete non-Round run target is:

```text
DASHI.Physics.Closure.NSConcreteLiteralClayABCDRunTargetExact
```

The user-approved intent is therefore implemented against the manifest that actually exists on this base: replace `NSLiteralClayABCDCapstone` with `NSConcreteLiteralClayABCDRunTargetExact`. An older spelling such as `NSConcreteRunTargetAuthorityRound406Exact` is not assumed to be present.

A separate module, `NSClayOfficialSemanticPromotionBoundaryExact`, preserves the distinction between a theorem of a selected model and an official Clay-level semantic realization. This tranche must preserve and test that firewall, but **must not add it as a second canonical-root entry**. The canonical-root manifest change in this tranche is exactly the stale-root replacement above.

## 3. Tranche A — authority/root hygiene

Authority hygiene precedes any classification result used to justify canonical promotion.

### 3.1 Root manifest correction

Update `.dashi/canonical-roots.json` so the stale NS root is replaced by:

```text
DASHI.Physics.Closure.NSConcreteLiteralClayABCDRunTargetExact
```

Preserve the existing policies that:

- Round modules are non-authoritative by default;
- body-only equality is not semantic equivalence.

`NSClayOfficialSemanticPromotionBoundaryExact` remains a separately preserved/tested firewall, not a new root.

### 3.2 Remove Round523 from canonical C/D coordinate ownership

`NSClayLiteralABCDExact` currently imports:

```text
DASHI.Physics.Closure.NSTriadKNClayForcedBreakdownFormulationRound523Exact
```

for exact C/D source-coordinate audit facts. This is historical provenance and should not remain a canonical authority dependency.

Create or reuse a non-Round owner with preferred ownership intent:

```text
DASHI.Physics.Closure.NSClayForcedBreakdownSourceCoordinatesExact
```

It must preserve the source-coordinate distinctions currently used by the literal theorem surface, including at least the audited C/D requirements for positive viscosity, decay, bounded energy, periodic initial data, periodic solutions, and rapid forcing time decay.

`NSClayLiteralABCDExact` should import this non-Round owner instead of Round523. The A/B/C/D theorem types must remain unchanged.

If the historical audit relies on an unsafe/postulated base, the canonical safe owner must abstract over externally fixed facts and any concrete unsafe realization must live in a separate explicit bridge. An axiom boundary may not be hidden behind `--safe`.

### 3.3 Authority-clean condition

After Tranche A:

- the configured NS canonical root is real and non-Round;
- newly extracted canonical authority owners have zero Round imports for theorem authority;
- the official semantic-promotion firewall remains failure-closed;
- historical Round files remain present as lineage/provenance evidence.

## 4. Authority closure and semantic comparison universe are distinct

Two graphs must remain separate:

```text
AUTHORITY CLOSURE
  = modules reachable from configured promoted roots

SEMANTIC COMPARISON UNIVERSE
  = all current non-Round declarations eligible to demonstrate that historical
    Round content is exact, renamed, alternate, compiler-covered, endpoint-owned,
    provenance-only, or otherwise already represented outside Round history
```

A non-authoritative non-Round theorem may still show that a Round declaration is not novel. Conversely, absence of a non-Round semantic match never promotes a Round declaration.

## 5. Full-domain multi-prefix discovery

The NS extraction domain is the union of:

```text
DASHI.Physics.Closure.
DASHI.Papers.NavierStokes.
```

All Round families under either prefix are eligible. The configuration may carry review/ranking hints such as `priority_families`, but those hints must not restrict inclusion.

This tranche intentionally differs from the first YM nine-family extraction: the NS history is broad enough that hand-selected seeds would create another artificial lower bound on stranded value.

## 6. Shared extraction engine

Generalize stable YM package mechanics into a domain-neutral module:

```text
scripts/_round_package_extraction.py
```

Retain these existing YM compatibility surfaces:

```text
scripts/cluster_ym_round_packages.py
scripts/classify_ym_round_packages.py
```

Add NS wrappers:

```text
scripts/cluster_ns_round_packages.py
scripts/classify_ns_round_packages.py
```

The shared engine should own generic behavior including:

- configuration loading;
- multi-prefix discovery;
- Round-family discovery;
- terminal-leaf detection;
- same-family Round ancestry traversal;
- declaration/history collection;
- deterministic package IDs;
- non-Round semantic indexes;
- capped match rendering with uncapped evidence counts;
- deterministic JSONL serialization;
- archive-status mapping.

Domain wrappers provide defaults and domain-specific hints without duplicating engine logic.

The SQLite repository index is opened read-only and never mutated.

## 7. Package model

The unit of extraction is a semantic package, not one declaration and not one whole Round file:

```text
terminal Round leaf
  -> same-family Round ancestry
  -> declaration mutation history
  -> dependency/package-neighbour evidence
  -> complete current non-Round semantic matches
  -> fail-closed disposition
  -> optional canonical owner
```

Each package records at least:

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
- semantic matches and evidence counts;
- disposition and disposition evidence;
- selected canonical owner, if any;
- unresolved residuals;
- archive status.

Use a domain-specific stable-ID namespace such as `ns-round-package` so NS/YM package IDs cannot collide accidentally.

## 8. Classification vocabulary and evidence policy

Retain the proven dispositions:

- `SUPERSEDED_EXACT`
- `SUPERSEDED_RENAMED`
- `ALTERNATE_PROOF`
- `CANONICAL_COMPILER_EXISTS`
- `NEGATIVE_RESULT`
- `STATUS_ONLY`
- `GENUINE_OPEN_OBLIGATION`
- `UNRESOLVED`

NS may additionally use:

- `CANONICAL_ENDPOINT`
- `PROVENANCE_ONLY`

when evidence warrants them.

`CANONICAL_ENDPOINT` means the historical package is represented by a concrete current theorem/run-target surface rather than merely a same-signature declaration.

`PROVENANCE_ONLY` means the mathematical/source-coordinate content has already been extracted or canonically represented and the historical package remains useful only as source, chronology, or audit provenance.

Evidence may include:

- exact normalized signature + body equality;
- same normalized signature with a distinct proof body;
- renamed declarations with strong type/dependency/forwarding evidence;
- a current compiler producing the historical conclusion from a smaller residual premise;
- an existing canonical theorem/run-target endpoint;
- status/count/reflexivity evidence;
- explicit negative/no-go/firewall evidence;
- explicit provenance extraction.

The following are never sufficient theorem evidence by themselves:

- body-only equality;
- matching names;
- source citations;
- proof-level/status flags;
- Boolean scheduler state;
- generated receipts;
- executable replay;
- foreign proof hashes.

## 9. `UNRESOLVED` stays fail-closed

`UNRESOLVED` is a first-class outcome, not a temporary synonym for irrelevant.

The final report must not claim “2,236 -> N obligations” unless all other packages have evidence-backed non-open dispositions. If the result is 20 identified live obligations plus 300 unresolved packages, that exact distinction must remain visible.

## 10. Match evidence without JSON bloat

Each receipt must expose:

```text
nonround_match_count
nonround_matches
nonround_matches_truncated
```

Rules:

- `nonround_match_count` is the uncapped exact count;
- `nonround_matches` is a deterministic bounded sample, default cap 10 unless configured otherwise;
- `nonround_matches_truncated` is true iff the full count exceeds the rendered sample.

High-frequency trivial signatures may be down-ranked or labeled low-information for review, but their counts cannot be discarded.

This is additive to the YM receipt schema. Existing YM CLIs, package IDs, disposition semantics, sorting, and outputs must remain regression-compatible.

## 11. Tranche B — NS clustering/classification outputs

Expected files:

```text
config/ns-round-extraction-targets.json
scripts/_round_package_extraction.py
scripts/cluster_ns_round_packages.py
scripts/classify_ns_round_packages.py
tests/test_ns_round_packages.py
```

Generated detailed receipt:

```text
.dashi/round-stranded/ns-packages.jsonl
```

The receipt is evidence/provenance, not theorem authority.

Classification is run only after Tranche A authority hygiene so the measurement is not biased by a stale root or Round-dependent canonical coordinate owner.

## 12. Tranche C — evidence-driven canonical owner extraction

Do not pre-authorize a large list of owner modules before classification.

Inspect surviving `GENUINE_OPEN_OBLIGATION` and relevant `UNRESOLVED` packages first. Create or reuse canonical non-Round owners only where evidence supports an actual theorem/source residual.

Expected residual categories may include:

- selected physical carrier / same-object welds;
- global commutator or spacetime-payment estimates;
- Combined-to-literal-R406 transport;
- literal R406 strict-margin production;
- continuation / literal Clay assembly;
- source/released-proof reconstruction;
- exact semantic carrier attachments;
- negative/no-go constraints on future proof search.

These are expected categories, not pre-proved obligations and not automatic owner names.

### 12.1 Canonical-owner safety rules

Every newly extracted canonical owner must satisfy, where mathematically possible:

- `{-# OPTIONS --safe #-}`;
- imports only builtins and verified-safe canonical interfaces;
- zero Round imports for theorem authority;
- zero `postulate` declarations;
- zero holes (`{!!}`);
- zero `--allow-unsolved-metas`;
- attachment predicates fixed externally rather than chosen as residual fields;
- target/reference objects fixed externally rather than selected to make equalities reflexive;
- compiler structure separated from quantitative/source premises;
- no theorem inhabitant manufactured from receipts, citations, scheduler state, names, or replay data.

If a useful existing theorem depends on an unsafe/postulated base, use:

```text
safe abstract canonical owner
        +
explicit non-safe realization bridge
        +
typed receipt stating "paid relative to X" rather than unconditionally
```

## 13. Source attribution

Follow `Docs/SourceAttributionPolicy.md`.

For the literal Clay statement surface preserve the existing attribution to Charles L. Fefferman, “Existence and Smoothness of the Navier–Stokes Equation”, Clay Mathematics Institute Millennium Prize Problem description (2000). Do not invent a DOI.

For paper-specific analytic packages retain existing verified primary-source metadata and stable identifiers.

Authority-root repair, package contraction, blocker taxonomies, semantic adapters, and synthetic residual interfaces are DASHI extensions unless an external source explicitly states them.

Attribution never creates theorem authority.

## 14. Tranche D — terminal scheduler

Add:

```text
DASHI/Physics/Closure/NSCanonicalClayResidualExact.agda
```

It answers:

> After Round contraction, canonical endpoint recognition, and reuse of current non-Round compilers, what mathematical/source obligations remain unpaid on the concrete Navier–Stokes authority path?

The scheduler consumes only canonical non-Round residual owners and already-canonical concrete theorem surfaces.

Use qualified-only imports (`as Alias using ()`) or equivalent non-polluting imports where owner modules expose overlapping names.

The scheduler remains failure-closed:

```text
clayNavierStokesPromoted = false
clayPromotion = false
```

Extraction cannot set either flag true. An independently checked theorem may later feed the existing concrete run target, but that is theorem work outside the extraction authority.

## 15. Typed extraction receipt

Add:

```text
DASHI/Physics/Closure/NSRoundExtractionReceiptExact.agda
```

It must pin at least:

```text
roundsAuthoritativeByDefault = false
extractionCreatesTheoremTruth = false
statusCountsAreClayPayments = false
negativeResultsPreserved = true
unresolvedPackagesCountAsDischarged = false
roundFilesArchivedOrDeleted = false
clayPromotion = false
```

This is repository-native DASHI authority bookkeeping. It does not replace the detailed JSONL package receipt.

## 16. Preserve existing endpoint layers

The tranche must keep separate:

- theorem-type ownership: `NSClayLiteralABCDExact`;
- canonical semantic carriers / concrete semantics;
- concrete terminal run target: `NSConcreteLiteralClayABCDRunTargetExact`;
- official semantic promotion firewall: `NSClayOfficialSemanticPromotionBoundaryExact`;
- historical research coordinators and Round lineages.

No extraction refactor may collapse these into one catch-all authority module.

In particular:

- materializing A/B/C/D theorem types is not a Clay proof;
- choosing concrete semantic carriers is not a Clay proof;
- a model-level theorem is not automatically an official Clay theorem;
- a foreign proof/hash/released receipt is not automatically an Agda proof term;
- the existing official-promotion firewall remains failure-closed.

## 17. Archive/provenance policy

This tranche does not delete, move, or quarantine Round files.

`ns-packages.jsonl` may use archive statuses:

- `EXTRACTED`
- `SUPERSEDED`
- `NEGATIVE-RESULT`
- `HISTORICAL-ONLY`
- `UNRESOLVED`

A later archive/quarantine tranche may act only after evidence-backed dispositions justify it. Negative/no-go history remains discoverable even if later work finds a positive route.

## 18. Tests and validation

### 18.1 Shared-engine/YM regression tests

Generalizing the engine must not silently change established YM behavior. Regression coverage pins existing YM CLI paths, stable package IDs, disposition semantics, deterministic sorting, and outputs except for explicitly additive evidence-count fields.

### 18.2 NS package tests

Add `tests/test_ns_round_packages.py` covering at least:

- both NS prefixes;
- full family discovery without inclusion seeds;
- deterministic terminal-leaf clustering;
- stable NS package IDs;
- ancestry/mutation history;
- exact/signature/name evidence policy;
- body-only matches failing closed;
- status/reflexivity classification;
- negative/no-go preservation;
- compiler-existing residual behavior;
- fail-closed `UNRESOLVED`;
- evidence requirements for `CANONICAL_ENDPOINT` / `PROVENANCE_ONLY`;
- uncapped `nonround_match_count` with capped deterministic samples;
- correct truncation flag;
- read-only SQLite access.

### 18.3 Canonical extraction tests

Add `tests/test_ns_canonical_extraction.py` covering at least:

- the configured root is `NSConcreteLiteralClayABCDRunTargetExact` and the stale root is absent;
- no second promotion-boundary root is introduced by this tranche;
- C/D canonical coordinate ownership has no Round import;
- `NSClayLiteralABCDExact` no longer imports Round523 for canonical coordinates;
- newly extracted canonical owners have zero Round imports;
- safe owners have no postulates, holes, or unsolved-meta option;
- unsafe bridges do not leak into safe owners;
- attachment predicates/reference objects are external parameters rather than inhabitant-selected fields;
- scheduler imports canonical owners rather than Round scheduler state;
- qualified-only imports where authority names can collide;
- `clayNavierStokesPromoted = false`;
- `clayPromotion = false`;
- the official semantic-promotion firewall remains fail-closed;
- typed extraction receipts preserve unresolved and negative-result semantics.

### 18.4 Local verification boundary

Connector-side Git/source inspection does not substitute for local pytest, semantic preflight, or Agda execution. No implementation report may claim those checks passed without fresh command evidence from an environment that ran them.

## 19. Four-tranche execution model

### Tranche A — authority/root hygiene

- replace the stale root with `NSConcreteLiteralClayABCDRunTargetExact`;
- do not add a second official-promotion root;
- extract Round523 C/D coordinate ownership into a non-Round authority module;
- update `NSClayLiteralABCDExact` to consume it;
- pin authority/firewall tests.

### Tranche B — shared engine + full NS classification

- factor generic mechanics into `_round_package_extraction.py`;
- preserve YM behavior;
- add NS multi-prefix/full-family config and wrappers;
- add match-count/truncation evidence fields;
- classify all NS packages against the full non-Round semantic universe;
- generate `.dashi/round-stranded/ns-packages.jsonl`.

### Tranche C — evidence-driven owner extraction

- inspect live and unresolved packages;
- create/reuse canonical owners only where supported by evidence;
- preserve safe/unsafe boundaries explicitly;
- never manufacture theorem inhabitants from historical artifacts.

### Tranche D — terminal scheduler + receipts

- add `NSCanonicalClayResidualExact.agda`;
- add `NSRoundExtractionReceiptExact.agda`;
- thread only canonical residual owners into the scheduler;
- preserve all Clay gates as false.

## 20. Success criteria

The milestone is complete when:

1. the stale NS root has been replaced by the real concrete non-Round run target;
2. the literal A/B/C/D owner no longer relies on Round523 for canonical coordinate ownership;
3. discovery covers both NS prefixes and all Round families without restrictive seeds;
4. YM behavior remains regression-compatible;
5. every discovered NS package has an evidence-backed disposition or remains explicitly `UNRESOLVED`;
6. evidence sampling preserves full match counts;
7. negative/no-go results remain first-class;
8. every live obligation selected for promotion has exactly one canonical non-Round owner;
9. new safe owners have zero Round imports and do not hide unsafe/postulated dependencies;
10. `NSCanonicalClayResidualExact.agda` presents a small explicit residual surface rather than historical scheduler sprawl;
11. typed and JSONL receipts preserve authority/provenance boundaries;
12. `clayNavierStokesPromoted` and `clayPromotion` remain false unless independently inhabited by actual theorem evidence.

The primary metric is semantic accountability, not a cosmetically low unmatched count.

## 21. Non-goals

This tranche does not:

- prove the Navier–Stokes Millennium Prize Problem;
- claim official Clay resolution;
- manufacture A/B/C/D proof terms;
- treat citations, foreign receipts, hashes, executable replay, or status Booleans as theorem evidence;
- delete or physically archive Round modules;
- silently alter concrete Fefferman semantics;
- collapse theorem ownership, concrete semantics, run-target ownership, and official semantic promotion into one layer;
- classify `UNRESOLVED` as discharged merely to reduce headline counts;
- introduce unsafe/postulated dependencies into safe canonical owners.

## 22. Implementation-plan gate

This document specifies architecture only.

After formal review and approval of this written specification, write the task-by-task implementation plan at:

```text
docs/superpowers/plans/2026-10-17-ns-round-canonical-extraction.md
```

No Tranche A–D implementation begins before that plan is separately reviewed and approved.
