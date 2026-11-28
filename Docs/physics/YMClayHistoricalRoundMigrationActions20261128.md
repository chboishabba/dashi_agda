# YM Clay historical Round migration actions

Status: generated planning and repair evidence. This document records the
semantic action classification for the live unresolved declarations found by
`scripts/round_migration_bundle_plan.py`, and the mechanically derived repair
actions from the migration/context JSON reports. It does not authorize file
deletion.

The generated machine-readable counterpart is
`.dashi/round-stranded/ym-live-bundle-plan.json`. The package matcher and
consolidation ledger provide routing evidence; they do not decide theorem
identity. In particular, a mechanically suggested terminal recipient is not a
substitute for tracing the declaration through the proof route.

## Current live bundles

| Historical declaration | Proof-search role | Migration action | Semantic recipient | New proof obligation |
| --- | --- | --- | --- | --- |
| `BalabanClayCanonicalBFrontierRound275Exact.compileCanonicalBPaymentCore` | compiler consequence | Inline into the canonical Ursell/payment bridge | `BalabanClayCanonicalBUrsellDonorBidiExact` | None new; preserve the `PositiveTransferGapCore` compiler |
| `BalabanClayCanonicalBFrontierRound330Exact.toR310RationalUpperOrderClosure` | compatibility packaging | Replace terminal use with the selected-limit closure; retain the bridge until consumers are rewired | `YMClayRouteSSelectedLimitClosureExact` | None new; the terminal route already consumes `SelectedLimitUpperClosure` |
| `BalabanClayCanonicalBFrontierRound330Exact.canonicalRound330Boundary` | audit coordinate | Inline required boundary projections into the direct-source frontier | `YMClayDirectSourceOSMassGapFrontierExact` | None new; preserve existing status/audit projections |
| `BalabanClayHighestAlphaRound77FiveAnalyticCutsetExact.round77InteractingWitnessFromLocalAndGap` | compiler consequence | Inline into the same-H interacting-witness closure | `YangMillsDirectSourceOSSameSystemH6Exact` | None new; use the existing same-H gap and OPE/Ward inputs |
| `BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact.literalClaySolutionFromTopDownThree` | compiler consequence | Inline into the Route-S literal Clay closure | `YMClayLiteralTopDownRouteSClosureExact` | None new; compile the existing A/B/C inputs |
| `BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact.continuumYM` | canonical-consumer residual | Retain as a field on the existing literal top-down construction; do not duplicate it | `YMClayLiteralTopDownRouteSClosureExact` | The UV-to-continuum same-family physical input remains conditional |

The six declarations form four source bundles. The first five are wrappers or
coordinates whose migration should preserve existing proof inputs. The
`continuumYM` field is different: it is the substantive conditional input to
the existing construction and must remain attached to that construction until
its source obligation is independently discharged.

The reconciliation also identifies three rows that are not missing theorem
mappings:

- R140 contributes two `ProofLevel` routing/status values. Preserve one shared
  status surface; do not rename them as theorems.
- R219 contributes the shared `BetaDrivenCMP119ResidualFamily` record. It has
  29 live importer rows and requires an existing non-Round owner that can
  absorb its import closure.
- R283 contributes the shared `FiniteVolumeReopeningPresentation` record. It
  has 19 live importer rows and the same acyclic-owner requirement.

These are recorded in `shared_structural_bundles` in the generated bundle plan.
They remain recipient-review items, not unresolved semantic theorem rows.

The R275 bundle has now been rewired: no nonhistorical Agda file imports
`BalabanClayCanonicalBFrontierRound275Exact`. Its deletion is still pending
because the sanctioned affected-cone check is blocked by a pre-existing
unsafe-import boundary in the shared Ursell/introspection dependency chain.

The R330 import rewiring has also been applied: its order-closure compatibility
adapter now lives in `YMClayRouteSSelectedLimitClosureExact`, and the direct
source frontier carries the existing zero-fresh-B status coordinate directly.
The former Walsh blocker is now paid constructively: `walshSpectralIdentityRaw`
is a finite 16-variable rational-ring certificate, and
`BalabanBoolean4BlockPoincareExact` is marked safe. The postulate-free trace
and finite P2 surfaces are also marked safe, and the downstream R330 cone
now reaches the intentional authority boundary
`DASHI.Foundations.RealAnalysisAxioms`. That module explicitly owns the
real-analysis postulates, so it must remain visible rather than being hidden
behind a false `--safe` annotation. The R330 deletion gate therefore remains
closed pending a separately reviewed replacement or adjudication of that
authority boundary and a fresh affected-cone check.

The constructive Walsh receipt is deliberately local: it establishes the
finite Boolean-block identity and does not promote any continuum or physical
Yang--Mills claim.

The R78 ledger recipient suggestion is therefore not authoritative: the proof
route traces both R78 declarations to the Route-S literal closure, even though
the package-level ledger can report a different single terminal candidate.

## Migration lifecycle

1. Inline compiler wrappers and audit projections into the semantic recipients
   above.
2. Keep `continuumYM` as a field of the existing literal top-down construction;
   do not create a second canonical theorem for it.
3. Rewire every historical importer and reverse-cone consumer, including
   consumers that use module context rather than a textually matched name.
4. Run the sanctioned Agda checks on each affected consumer cone and record
   their receipts in the generated lifecycle JSON.
5. Re-run the package, import, and reverse-consumer scans.
6. Delete a historical Round file only after it has zero importers, zero
   reverse-cone consumers, and a verified replacement for every declaration.

Until those gates pass, `deletion_authorized` remains false. The current JSON
is an action ledger for the next repair pass, not a claim that YM is finished.

## Automated reconciliation

`scripts/round_migration_reconcile.py` consumes the generated ledger, import
plan, candidate report, bundle plan, context audit, and probe receipts. It
separates import-edge counts from semantic declaration counts and produces
`.dashi/round-stranded/ym-migration-reconciliation.json`.

The reconciliation classes are deliberately fail-closed:

- confirmed bundle migration: an already traced source-bearing bundle with an
  explicit canonical recipient;
- metadata/status use: a live declaration used as a routing or audit value,
  not a theorem mapping;
- probe-removable batch: an exact historical import batch whose removal passed
  the sanctioned Agda probe;
- retained import requiring repair: the probe failed or has not run;
- unresolved semantic mapping: a declaration still lacks an explicit,
  non-Round canonical owner.

The three structural/status cases above are intentionally excluded from that
last class: their action is `metadata-status-use` or
`shared-bundle-migration`, with recipient assignment still fail-closed.

`round_context_probe.py --apply-probed-batches` may apply only exact passing
batches after checking the consumer source hash. It writes a checkpoint and
rollback receipt for every applied batch. A batch probe never authorizes
historical-file deletion by itself.

## Current worker-2 repair cone

The latest sanctioned probe is continuing from the previously clean R156
baseline through the R170/R168/R164 and P33 dependencies. It has already
repaired several mechanical blockers: false `--safe` annotations on
source-facing bridges, qualified record-field syntax rejected by Agda 2.9,
the rational-base import form, list-concatenation qualification, and the
custom-versus-built-in Nat addition transport. The active receipt is
`.dashi/round-stranded/ym-repair-pointwise-worker2-v53-20261129.log` on the
named Colab worker `dashi-agda-worker-2`; it is not yet a clean-cone receipt.

This is repair work on the affected dependency cone, not a new historical
Round module and not a deletion authorization. The roadmap JSON records the
active probe as `cmp98-pointwise-repair-cone-v53`.

## Migration control queues

The generated reconciliation now keeps three queues distinct:

- `migration-ready`: exact import-removal evidence that passed its probe;
- `mechanical-repair`: historical R-file/context work that can be repaired and
  rechecked by the scripted lifecycle;
- `proof-cone-external`: canonical YM/NS proof obligations exposed by a check,
  recorded for follow-up but not counted as historical-R migration work unless
  the historical bundle still uniquely depends on them.

The classification is scope-based: a `Round###` or `R###` module present in the
historical ledger remains migration scope even when its family is CMP98. The
repair planner at `scripts/round_migration_repair.py` emits hash-bound dry-run
patches and never authorizes proof search or deletion.
