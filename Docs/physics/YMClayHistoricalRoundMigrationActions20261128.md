# YM Clay historical Round migration actions

Status: planning evidence only. This document records the semantic action
classification for the live unresolved declarations found by
`scripts/round_migration_bundle_plan.py`. It does not authorize import edits,
declaration moves, or file deletion.

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

The R275 bundle has now been rewired: no nonhistorical Agda file imports
`BalabanClayCanonicalBFrontierRound275Exact`. Its deletion is still pending
because the sanctioned affected-cone check is blocked by a pre-existing
unsafe-import boundary in the shared Ursell/introspection dependency chain.

The R330 import rewiring has also been applied: its order-closure compatibility
adapter now lives in `YMClayRouteSSelectedLimitClosureExact`, and the direct
source frontier carries the existing zero-fresh-B status coordinate directly.
The former Walsh blocker is now paid constructively: `walshSpectralIdentityRaw`
is a finite 16-variable rational-ring certificate, and
`BalabanBoolean4BlockPoincareExact` is marked safe. The downstream R330 cone
now reaches a separate pre-existing unsafe import at
`BalabanClayP2LargeFieldStepVExact`; the R330 deletion gate therefore remains
closed pending that boundary repair and a fresh affected-cone check.

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
