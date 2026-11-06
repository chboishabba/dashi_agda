# Karp-21 compiler repair: O/R/C/S/L/P/G/F, 6 November 2026

**Authority:** `chboishabba/dashi_agda` PR [#1445](https://github.com/chboishabba/dashi_agda/pull/1445), branch `chatgpt/karp21-reduction-transport`. **Golden:** Agda source and actual pinned Agda compiler receipts; Lean is a comparison/donor lane and Python is an executable referee, not the proof authority.

## Typed interpretation

`DASHI/Mathematics/Complexity/Karp21CompilerRepairGovernanceExact.agda` is the source-native record `CompilerRepairLane` with named O/R/C/S/L/P/G/F fields, a closed five-constructor `RepairIssue` enumeration and `reportedGapCountExactlyFive`. This is an exact *historical diagnostic inventory*, not a claim that five errors remain after patching.

- **O — Organisation:** DASHI / Karp-21 Formalization Lane.
- **R — Request:** PR #1445, compiler diagnostics and preflight stabilization, with exact branch/source attribution.
- **C — Code:** original `CookLevinCircuitGCTBoundary` and indexed `BooleanFormulaSATSelfReductionExact`, gamma roundtrip, Fin construction-cost theorem, clique-cover edge, referee and regression test.
- **S — State:** User-supplied local receipt at **`2340ed9374f825af7e61d38a7319da5901e2dded`**, using **Agda 2.9.0**, Python **3.14.8** in `.venv`, and `scripts/run_agda29_parallel_check.sh`. This is a *historical observed head*: subsequent GitHub repair commits must be rechecked before claiming success.
- **L — Lattice:** `compilerObserved → sourcePatched → pythonPreflightPassed → agdaKernelAccepted`; this is a tracking order, **not** an implicit proof promotion.
- **P — Proposal:** repair each diagnostic in the existing owner and its consumers, then rerun the exact-head parallel verifier and collect first compiler failure.
- **G — Governance:** `canPromoteWithoutReceipt` is false for **all** statuses, including the label `agdaKernelAccepted`; the `KernelPromotion TrustedReceipt` interface requires a separately supplied trusted witness. The Agda declaration does not forge or instantiate a compiler receipt.
- **F — Gap:** five observed initial issues, four Agda compiler failures and one preflight-regression defect.

The formal model respects `DASHI.Core.AuthorityBoundary`'s citation-versus-artifact distinction, plus the observation→consumer refinement of `DASHI.Core.SequentialConsumerExperimentPlannerExact`. In `dashi_lean4`, `AgdaMirror/AuthorityBoundary.lean` mirrors that distinction, and `AgdaMirror/LoomRelationAlgebra.lean` separates evidence status from promotion. These Lean surfaces are **not** independent proof receipts for the Agda repairs, and the Agda compiler-repair ledger deliberately does not import the currently unmarked-safe authority module into a `--safe` Golden root.

## Repaired sources and acceptance cuts

| Historical diagnostic | Actual source change on PR #1445 | Acceptance gate |
| --- | --- | --- |
| `CookLevinCircuitGCTBoundary.agda:40` reserved constructor | Renamed original constructor to `formulaVar` in the owner, in the indexed SAT self-reduction owner, and in matched downstream Cook/SAT consumers. | Compile `Karp21CookGoldenEverything.agda`, followed by affected P≠NP and indexed SAT consumers. Run full-tree `check_karp21_reserved_formula_constructors.py` to detect any remaining legacy aliases; fix in place. |
| `Karp21GammaBinaryRoundTripExact.agda:64,68` missing `+` | Import `_+_` from `Data.Nat.Base` in the original gamma owner. | Compile `Karp21GammaGoldenEverything.agda` under Agda 2.9. |
| `Karp21BinaryFinMaterializationCostExact.agda:67,69` incorrect named argument | Replace `NatP.≤-refl {n = suc u}` with the actual implicit `{x = suc u}`. | Compile that `--safe` exact file. |
| `Karp21CliqueVertexCoverExact.agda:68` missing `with` refinements | Capture `picked u in eqU` and `picked v in eqV`; supply `eqU,eqV` to clique lemma and `cong negBool` transports for cover. Also capture `adjacency u v in eqAdj` for the reverse direction rather than relying on `refl`. | Compile `Karp21CliqueVertexCoverExact.agda` and `Karp21RawGraphValidatorObservationExact.agda` against the original owner. |
| `referee_karp21_maxcut.sh:46` recursive self-test | Remove `python3 scripts/check_karp21_referee_no_agda.py` **from inside the referee**. Run this test independently as CI already does. Retain four original preflight checks plus the new reserved-constructor checker; update the isolated fixture's CHECKERS tuple. | `python3 scripts/check_karp21_referee_no_agda.py` and `bash scripts/referee_karp21_maxcut.sh preflight` must both pass without recursion. |

**Strict next run on the user's local environment** (Agda/venv unavailable to this connector session):

```bash
git fetch origin chatgpt/karp21-reduction-transport
git switch chatgpt/karp21-reduction-transport
git pull --ff-only
.venv/bin/python scripts/check_karp21_referee_no_agda.py
.venv/bin/python scripts/check_karp21_reserved_formula_constructors.py
bash scripts/referee_karp21_maxcut.sh preflight
bash scripts/run_agda29_parallel_check.sh
```

Keep **per-root exact compiler diagnostics**, pinned source SHA and exit codes. A successful Fin-index decoder at the *old* head is not a receipt for the changed graph/Cook roots at the *new* head. Do not report the Karp-21 NP-completeness chain closed; its source/gamma/bit-tape clocks, encoded reductions and actual `CertifiedKarpNetwork` remain independently open.

## Same-object documentary policy

The Python scripts are execution/referee surfaces, not new mathematical problem definitions. The one original finite signed Max-Cut and Cook SAT semantics must remain the inputs of any repaired Golden theorems. When compiler feedback identifies a new issue, change the original source owner and this ledger together; do not add an assumed Boolean pass marker or construct a fake `TrustedReceipt`. The Lean authority and Loom relations may be used for vocabulary, never to override the Agda kernel.

## Second exact Agda 2.9 verification round at 972219b398…

The user supplied a **new local exact-head receipt** at `972219b39894d28fed950f95fe0e2a2f050c68c6` using Agda 2.9.0 and `.venv`, accepting: `Karp21CompilerRepairGovernanceExact` (44/44), `Karp21FinDecoderIndexBidiExact` (148/148), `Karp21BinaryFinMaterializationCostExact` (143/143), `CookLevinCircuitGCTBoundary`, and `Karp21GammaBinaryRoundTripExact`. These are historical **positive receipts only for that head**; no success is inferred for subsequent edits.

The same local verification identified the following remaining failures. They have now been **patched in original source files** on PR #1445, with a fresh Agda 2.9 run still REQUIRED:

| Exact failure | Original-owner repair | Verification target |
| --- | --- | --- |
| Residual reserved constructors: 14 reported lines in `PNotEqualsNPCookIndexedRejectGuardCommutationExact.agda` and 2 lines in `PNotEqualsNPDirectSATLowerBoundExact.agda` | Replace all qualified `Cook.variable` and `SAT.variable` references in both files with `Cook.formulaVar`/`SAT.formulaVar`. Source token count was 15+2=17, while the user's 16 figure counts line coordinates; these are not contradictory. | Run `check_karp21_reserved_formula_constructors.py`, then compile affected P≠NP source owners. |
| `Karp21GammaSignedListRoundTripExact.agda:92` missing `sym` | Import `sym` from `Relation.Binary.PropositionalEquality` using the original source import list. | Compile `Karp21GammaSignedListRoundTripExact` and `Karp21GammaGoldenEverything`. |
| `Karp21CliqueVertexCoverExact.agda:65` missing `trans` | Import `sym; trans; cong` from `Relation.Binary.PropositionalEquality`, preserving the prior explicit with-equality transports. | Compile `Karp21CliqueVertexCoverExact` and `Karp21RawGraphValidatorObservationExact`. |
| `PNotEqualsNPCookFormulaPrefixCodecExact.agda:127` nonstructural recursion on `afterLeft` | Replace the original recursive parser body by `parseCookFormulaFuel`, strictly structural on a decreasing `Nat` fuel. The public parser uses `listLength tokens` fuel, not an oracle or unsafe termination pragma. | Compile the original `--safe` prefix codec and Cook Golden root. |
| Same codec around line 201: round-trip rewrite mismatch | Replace rewrite-based structural parser proof with `parseCookFormulaFuelEncodeInto`: an induction requiring `listLength (encodeCookFormulaInto formula suffix) ≤ fuel`. `encodeCookFormulaIntoSuffixLower` guarantees the right child fits the remaining fuel; `parseCookFormulaEncodeInto` specializes to the actual input length. All original exported theorem names remain intact. | Kernel-check suffix preservation, decoding, token-count properties and transitive Golden root. |

The repaired parser was also independently modelled in local Python against 1,400 generated formula/continuation pairs, including additional surplus-fuel checks. Those finite tests passed; they are not Agda kernel evidence.

The source-native `Karp21CompilerRepairGovernanceExact.agda` now also enumerates the five **second-round diagnostic categories** as `FollowupRepairIssue`/`reportedFollowupKinds`. It continues to prohibit promoting any source-stage status to proof authority without an actual new exact-head receipt. This formalism remains Golden Agda; the checked `dashi_lean4` AuthorityBoundary/Loom relation language is context, not an independent certification.

**Immediate acceptance cut:** update branch, run existing Python/preflight and `scripts/run_agda29_parallel_check.sh` under the user's existing Agda 2.9.0 environment; return the first exact failing filename/coordinate or the complete successful root receipts with new head. No Agda toolchain is present in this execution environment, so no newly updated kernel outcome is asserted.

## 2026-11-06 local Agda 2.9 follow-up: three compiler fronts


**Supplied local receipt:** at historical commit `cbf4302cc90d72dcc44ce3d27847954bf56a6654`, the user reports that `referee_karp21_maxcut.sh preflight` and `check_karp21_reserved_formula_constructors.py` pass, including the Cook/SAT constructor migration. This is a user-supplied preflight report, not an Agda kernel receipt for the subsequently edited head.

**Source repair 1 — Clique / cover:** `Karp21CliqueVertexCoverExact.agda` replaces the unnecessary `trans (cong negBool eqU) refl` and matching `eqV` expression with direct `cong negBool eqU` / `cong negBool eqV`. This preserves the source-owned `with ... in` equality witnesses and the same semantic graph carrier.

**Source repair 2 — signed gamma list:** `Karp21GammaSignedListRoundTripExact.agda` explicitly supplies `{ys = encodeSignedValuesPure rest}` to the original standard-library `ListP.length-++ (encodeSignedGammaPure value)` rewrite, avoiding an implicit function-valued rewrite target. No new encoding or parser is introduced.

**Source repair 3 — Cook prefix codec:** `PNotEqualsNPCookFormulaPrefixCodecExact.agda` on the current branch already contains a fuel-indexed `parseCookFormulaFuel` implementation with the public `parseCookFormula` wrapper and a strengthened encoded-roundtrip length-budget proof. This is source-written and must be independently checked with the pinned Agda 2.9.0 compiler; do not regard the old termination issue as kernel-resolved merely because the recursive calls now descend on fuel.

**Exact promotion checks:** `Karp21GammaGoldenEverything.agda`, `Karp21RawGraphValidatorObservationExact.agda`, and `Karp21CookGoldenEverything.agda` must be recompiled on the new exact Git head. A further compiler diagnostic becomes a new F-gap coordinate, not a pretext for a simulated acceptance receipt. The Lean mirror remains an independent comparison surface; the Agda source and Agda 2.9.0 receipts are Golden.
