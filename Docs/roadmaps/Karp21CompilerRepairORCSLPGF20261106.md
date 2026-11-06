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
