# YM / RH Pareto Coordination

Status: **live coordination sheet**. Not theorem authority, not source authority, not a Clay-completion claim.

Historical companions:

- `Docs/support/reference/YMRHPRRoundArchaeologyAudit.md` — broad PR/round card catalogue.
- `Docs/support/reference/YMRHFinalizationProducerAtlas.md` — alternate producer/construction atlas.
- `Docs/support/reference/YMCMPWorkStatus.md` — CMP109/116/119/122 completion/status boundary.
- `DASHI/Interop/CrossLaneProofArchaeologyLedgerExact.agda` — typed archaeology ledger.

This file is the **first-stop current-state sheet**. Update it whenever a Pareto pass changes a live primitive, demotes a route, closes a compiler seam, or discovers a better producer. Do not make future investigators reconstruct the current cut from chat history.

## Snapshot — 2026-09-15

Repository base used for this tranche:

```text
master = 20ddc053cc7d98be40cb60c9dafcdccf43bca695
branch = agent/ym-rh-pareto-form-flow-v1
```

Recent archaeology consolidation:

```text
PR #883 merged 2026-09-13
92 commits / 51 files
merge commit 7e7c493f196c82f884efa71a47ae455c5877d5b7
```

## 1. Current Pareto frontier

### YM — preferred BC1 source/representation route

Current preferred representation path:

```text
finite-history raw CMP119 objects
  -> concrete Sect.-2 predicate family
       ELocalizedAnalytic := exact same-E localization record
  -> genuine CMP122 Theorem-1 witness on that concrete family
  -> identity E-localization decoder                         [R248 compiler]
  -> active raw Sect.-2 witness                              [compiler]
  -> active regular-E/localization form                      [R248 compiler]
  -> active CMP109/CMP116 continuation                       [R247 compiler]
  -> canonical BC1 representation                            [R250/R115 compiler]
```

Round250 now exposes this preferred source-to-continuation compiler directly. On this route, the following are **not primitive theorem payments**:

```text
runningCoupling = finite-history coupling
decoder construction
active raw witness assembly
regular-E form projection
R247 continuation
common-radius construction after finite demand extraction
BC1 potential = same raw E_k
```

Current theorem-bearing inputs at the BC1 cut:

```text
YM-P0  genuine CMP122 Theorem-1 witness on the selected concrete predicate family
YM-P1  physical SecondVariationLinearity on the exact active E_k carrier
YM-P2  literal CMP109 Eq.(5.1) binding on that SAME continuation
YM-P3  literal finite normalized CMP116 demand extraction
```

Do not reopen whole CMP119/CMP122 theory. See `YMCMPWorkStatus.md`.

#### YM alternate/donor routes

```text
R249 reuse route:
  R244 function-valued localization carrier
  + same-E_k weld into finite-history raw carrier

legacy route:
  opaque ELocalizedAnalytic
  + explicit decoder
```

Both are legitimate donors. Neither should be counted in addition to the preferred concrete-predicate route.

### RH — current direct high route

Representation wall:

```text
RH-R1
nearResponseAt(chosen J)
  = finiteNearSum(cellResponse)
```

First genuinely high analytic family after R1:

```text
RH-R2
literalNear(J)
  + B_far(J)
  + D_Gamma(g_pole)
  < actual ClusterResponse(g_pole)
```

uniformly for every arbitrary high off-line nontrivial zero.

Current rules:

- `B_near = D_near` and `B_Gamma = D_Gamma` are normalization/reflexive choices, not extra analytic theorems.
- intermediate `M_cluster` is not a primitive target.
- determinant/G2d and old window/Schur lanes are donors/alternates unless same-object transport to the final universal pole-quotient carrier is explicit.
- checked Lean 8889 cluster status is not an Agda theorem payment without theorem-bearing same-carrier transport.
- repeated alias/history search for `nearSignedSum` / `nearOffFinset` is currently dominated: the theorem-bearing bytes are not present in the indexed Agda tree/history.

### Unification / common metric

Keep downstream of source-realized YM action/stress:

```text
source-generated YM action
  -> first variation
  -> T_YM
  -> Round131 native continuum/Schwinger/common-metric endpoint
  -> shared stress representation
  -> sector aggregation / Einstein variation
```

Do not use the unification lane backwards to define upstream CMP119 semantics or to block the shorter regular-E -> BC1 route.

## 2. Pareto ordering for next work

Current ordering as of this snapshot:

| Priority | Work | Why |
|---|---|---|
| 1 | YM-P1 / YM-P2 archaeology together | Eq.(5.1) depends on the physical D2 calculus on the SAME E_k; likely shared source/differential seam. |
| 2 | YM-P3 finite CMP116 demand extraction | Common radius is already compiler-owned once these source coordinates are paid; later R324 confirms extraction remains physical. |
| 3 | RH-R1 representation | High fanout and nonanalytic, but no hidden theorem-bearing Agda donor currently recoverable. |
| 4 | RH-R2 strict literal complement | Genuine hard analytic family after R1. |
| 5 | Unification transport | Important consistency/endgame work, but downstream of shorter YM Clay-facing source route. |

Recompute this table whenever a new donor or same-object weld is found. Do not preserve priorities by inertia.

## 3. Do-not-reopen list

Unless a current consumer proves otherwise, do not spend cycles on:

- generic CMP109/116/119/122 re-formalization;
- running-coupling identity already definitional on the finite history;
- abstract regular-term evaluation after `RegularTerm = Background -> Real`;
- R246/R247 active continuation plumbing;
- BC1 same-regular-E identity;
- common-radius existence after finite normalized demands are supplied;
- old all-Nat source histories;
- RH determinant taper as if definitionally equal to final `g_pole`;
- generic RH local zero counts that erase target-centred phase;
- re-searching inaccessible 8883/8889 Lean filenames unless new source bytes/path appear;
- unification as an upstream definition of YM source semantics.

## 4. Source / attribution coordinates

Keep identifiers separate from proof payment.

### Yang--Mills / Bałaban source family

- CMP109 — DOI `10.1007/BF01215223`
- CMP116 — DOI `10.1007/BF01239022`
- CMP119 — DOI `10.1007/BF01217741`
- CMP122 I — DOI `10.1007/BF01257412`
- CMP122 II — DOI `10.1007/BF01238433`
- Yang--Mills theory QID `Q1192873` — identity/navigation only
- Bałaban person QID — unresolved here
- paper-specific Dewey — unresolved here; do not guess
- OEIS — not applicable

### RH

- Riemann hypothesis QID `Q205966`
- Riemann zeta function QID `Q187235`
- Bernhard Riemann QID `Q42299`
- zeta-function Dewey coordinate `515.56`

These are discovery/classification coordinates only.

## 5. Validation boundary

No `ProofLevel = machineChecked` label created by a source edit is a fresh kernel receipt by itself.

For every active branch/tranche record separately:

```text
source written?
focused validation root updated?
exact-head workflow observed?
Agda/kernel receipt observed?
cross-prover theorem transported?
```

Do not merge those statuses.

## 6. Update log

### 2026-09-15 — R248/R250 Pareto recut

- R248 found to already own the exact raw active E-localization decoder architecture.
- preferred concrete Sect.-2 predicate makes E-localization decoding identity.
- R249 retained as alternate R244-reuse route using one honest same-E_k weld and no history coercion.
- R250 now exposes direct composition from concrete predicate + genuine CMP122 theorem witness to the BC1-facing active continuation.
- decoder/rawWitness demoted from primitive inputs on the preferred route.
- current BC1 theorem inputs normalized to CMP122 source witness + D2 + Eq.(5.1) + finite CMP116 demands.
- RH unchanged: R1 remains representation wall; R2 remains first high analytic family.

When the next Pareto pass changes any of these statements, update this file in the same tranche as the code change.
