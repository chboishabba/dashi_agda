# Yang–Mills / Riemann Hypothesis PR–Round Archaeology Audit

Status: repository archaeology reference, not theorem authority.

Canonical companion owner: `DASHI/Interop/CrossLaneProofArchaeologyLedgerExact.agda`.

Primary maintenance PR: https://github.com/chboishabba/dashi_agda/pull/883

This document exists to stop repeated rediscovery of the same PR/round history. It records the Yang–Mills and Riemann-hypothesis proof-search spine by **PR title**, **round clock**, **role**, **supersession**, and **current relevance**. It is a navigation/audit object only. PR titles, citations, source metadata, QIDs, Dewey numbers, Lean-return statuses, and historical compiler flags do not manufacture proof payment.

## 1. Read this first: there are several different clocks

Do not treat these as interchangeable.

1. **GitHub PR number** — repository integration chronology, e.g. `#846`.
2. **PR-title round** — phrases such as “submission round ten”, “highest-alpha Round 24”, or “YM Round58”. These are programme labels in that PR lineage.
3. **Internal Agda module round** — names such as `Round214`, `Round246`, `R259`. These are module-local proof-search rounds and frequently occur long after PR-title rounds with the same numeral family.
4. **G-lane labels** — e.g. `G20`, `G21`; these are RH subprogramme labels, not PR or Agda rounds.
5. **Lean return/build labels** — e.g. `8883`, `8885`, `8889`, `8894`; these identify external/cross-prover sessions or returns, not Agda rounds.
6. **Dated commit archaeology** — first source appearance / route correction / consolidation. This is the closest analogue to the NS worker’s forensic timeline.

The most common source of repeated search has been confusing one clock with another.

## 2. Status vocabulary

- **CURRENT** — on the current preferred proof-search path.
- **ACTIVE DONOR** — useful theorem/representation source, but not itself the current consumer.
- **SUPERSEDED AS ROUTE** — still historically/theoremically useful, but a later route removed it as a prerequisite.
- **CORRECTED** — later PR/module fixed a semantic, carrier, sign, scope, or circularity defect.
- **SUPPORT / DIAGNOSTIC** — useful comparison, source atlas, performance, validation, or cross-pollination work; not a new primitive Clay payment.
- **VALIDATION ONLY** — checker/CI/probe PR; do not interpret as new mathematics.
- **INTERNAL ROUND / NO STANDALONE PR LOCATED** — the round is visible in successor bodies/modules but this audit did not find an honest standalone PR-title mapping.

## 3. Current start points — do not begin from the historical tables

### 3.1 Yang–Mills current Clay-facing source route

Current consumer-minimal route:

```text
finite beta history
  -> active density family
  -> CMP122 Theorem 1 source witness
  -> active CMP119 regular-E Section-2 form
       E_k : Background -> Real
       + literal localized (2.25)-(2.27) composite-sum representation
  -> CMP109/CMP116 continuation
  -> BC1
```

Current branch owners:

- `BalabanCMP119RegularESection2PredicateRound246Exact.agda`
- `BalabanTheorem1RegularEContinuationRound247Exact.agda`
- `BalabanCMP119RegularEActiveRound247Validation.agda`

The branch additionally has the least-privilege **form-only witness**: quantitative Section-2 bounds are no longer primitive inputs merely to reach BC1.

The surviving source-facing payment is therefore the exact active `CMP119RegularESection2Form` on the beta-driven density family. Whole `A_k` semantics remains important for generated-action / first-variation / stress / unification provenance, but is **not** a prerequisite of the shorter BC1 route.

### 3.2 Yang–Mills current mass-gap consumer

PR #869 / internal R270–R275 is the conceptual correction to keep in mind:

```text
same reconstructed continuum family
  -> quantitative clustering upper
  -> positive rate/gap identification
  -> physical spectral gap
```

Row-C Heat/Doob/Langevin, unified polymer norms, and source-native multiscale cluster-expansion routes are producer tactics, not mandatory architecture.

### 3.3 RH current route

Current direct high route:

```text
R1 representation:
  nearResponseAt(chosen J) = finiteNearSum(cellResponse)

then R2 analytic family:
  literalNear(J) + B_far(J) + D_Gamma(g_pole)
    < actual ClusterResponse(g_pole)

uniformly for every arbitrary high off-line nontrivial zero.
```

Important current reductions:

- `B_near = D_near` and `B_Gamma = D_Gamma` are source-order reflexive choices, not primitive analytic theorems.
- intermediate `M_cluster` was removed; the target is actual `ClusterResponse`.
- the final balance `ClusterResponse = Off + Gamma` is downstream and must not be available to the independent R2 proof.
- R0 concrete numeric/certificate scalar realization is optional execution debt, not a prerequisite of a direct analytic R2 proof.
- the 8889 quantitative cluster result is only an optional donor unless theorem-bearing same-object transport is recovered.

## 4. Yang–Mills PR chronology — foundational and pre-round spine

These PRs establish the major pre-“round-number” machinery. They remain useful for provenance and donor lookup but should not be mistaken for the current proof cut.

| PR | Title | Role / what to remember |
|---|---|---|
| #6 | `feat(ym): generate source-aware critical-path theory atlas` | SUPPORT: early source/status atlas. |
| #8 | `feat(ym): add literal Balaban lattice operator realization` | Foundational literal Bałaban operator donor. |
| #9 | `feat(ym): construct a concrete SU(2) quaternion carrier` | Concrete SU(2) carrier. |
| #10 | `feat(ym): realize the concrete SU(2) adjoint operator lane` | Adjoint/operator realization. |
| #49 | `feat(ym): package uniform SU(2) radial inverse families` | Early uniform inverse/chart donor. |
| #92 | `Integrate finite Bałaban one-step SU(2) RG frontier` | Finite one-step RG consolidation. |
| #125 | `Extract generic Schur coercivity and join NS/YM` | ACTIVE DONOR: cross-domain Schur/coercivity. |
| #143 | `Formalise generic compact Lie group theory for Yang–Mills` | Compact-Lie abstraction. |
| #146 | `Close compact Lie exact stack and formalise Yang–Mills frontier` | Compact-Lie consolidation. |
| #151 | `Instantiate SU(N) matrices and constructive Yang–Mills closure stack` | SU(N) constructive stack. |
| #153 | `Land concrete SU(N) and constructive Yang–Mills analytic stack` | Concrete SU(N) analytic integration. |
| #191 | `Cross-pollinate shift geometry, Lorentz uniqueness, constraints, and YM frontier` | SUPPORT / cross-pollination. |
| #248 | `Formalize uniform Yang–Mills contraction through continuum gap survival` | Historical contraction/gap route. |
| #260 | `feat(ym): add compact-simple group-parametric coverage` | Compact-simple parameterization. |
| #262 | `Refine all-scale RG invariant-domain obligations` | Historical all-scale RG route. |
| #264 | `Formalize infinite-volume continuum limits C1-C9` | Historical continuum-limit packaging. |
| #269 | `Derive dominant-free background closure bridges` | Background closure compiler. |
| #288 | `Add infinite-volume and continuum OS bridge` | Continuum/OS bridge. |
| #291 | `Formalize explicit Step V and all-scale invariant chains` | Step-V/all-scale chain. |
| #303 | `Add exact continuum OS and physical mass-gap cutset` | Historical mass-gap cutset. |
| #304 | `Complete finite-background critical-map and one-step RG cutset` | Finite critical-map/RG. |
| #305 | `Add proof-relevant all-scale and thermodynamic cutset` | Historical all-scale thermodynamic cut. |
| #306 | `Implement complete Yang-Mills analytic inhabitation cutset` | Broad historical inhabitation interface; not current proof payment. |
| #307 | `Add published-analytic authority boundary and proof-branch CI` | SUPPORT / authority + CI boundary. |
| #309 | `Add source-faithful Bałaban matching and finite Fourier Hodge reduction` | Source-faithful/Hodge donor. |
| #313 | `Add periodic four-torus and finite Fourier Hodge foundation` | Periodic/Hodge foundation. |
| #315 | `Close periodic physical fibres, exact finite reductions and terminal-scale assembly` | Periodic finite assembly. |
| #328 | `Add trusted clean Agda CI for the YM coercivity cone` | VALIDATION ONLY. |
| #329 | `Close side-four bond coercivity and repair the SU2 chart-radius lane` | Coercivity + chart repair. |
| #334 | `Close configured-side C1 identification and radial chart interfaces` | C1/chart identity. |
| #335 | `Prove exact SU(2) Wilson plaquette second-order jet` | Wilson-jet theorem donor. |
| #339 | `Close side-four averages and instantiate the C2 coarse propagator frontier` | C2/coarse propagator. |
| #342 | `Expose and advance the P1–P5 Clay Yang–Mills frontier` | P1–P5 frontier. |
| #343 | `Close the configured Green inverse and advance the literal Clay frontier` | Green inverse/literal frontier. |
| #344 | `Construct T1–T5 Yang–Mills frontier reductions and physical transport` | T1–T5 reduction spine. |
| #346 | `Internalize literal Yang–Mills frontier producer cutset` | Producer cutset formalization. |
| #348 | `Integrate Bishop and DASHI constructive-real backends with literal Yang–Mills frontier` | Bishop/real backend donor. |
| #349 | `Merge literal Yang–Mills frontier into Bishop integration branch` | Integration-only merge tranche. |
| #350 | `Sync current master into Bishop integration branch` | Sync-only. |

## 5. YM submission-round sequence

The “submission round” clock predates the later “highest-alpha round” clock.

| PR | Round | Title / role |
|---|---:|---|
| #353 | Gate-4 round six + submission rounds 7–9 | `Advance Gate 4 through physical involutions, Bishop parity, P06/P11, Step-V and SI` — aggregate multi-round integration. |
| #357 | 8 | `Validate Yang-Mills submission round eight` — VALIDATION ONLY. |
| #358 | 8 | second validation pass — VALIDATION ONLY. |
| #359 | 8 | third validation pass — VALIDATION ONLY. |
| #360 | 8 | fourth validation pass — VALIDATION ONLY. |
| #361 | 9 | `Validate Yang-Mills submission round nine` — VALIDATION ONLY. |
| #362 | 9 | `Validate latest Yang-Mills submission round nine` — VALIDATION ONLY. |
| #365 | 10 | `Discharge Bishop factorial/parity/interlacing and finite Step-V sums; isolate lightweight P06` — substantive Round10. |
| #366 | 10 | `Validate Yang-Mills submission round ten` — VALIDATION ONLY. |
| #367 | 11 | `Add direct-ratio Step-V reducer, audit P06 diameter claims, and order P33 before Gate 4` — Round11 tranche. |
| #369 | 11 | `Complete Round-11 full-ball, P11, and fixed-lattice-to-continuum dependency spines` — continuation. |
| #370 | 11 | `Advance Yang-Mills Round 11: direct-ratio, P06/P11 audit, Gate-4 ordering, and OS spine` — master-facing Round11 integration. |

## 6. YM highest-alpha PR-title rounds

This is the round sequence most likely to be confused with later internal module rounds.

| PR | Title round | Title / status |
|---|---:|---|
| #377 | 14 | `Advance the Clay path with inverse-dexp bounds, Wilson budgets, and continuum-limit reuse`. |
| #378 | 15 | `Audit physical-unit mass-gap transport and close new P33 algebra`. |
| #380 | 16 | `Close inverse-dexp positivity and advance the local SU2 chart engine`. |
| #381 | 17 | `Close the actual endpoint modulus and coupled RG factor audits`. |
| #386 | 18 | `Close the literal quaternion chord lane and calibrate the physical residual`. |
| #391 | 19 | `Replace the collar residual lane with exact Combes–Thomas conjugation`. |
| #393 | 20 | `Close the finite Schur and physical Combes–Thomas endgame`. |
| #394 | 21 | `Cancel exact gauge and constraint jets from the physical Hessian remainder` — later CORRECTED by Round22. |
| #396 | 22 | `Repair the physical Hodge split and construct the rational Wilson sixteen-atom Hessian` — important correction to Round21. |
| #402 | 23 | `Block bare volume-uniform coercivity and formalize terminal-scale gap pullback` — early/diverged Round23 stack. |
| #403 | 23 | same programme on clean branch — definitive Round23 integration. |
| #409 | 24 | `Reduce physical Wilson atoms and prove the signed gauge defect modulo the literal link radius`. |
| #416 | 25 | `Cross-pollinate Yang–Mills RG with projection leakage and reduced modes` — Round25 cross-pollination / donor rather than new primitive route. |
| #421 | 26 | `Separate physical gap scaling from RG compatibility and quantify uniform Schur inputs`. |
| #427 | ~27 support | `Cross-pollinate YM gap scaling with harmonic and wreath refinement` — SUPPORT/DONOR around Round27. |
| #430 | 27 | `Close signed Wilson incidence, same-h terminal coercivity, and exact RG tails` — main Round27. |
| #432 | 27 | `Validation probe: round 27 signed Wilson and terminal Hessian` — VALIDATION ONLY. |
| #435 | 28 | `Separate observable and spectral uniformity and formalize RG good-class preservation` — later superseded/integrated by Round29. |
| #439 | 29 | `Unify YM highest-alpha head and isolate correlated W-local cancellation` — cumulative correction/integration of Round28 ancestry. |
| #440 | 30 | `Add strong-coupling functional-inequality route and exact SU(2) margin arithmetic`. |
| #443 | 30 support | Hurwitz/Hopf cross-pollination — SUPPORT/DONOR. |
| #444 | 31 | `Reconcile SO/SU curvature rates, weighted Wasserstein contraction, and all-beta scaling`. |
| #458 | 32 | `State the literal Clay YM contract and derive the Hessian coefficient from sixteen atoms`. |
| #461 | 33 | `Formalize Yang-Mills claim papers, all-group promotion guards, and gap scaling`. |
| #462 | 34 | `Derive the physical selected-background radius and construct W-local`. |
| #466 | 35 | `Derive the plaquette curl and isolate the sharp Wilson deep remainder`. |
| #470 | 36 | `Close the finite Wilson pair/deep channels and expose the exact variation selector`. |
| #473 | 37 | `Construct the finite selected-variation repair and spillover ledger`. |
| #476 | 37 continuation | `Construct the physical projector and split the selected-variation spillover`. |
| — | 38 | **INTERNAL ROUND / NO STANDALONE PR LOCATED**. Round39 explicitly says it continues from Round38. |
| #486 | 39 | `Construct the redundancy-safe KKT projector and local constrained Green algebra`. |
| #487/#488 | 39 | temporary checker/probe PRs — VALIDATION ONLY. |
| #489 | 40 | `Localize the KKT multiplier and close the correlated singleton reducer`. |
| #491 | 40 | temporary checker — VALIDATION ONLY. |
| #496 | 41 | `Build the physical Yang–Mills constraint producer and SZZ decision tranche`. |
| #497 | 41-certified fork | `Certify the single-plaquette owner envelope with exact budget slack` — body says certified-enclosure fork after Round40; historical branch metadata labels it Round41. |
| — | 42 | Internal round exists in the subsequent Gate-I lineage; no trustworthy standalone PR-title mapping fixed by this audit. |
| — | 43 | INTERNAL ROUND / NO STANDALONE PR LOCATED. |
| #522 | 44 | `YM round44: type beta coefficient and attempt termwise positivity`. |
| — | 45 | INTERNAL ROUND / no standalone PR title located. |
| #540 | 46 | `YM Round46: weld metric-stress identities and close invariant-theory G2`. |
| #542 | 47 | `YM Gate I: tighten physical producer seams` — body identifies Round47. |
| #543 | post-47 source-faithful | `YM Gate I + source-faithful complete-density RG reuse`. |
| #547 | 52 | `YM Round52: source-native physical leaf reductions`. |
| #554 | 54 | `YM Round54: derive Federbush cancellation and finite physical producer spine`. |
| #564 | 56 | `YM Round56: normalized pi momentum bridge + five-channel quartic beta adapter`. |
| #566 | 57 | `YM Round57: four-orbit beta, Bishop interval semantics, grouped G2 and source-native RG`. |
| #574 | 57 parallel | `YM Round57: hyperoctahedral orbit reduction + Walsh cancellation` — symmetry-first parallel tranche. |
| #568 | 58 | `YM Round58: canonical G2, compact-group one-loop, and published 4D UV boundary`. |
| #571 | 59 | `YM Round59: positive RG geometry, Cheeger gap, and two-metric cutoff gate`. |
| #575 | 60 | `YM Round60: Walsh cancellation before Bishop intervals and G2 symmetry falsifier`. |
| #578 | 60 parallel | `YM Round60: literal G2 support, charge-relative Green closure, FP ghost and Wilson transfer positivity`. |
| #583 | 61–87 aggregate | `YM Round61–87: literal Clay four-family frontier; marked stress fields and beta trig reduction` — aggregate PR spanning many internal rounds; do not infer one PR per round. |
| #644 | 112 | `YM Round112: pay A2 marginal sensitivity with mixed-Cauchy cubic telescope`. |

The gaps above are deliberate. They mean “no standalone PR title located in this audit”, not “round did not exist”.

## 7. YM late source/operator/path13 PR spine

These PRs are more useful for current work than many earlier title rounds.

| PR | Title | Current interpretation |
|---|---|---|
| #789 | `YM: split Path13 uniform calculus source payment` | Path13/CMP98 Eq.(119) source minimization. |
| #790 | `YM: minimize Path13 Eq119 semantic calculus payments` | Further least-privilege source cut. |
| #792 | `YM: correct Path13 Eq119 printed dexp/J roles` | CORRECTED source-sign/operator roles. |
| #793 | `YM: x-pollinate T3 right Jacobian into corrected Eq119 roles` | T3 compatibility donor. |
| #795 | `YM: minimize T3 Eq119 scalar source boundary` | Removes over-strong scalar prerequisites. |
| #796 | `YM: split Path13 physical data from standard operator representation` | Separates physical/source from standard representation. |
| #797 | `YM: add current preferred Path13 Eq119 source frontier` | Canonical Eq119 frontier at that time. |
| #799 | `YM: make mass-gap route consume current Eq119 frontier` | Mass-gap route integration. |
| #800 | `YM: synchronize spectral statement with current Eq119 frontier` | Spectral statement alignment. |
| #801 | `YM: specialize Bałaban variational theorem directly to Path13` | Removes same-object receipts by construction. |
| #803 | `YM: align Path13 selected defect with R171 and minimize printed semantics` | Further source minimization. |
| #804 | `YM: replace 1/24 cut with exact 74-link Eq119 budget` | Exact threshold correction. |
| #806 | `YM: reduce M7 domain/self-adjointness through Kato closed forms` | Operator/domain donor; physical closed form still open. |
| #809 | `YM: minimize T5 physical continuum OS-gap source cut` | Continuum/OS/gap least-privilege input. |
| #811 | `YM: construct finite projected P33 Hamiltonian domain and floor` | Finite M7 precursor only. |
| #821 | `YM: isolate literal CMP119 raw-source family as first preferred source wall` | Internal R212–217. Historical first-source wall; later compressed for BC1. |
| #846 | `YM: recut preferred source frontier to regular-E and marked-history seams` | Internal R218–228. SUPERSEDES whole raw-family-first ordering for BC1. |
| #849 | `YM Path13: fibre-native aggregation and OOM profiling follow-up` | SUPPORT / elaboration-resource route, not new physical theorem. |
| #857 | `YM Row C: minimize Heat/Doob debt to real majorants and one weighted generator row` | Internal R251–259; Row-C tactic minimization. |
| #867 | `YM Row C: split Langevin commutator from symmetric Hessian row weld` | CLOSED / SUPERSEDED by #869. |
| #869 | `YM: normalize mass-gap search to quantitative clustering consumer` | **CURRENT conceptual mass-gap correction**; internal R270–275. Row-C becomes optional producer tactic. |
| #883 | `Collate NS/YM/RH/GRQ proof archaeology into one canonical ledger` | CURRENT archaeology/integration branch. |

### Important naming collision

`CMP98 Eq.(119)` / “Eq119” in the Path13 series is **not** “CMP119” the 1988 Bałaban journal-volume paper. They are unrelated numerals and have repeatedly produced misleading search hits.

## 8. YM internal module-round crosswalk most relevant to current archaeology

These are **not** PR-title rounds.

| Internal round | Meaning / route |
|---:|---|
| R58 | Source-native raw-state ancestry / published finite-cutoff UV-stability lane. |
| R61–87 | Large four-family aggregation represented by #583. |
| R103 | Physical finite effective-action/Hessian A1/A2/BC1/BC2 leaf family. |
| R108 | CombinedRG/source semantics and same-density continuation family. |
| R112 | A2 marginal sensitivity; #644 title round112. |
| R131 | Same-family finite/continuum/Schwinger/common-metric stress endpoint. |
| R132/133 | Generated-action + first-variation/stress weld. |
| R145 | Detects post-hoc density/action semantics circularity; forces source semantics before BC1. |
| R191–211 | Current terminal-cutset iteration sequence before source recut. |
| R212 | Compatibility source-realization route. |
| R214 | Source-fixed `rho_k -> A_k`; important for generated-action/unification provenance. |
| R215 | Route reversal: shortest BC1 path consumes literal regular `E_k`, not whole `A_k`. |
| R216/217 | Raw source realization split / raw-state frontier. Historical broad source wall. |
| R218 | Published source flow. |
| R219 | Beta-driven residual/complete-density family. |
| R221 | Selected regular-E source projection. |
| R225 | Preferred regular-E source route; full residual family demoted to stronger alternative. |
| R234/235 | Source-fixed regular-E semantics / localization-radius split. |
| R236 | Preferred source frontier recomputation. |
| R237 | Selected-scale semantics; total arbitrary-density interpreter no longer required. |
| R240 | Priority router; regular-E projection, common radius, and D2 calculus separated. |
| R241 | Regular-E projection compiler from source-native flow. |
| R242 | `RegularTerm = Background -> Real` at source construction. |
| R243 | Extraction + pointwise evaluation become compiler output. |
| R244 | CMP119 localization source theorem separated from carrier realization. |
| R245 | Function-valued E + localization -> CMP109/116 continuation. |
| R246 | Consumer-indexed Section-2 form, finite `ActiveScale`; current branch adds form-only witness. |
| R247 | Active continuation into CMP109/116; current branch has focused validation. |
| R251–259 | Least-privilege Row-C Heat/Doob/Hessian/generator-row tranche. |
| R260 | Anchored Hessian majorant correction. |
| R270–275 | Canonical mass-gap/B-facing clustering consumer; producer tactics demoted. |

### Dated source-frontier corrections worth remembering

- R131: `258e977a...`, 2026-08-30 03:19 Brisbane — common-metric finite/continuum/Schwinger/stress endpoint.
- R132/133: `10d00f01...`, `281f2b7a...`, 30 Aug 20:56 Brisbane — generated action / first variation.
- R145: `b8e2add4...`, 31 Aug 19:43 Brisbane — circular/post-hoc semantics correction.
- R214: 8 Sep 07:35–07:37 Brisbane — whole-action semantics moved to source boundary.
- R215: 8 Sep 07:39–07:41 Brisbane — BC1 regular-E route reversal.
- R242: `0712caaa...`, 9 Sep 21:47 Brisbane — function-valued regular E.
- R243: `c7c65b17...`, 9 Sep 21:47:59 Brisbane — extraction/evaluation compiler.
- R244: `8f1b0d3b...` / `9f55e85d...`, 21:50:39 / 21:51:26 Brisbane — localization authority/carrier split.
- R246: `c3a184b8...`, 21:54:33 Brisbane — consumer-indexed active Section-2 predicate.

## 9. YM supersession map

Use this before reviving an older route.

```text
Round21 (#394)
  -> corrected Round22 (#396)

early/diverged Round23 (#402)
  -> clean Round23 (#403)

Round28 (#435)
  -> integrated/corrected by Round29 (#439)

R217 / #821 broad raw-family-first source wall
  -> R218–228 / #846 regular-E preferred source cut
  -> R242–247 current function-valued active regular-E/localization cut

Row-C tactic R251–260 / #857
  -> canonical clustering consumer R270–275 / #869
     (Row C remains an optional sufficient producer)

#867
  -> explicitly superseded by #869
```

## 10. RH PR chronology — substantive proof-search spine

| PR | Clock / label | Title / role |
|---|---|---|
| #100 | foundational | `Formalise Riemann zeta and the DASHI–Weil RH proof route` — initial zeta/explicit-formula/Weil architecture. HISTORICAL SUBSTRATE. |
| #121 | foundational | `Extend zeta with von Mangoldt exhaustion and Weil-square coercivity`. |
| #128 | support | `Formalise prime counting, Chebyshev functions, and Riemann transforms` — background donor. |
| #449 | support | `Add substantive RH, Hodge, BSD, P-v-NP, Poincare, and graded-VOA tranches` — Xi/reflection and broad cross-math support. |
| #604 | early top-down | `Formalize zeta Hermitian defect, finite retention, interference and detectability route` — historical G1–G4 style route. |
| #622 | G21 | `G21: pole-quotiented two-channel exterior explicit-formula desk test` — exterior explicit-formula desk test. |
| #630 | Lean 8883 | `Aristotle RH bidi: explicit cutoff tail and finite post-Schur near core` — checked every-J near/far, far shell, finite near carrier, cutoff transport; Agda proof transport not supplied. |
| #642 | Lean 8885 | `RH bidi cut: checked scalarization plus balance no-go frontier` — determinant scalarization + balance no-go; diagnostic route. |
| #646 | post-8885 | `RH bidi: pole-quotient complement margin after balance no-go` — universal pole quotient promoted as final carrier; channels separated. |
| #676 | support | `Math 2026: source-exact Dujella/DBN BIDI cross-pollination with RH/NS/YM` — donor/attribution support. |
| #677 | Lean 8889 | `RH: bidi-aware experimental proof search and 8889 feedback` — quantitative cluster/Gamma feedback; now OPTIONAL DONOR only unless theorem-bearing transport recovered. |
| #686 | Lean 8894 | `RH BIDI: 8894 gap-split no-go and adaptive clustering reconciliation` — gap-split no-go/adaptive clustering; target-modulation/source recovery. |
| #691 | source compression | `RH: H_A consumer-quotient active recovery cross-pollination` — collapses H_A to dependent source producer. |
| #721 | same-object weld | `BIDI-weld ζ density, literal target-gap moment, and direct finite producer into the live RH cut`. |
| #751 | terminal recut | `Reconcile merged RH diagnostics with final pole-quotient cut` — one crossing J, signed near + far, same-taper Gamma. |
| #774 | analytic cores | `Reconcile post-751 RH final carrier and Gamma proof routes` — Off/Gamma analytic-core recut. |
| #813 | terminal compiler | `Fix and wire direct RH terminal compiler` — CLOSED / explicitly superseded by #818. |
| #818 | analytic-core prize path | `RH: unify current terminal compiler with analytic-core prize path` — historical payment APIs factor through minimal analytic-core route. |
| #824 | one-leaf direct route | `RH: direct one-leaf pole-quotient cut with proof-gap introspection` — key route correction; isolates final-near representation + one high analytic family. At this point still used intermediate `M_cluster`. |
| #847 | actual ClusterResponse | `RH: reduce high leaf to balance-free actual ClusterResponse` — **CURRENT conceptual correction**; removes `M_cluster`, enforces balance-free analytic context. |
| #855 | generic high + certificates | `RH: generic high contradiction and certified final-near follow-up` — generic high consumer; R0/R1/R2/R3 decomposition; optional 8889 lower-envelope donor. |
| #865 | fold-local certificate | `RH: fold-local concrete certificate bridge and R3 min-cut` — concrete certificate scalar may differ from final analytic scalar. |
| #868 | cellwise upper route | `RH: reduce certified near route to cellwise integral uppers` — optional sufficient numerical producer; one-sided cell bounds enough. |
| #883 | current archaeology | `Collate NS/YM/RH/GRQ proof archaeology into one canonical ledger`. |

## 11. RH clock crosswalk

### G-lane

- `G21` is explicitly represented by PR #622.
- A `G20` predecessor exists in the historical architecture, but this audit did not locate a safe standalone PR-title mapping. Do not guess one.

### Lean / Aristotle returns

| Return | PR | What it owns / does not own |
|---:|---|---|
| 8883 | #630 | Checked Lean every-cutoff near/far split, explicit far-shell modulus, finite near carrier, `D_off` cutoff transport. **Does not equal Agda proof transport.** |
| 8885 | #642 | Determinant scalarization and balance no-go. Useful diagnostic; determinant carrier is not automatically the final universal pole quotient. |
| 8889 | #677 | Quantitative cluster/Gamma feedback. Optional lower-envelope donor only after theorem-bearing same-carrier transport; status Boolean is not payment. |
| 8894 | #686 | Gap-split no-go/adaptive clustering reconciliation and source recovery. |

### Current direct-route internal chronology

- 2026-09-08 05:20 Brisbane, `629700b2...`: `B_near = D_near`, `B_Gamma = D_Gamma`; separate channel-envelope theorems pruned.
- 2026-09-09 16:17 Brisbane, `b1eeccee...`: bypass intermediate `M_cluster`; target actual `ClusterResponse`.
- 2026-09-09 19:11 Brisbane, `751cd262...`: separate least terminal consumer from preferred phase-visible acquisition theorem.
- 2026-09-09 22:07 Brisbane, `a25681a6...`: final near kernel evaluator-independent; one representation equality remains.
- 2026-09-09 23:51 Brisbane, `4d48fbc7...`: current direct frontier = one representation seam + one primitive uniform high scalar family.

### R0/R1/R2/R3 terminology

- **R0** — optional concrete numeric/certificate scalar realization of the final carrier.
- **R1** — exact same-object final-near representation:
  `nearResponseAt(J) = finiteNearSum(cellResponse)`.
- **R2** — independent high analytic theorem against actual `ClusterResponse`.
- **R3** — actual-zeta critical coordinate / verified-low-region / high-low terminal carrier obligations.

These are RH route labels, not YM internal rounds.

## 12. RH supersession map

```text
historical broad Weil/window/global explicit-formula routes
  -> useful donors, not mandatory current architecture

8885 determinant scalarization
  -> diagnostic/scalarization donor
  -> NOT final universal pole-quotient carrier

#751 allowance/payment API
  -> compressed by #774/#818 analytic cores

#813
  -> explicitly superseded by #818

#824 direct one-leaf route with M_cluster
  -> #847 removes M_cluster
  -> direct target is actual ClusterResponse

#855 certificate route
  -> optional sufficient producer
  -> direct R2 theorem remains admissible and shorter if found

8889 checked quantitative cluster status
  -> optional donor only after theorem-bearing same-object transport
```

## 13. Stop rules — do not search/reprove these from scratch unless a current route actually fails

### YM

Do not restart:

- generic CMP122 RG-stability theorem reconstruction merely because the local witness socket is conditional;
- running-coupling identity over the finite beta history;
- regular-E extraction or pointwise evaluation once using the R242 function-valued carrier;
- CMP109/116 continuation compiler after the R246/R247 form witness;
- BC1 same-object compiler from the literal regular-E continuation;
- whole `A_k` semantics as a prerequisite of BC1;
- Row-C stochastic/Heat/Doob/Langevin tactic architecture as if mandatory for the canonical mass-gap consumer;
- generic geometric summation / Dyson plumbing already compiler-owned;
- Path13 `CMP98 Eq.(119)` when searching for `CMP119` regular-E source semantics.

Do not infer:

- finite-cutoff UV stability => continuum YM/OS/mass gap;
- source DOI/QID => proof term;
- whole-action semantics from downstream BC1 identity;
- Round131/133 stress/action consistency backwards into upstream source semantics.

### RH

Do not restart as primitive prerequisites:

- absolute `W(t)` majorant route;
- selected Weil-window machinery merely because it is mathematically available;
- determinant-q scalarization;
- intermediate `M_cluster`;
- separate `B_near` and `B_Gamma` analytic envelope theorems;
- far-shell theorem from scratch while the 8883 checked return is the source/status donor;
- generic target translation/modulation/cosine mathematics;
- reflection pairing/odd-channel cancellation as a fresh theorem unless same-object attachment genuinely fails;
- certificate infrastructure as though it proves RH.

Do not infer:

- one fixed-zero certificate => uniform high theorem;
- Lean status => Agda theorem;
- cluster balance => independent R2 inequality;
- certificate scalar identity => final analytic scalar type equality.

## 14. Attribution / identifier coordinates

These are navigation and source-identity coordinates only.

### YM

- Bałaban CMP109: DOI `10.1007/BF01215223`
- Bałaban CMP116: DOI `10.1007/BF01239022`
- Bałaban CMP119: DOI `10.1007/BF01217741`
- Bałaban CMP122-I: DOI `10.1007/BF01257412`
- Bałaban CMP122-II: DOI `10.1007/BF01238433`
- Yang–Mills theory: Wikidata `Q1192873`
- Tadeusz Bałaban person QID: unresolved in the authoritative repo atlas; do not guess.
- Exact paper-specific Dewey: unresolved; do not substitute MSC for Dewey.
- OEIS: not applicable to these source papers.

### RH

- Riemann hypothesis: Wikidata `Q205966`
- Riemann zeta function: Wikidata `Q187235`
- Bernhard Riemann: Wikidata `Q42299`
- Dewey coordinate recorded for the Riemann zeta function: `515.56`
- Riemann 1859 memoir: no DOI assigned in the current source atlas.

## 15. Fast lookup by question

If the question is…

- **“Where did YM source semantics become source-fixed?”** -> R145, R214.
- **“When did BC1 stop requiring the whole action?”** -> R215, then R242–247.
- **“Where is the current active regular-E source path?”** -> R246/R247 on PR #883 branch; historical recut in #846.
- **“Where did Row C become optional rather than canonical?”** -> #869 / R270–275.
- **“Where is the current Eq119 operator route?”** -> #789–#804; remember CMP98 Eq.(119) != CMP119.
- **“Where is YM domain/self-adjointness?”** -> #806 plus operator/continuum frontier owners.
- **“Where is YM continuum/OS least-privilege cut?”** -> #809 and later T5 owners.
- **“Where did RH get the finite near/far checked source?”** -> #630 / 8883.
- **“Where did determinant scalarization get demoted?”** -> #642 then #646/#824.
- **“Where was M_cluster removed?”** -> #847.
- **“Where are R0/R1/R2/R3?”** -> #855, refined by #865/#868.
- **“What is the current RH first wall?”** -> R1 final-near literal finite representation; then R2 actual-ClusterResponse strict theorem.
- **“Can we use 8889?”** -> only as optional donor with theorem-bearing same-carrier transport; see #855 optional lower-envelope adapter.

## 16. Maintenance rule

When a future PR changes a primitive proof obligation, update this document in the same tranche with:

1. PR number and exact title;
2. which clock changed (PR-title round / internal round / G label / Lean return);
3. predecessor route;
4. whether the predecessor is corrected, superseded, or still an active donor;
5. new first live leaf;
6. source/DOI/QID/Dewey changes, if any;
7. exact-head validation status separately from theorem content.

Do not rewrite history to make the current route look inevitable. Keep route reversals and failed/superseded consumers visible; they are part of the proof-search evidence.
