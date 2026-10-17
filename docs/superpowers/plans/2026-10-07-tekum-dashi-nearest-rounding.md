# DASHI Exact Nearest Tékum Rounding Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a DASHI-owned exact nearest-rounding semantics for ordinary finite Tékum values, derive a deterministic canonical operator, characterize raw-truncation correction, and close no-double-rounding with either a theorem or an exact same-object falsifier.

**Architecture:** Keep semantic authority set-valued and exact over `ℚ`: enumerate ordinary finite target words, compute exact rational distance, and define nearestness independently of raw truncation. Raw truncation is only a provisional implementation hint. Small-width exhaustive computation determines tie structure and correction radius before any efficient algorithm is promoted. No-double-rounding is theorem-or-falsifier, never assumed.

**Tech Stack:** Agda + stdlib `Data.Rational`, `Data.Vec`, existing Tékum parser/order/balanced-ternary owners, local Python for exact exhaustive discovery.

**Spec:** `docs/superpowers/specs/2026-10-07-tekum-dashi-nearest-rounding-design.md`

## Global Constraints

- This is DASHI semantics, not Hunhold Proposition 5 and not a repair of that proposition.
- Reuse `TekumSourceWordDecodeExact.parseTekumWord` and `TekumExactTriadicSemanticsExact.ordinaryRational`; do not introduce a second numeric decoder.
- Reuse existing finite balanced-ternary word carriers/enumerators rather than encoding Tékum words in a new representation.
- Reserved NaR, special zero, and infinity are excluded from the ordinary finite target metric.
- Numerical same-object claims are restricted to source-parser-supported even widths `8 + extra`; the first no-double-rounding chain is 12→10→8.
- `exactNearestSet` is set-valued. Do not choose a tie policy until exact enumeration maps the tie surface.
- Machine Float is never semantic authority.
- Stop a theorem lane immediately on an exact same-object counterexample and promote the falsifier.
- Existing flags `sourceProp5NearestRoundingPaid = false` and `numericalNoDoubleRoundingPaid = false` retain their historical Hunhold/raw meaning.

## Review Focus

1. **Special strings:** target enumeration must exclude reserved NaR/zero/infinity strings even if neighbouring ordinary values are close.
2. **Target-width floor:** no numerical theorem may instantiate a target width below the parser’s `8 + extra` domain.
3. **Ties:** semantic nearestness remains multi-valued until a separate intrinsic tie policy is proved.
4. **Regime boundaries:** raw→nearest displacement must be measured across all ordinary/special boundary neighbourhoods, not only central regimes.
5. **No-double-rounding:** a passing finite probe is evidence only; a global claim needs proof, while one exact counterexample terminates the theorem lane.

---

### Task 1: Exact ordinary-finite target carrier and distance

**Files:**
- Create: `DASHI/ComputerScience/TekumExactNearestRoundingSemantics.agda`
- Modify: `scripts/check_tekum_prop5_nogo_static.py` or add a dedicated `scripts/check_tekum_dashi_nearest_static.py`

**Interfaces:**
- Consumes: `parseTekumWord`, `ordinaryRational`, existing word carrier/enumeration machinery.
- Produces: `FiniteTekumWord`, `finiteWordValue`, `tekumDistance`, `Nearest`, `NearestSet`.

- [ ] **Step 1: Add failing static regression** requiring the five interface names and an explicit exclusion of the three reserved special strings.
- [ ] **Step 2: Verify RED** with the local Python static checker.
- [ ] **Step 3: Implement `FiniteTekumWord` as a same-object package** containing a target source word, the decoded `Sem.OrdinaryTekum`, and `parseTekumWord word ≡ just (Sem.ordinary ordinary)`.
- [ ] **Step 4: Implement exact `finiteWordValue`, `tekumDistance`, `Nearest`, and `NearestSet`** over `ℚ`, with no raw-truncation dependency.
- [ ] **Step 5: Add width-8 fixtures** proving ordinary candidates are admitted and NaR/zero-special/infinity are not ordinary candidates.
- [ ] **Step 6: Run static checks; commit** `Tekum: define exact nearest-rounding semantics`.

### Task 2: Finite enumeration and nearest-existence oracle

**Files:**
- Create: `DASHI/ComputerScience/TekumNearestRoundingEnumerationExact.agda`
- Modify: `DASHI/ComputerScience/TekumExactNearestRoundingSemantics.agda`
- Modify: `scripts/check_tekum_dashi_nearest_static.py`

**Interfaces:**
- Consumes: Task 1 semantic predicates and the existing finite trit-word enumeration/bijection.
- Produces: `ordinaryFiniteTargets`, `exactNearestSet`, `nearestSetNonempty`, `nearestDistanceMinimal`.

- [ ] **Step 1: Require enumeration/oracle names in the static regression and verify RED.**
- [ ] **Step 2: Enumerate all target words at a supported width and filter by same-object ordinary decode**, preserving the original source word in each element.
- [ ] **Step 3: Define `exactNearestSet` by minimum exact rational distance** over that finite list; return all minimisers.
- [ ] **Step 4: Prove/construct `nearestSetNonempty` for supported widths** from nonempty ordinary target enumeration.
- [ ] **Step 5: Export `nearestDistanceMinimal`** showing every returned candidate is no farther than every finite target candidate.
- [ ] **Step 6: Commit** `Tekum: construct exact finite nearest-set oracle`.

### Task 3: Exact Python discovery of ties and raw correction radius

**Files:**
- Create: `scripts/tekum_nearest_rounding_exhaustive.py`
- Create: `docs/superpowers/receipts/2026-10-07-tekum-nearest-rounding-enumeration.md`

**Interfaces:**
- Consumes: literal repository source formulas for balanced-ternary evaluation, anchor arithmetic, parser tables, and exact rational semantics.
- Produces: exhaustive tables/receipts for 10→8 and 12→10; tie classes; raw-target special frequency; raw→nearest source-code displacement; candidate uniform correction radius.

- [ ] **Step 1: Implement a Python exact-rational mirror only for discovery**, with assertions against existing Agda calibration rows and the known Prop. 5 finite counterexample (`1094/2187`, `122/243`, `364/729`).
- [ ] **Step 2: Exhaust all ordinary 10-trit sources against ordinary finite 8-trit targets.** Record nearest-set cardinality, tie locations, raw-target class, and raw→nearest displacement.
- [ ] **Step 3: Exhaust or stream 12→10 if practical; otherwise exhaust all boundary/regime slices plus a deterministic complete chunking strategy and state the limitation explicitly.**
- [ ] **Step 4: Write the receipt with exact counts and the smallest observed correction radius.**
- [ ] **Step 5: Ruling:** if radius-one fails, do not implement a ±1 correction; if any tested displacement exceeds every candidate bounded radius under consideration, promote the local-radius lane to open/no-go.
- [ ] **Step 6: Commit** `Tekum: enumerate exact nearest rounding behaviour`.

### Task 4: Canonical intrinsic tie policy

**Files:**
- Create: `DASHI/ComputerScience/TekumCanonicalNearestTieExact.agda`
- Modify: `scripts/check_tekum_dashi_nearest_static.py`

**Interfaces:**
- Consumes: `exactNearestSet` and Task 3 tie receipt.
- Produces: `CanonicalTieKey`, `canonicalNearest`, `canonicalNearestInExactNearestSet`, `dashiNearestRound`.

- [ ] **Step 1: From the receipt, choose the simplest representation-intrinsic total tie key** (source integer-code order is the fallback if no stronger canonical parity property is evidenced). Record the choice and rationale in source comments as DASHI policy.
- [ ] **Step 2: Add failing static requirements for the four interface names.**
- [ ] **Step 3: Implement tie-key minimisation only within `exactNearestSet`.**
- [ ] **Step 4: Prove `canonicalNearestInExactNearestSet` and expose `dashiNearestRound`.**
- [ ] **Step 5: Add at least one exact tie fixture if ties exist; otherwise prove/record uniqueness on the exhaustively checked widths without generalising it globally.**
- [ ] **Step 6: Commit** `Tekum: define canonical exact-nearest tie policy`.

### Task 5: Raw candidate and correction characterization

**Files:**
- Create: `DASHI/ComputerScience/TekumRawNearestCorrectionExact.agda`
- Modify: `scripts/check_tekum_dashi_nearest_static.py`

**Interfaces:**
- Consumes: existing anchor/truncation/inversion path, `dashiNearestRound`, source integer-code order.
- Produces: `rawTruncationCandidate`, `rawTargetOrdinary`, `rawNearestDisplacement`, and theorem/falsifier owners for the strongest correction-radius claim surviving Task 3.

- [ ] **Step 1: Reconstruct the existing raw  n→n-2 candidate as a named same-object function**, without changing `truncateTwo`.
- [ ] **Step 2: Define displacement only when both raw and canonical targets are ordinary finite.**
- [ ] **Step 3: Formalize exact fixtures from the Task 3 receipt, including the existing finite-nearest counterexample.**
- [ ] **Step 4: Promote the strongest honest radius statement:** prove radius one if true; otherwise prove its counterexample and proceed to the smallest surviving radius; if no width-independent radius is justified, expose an explicit open/no-go boundary.
- [ ] **Step 5: Commit** `Tekum: characterize raw-to-nearest correction`.

### Task 6: Efficient local nearest implementation or no-go boundary

**Files:**
- Create: `DASHI/ComputerScience/TekumEfficientNearestRoundingExact.agda`
- Modify: `scripts/check_tekum_dashi_nearest_static.py`

**Interfaces:**
- Consumes: Task 5 correction bound and Prop. 4/order machinery.
- Produces, if viable: `localNearestCandidates`, `efficientNearestRound`, `efficientNearestEqualsCanonicalNearest`; otherwise `uniformLocalCorrectionNotEstablished` / exact falsifier owner.

- [ ] **Step 1: If Task 5 yields a proved finite radius R, define the R-neighbourhood in source integer-code order around raw target; include boundary handling across reserved strings/regime transitions.**
- [ ] **Step 2: Choose exact-rational nearest inside that neighbourhood using the canonical tie policy.**
- [ ] **Step 3: Prove candidates outside the neighbourhood cannot beat the local minimum using monotonic source order and the Task 5 radius theorem.**
- [ ] **Step 4: Prove `efficientNearestEqualsCanonicalNearest`.**
- [ ] **Step 5: If no finite radius is proved, do not create a fake efficient implementation; instead create a fail-closed owner recording exhaustive oracle as canonical and local optimisation as unproved/refuted.**
- [ ] **Step 6: Commit** `Tekum: close efficient exact-nearest implementation boundary`.

### Task 7: No-double-rounding exhaustive search at 12→10→8

**Files:**
- Extend: `scripts/tekum_nearest_rounding_exhaustive.py`
- Extend: `docs/superpowers/receipts/2026-10-07-tekum-nearest-rounding-enumeration.md`

**Interfaces:**
- Consumes: deterministic `dashiNearestRound` semantics from Task 4.
- Produces: exact equality census or lexicographically/source-code minimal counterexample for 12→10→8.

- [ ] **Step 1: Enumerate ordinary 12-trit source words and compare canonical two-stage 12→10→8 against direct 12→8.**
- [ ] **Step 2: If a mismatch appears, stop the theorem lane at the first source-code-minimal mismatch and record all three decoded rational values and nearest sets.**
- [ ] **Step 3: If exhaustive equality holds, record exact coverage/counts and proceed to a general proof attempt; do not promote the census itself to a theorem.**
- [ ] **Step 4: Commit** `Tekum: probe exact-nearest no-double-rounding`.

### Task 8: Global no-double-rounding theorem or exact falsifier

**Files:**
- Create: `DASHI/ComputerScience/TekumNearestNoDoubleRoundingExact.agda`
- Modify: `scripts/check_tekum_dashi_nearest_static.py`

**Interfaces:**
- Consumes: Task 7 outcome and Tasks 1–6 semantics.
- Produces exactly one terminal lane: `dashiNearestNoDoubleRounding` or `dashiNearestNoDoubleRoundingCounterexample` plus an impossibility theorem for the global equality claim.

- [ ] **Step 1A (counterexample lane):** encode the source/intermediate/direct target words from Task 7, prove their parser same-object receipts and exact rational values, prove each chosen target is canonical nearest at its stage, and prove the two final target words differ.
- [ ] **Step 2A:** define the universal no-double-rounding proposition and refute it from the concrete instance.
- [ ] **Step 1B (theorem lane):** if Task 7 found no counterexample, prove a general midpoint/cell nesting theorem sufficient for canonical-nearest composition, including tie-policy compatibility.
- [ ] **Step 2B:** derive `dashiNearestNoDoubleRounding` for supported even width drops.
- [ ] **Step 3: Commit** `Tekum: close exact-nearest no-double-rounding theorem boundary`.

### Task 9: Canonical DASHI boundary and assembly integration

**Files:**
- Create: `DASHI/ComputerScience/TekumDASHIRoundingBoundaryExact.agda`
- Modify: `DASHI/ComputerScience/TekumBalancedTernaryVerifiedAssembly.agda`
- Modify: `scripts/check_tekum_dashi_nearest_static.py`
- Update: PR #1102 description/title if needed.

**Interfaces:**
- Consumes: all prior tasks.
- Produces explicit independent truth fields for exact-nearest semantics, tie policy, correction radius, efficient equivalence, and no-double-rounding theorem/refutation.

- [ ] **Step 1: Add boundary fields:** `hunholdRawTruncationNearestRefuted`, `dashiExactNearestSemanticsPresent`, `nearestExistencePaid`, `canonicalTieRulePaid`, `rawCorrectionRadiusCharacterized`, `efficientNearestImplementationPaid`, `efficientNearestEqualsSemanticOraclePaid`, `nearestNoDoubleRoundingPaid`, `nearestNoDoubleRoundingRefuted`.
- [ ] **Step 2: Enforce mutual exclusion of the final no-double-rounding true/refuted fields by constructor/theorem shape rather than prose alone.**
- [ ] **Step 3: Import the DASHI owners into the canonical assembly without changing the historical Hunhold false flags.**
- [ ] **Step 4: Run local Python static/exhaustive checks available in this environment.**
- [ ] **Step 5: Update PR receipt with exact theorem/falsifier state and attribution boundary.**
- [ ] **Step 6: Commit** `Tekum: integrate DASHI exact-nearest rounding max-cut`.
