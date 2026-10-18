# Collatz/Syracuse Same-Object Bridge Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a source-written, same-object bridge from the literal shortcut Syracuse process on positive integers to the repository's finite 2-adic/parity-cylinder machinery, then expose independently verified prefix-absorption and concentration consumers without promoting finite statements to the Collatz conjecture.

**Architecture:** Keep the literal Syracuse orbit as the unique fine dynamical object. Represent finite parity prefixes as observer fibres/residue cylinders, prove forward and reverse reification, and connect the existing finite `3z` / `3z-1` operator only through an explicit transfer/intertwining seam. Reuse the repaired prefactored finite mixing stack and the generic prefix-absorption/hitting stack as independent consumers.

**Tech Stack:** Agda 2.9 repository modules, existing DASHI finite-state/non-Archimedean libraries, shell/static proof-audit scripts, optional existing Lean source receipts only where already canonical.

**Spec:** `docs/superpowers/specs/2026-10-06-collatz-syracuse-same-object-bridge-design.md`

## Global Constraints

- No claim of the Collatz conjecture unless a separate universal integer-stopping theorem is actually proved.
- Never identify the finite affine chain `z -> 3z` / `z -> 3z - 1` with `shortcutSyracuse` itself.
- Never reinstate the refuted unit-prefactor one-step `L2` contraction; preserve finite level-dependent prefactors.
- Probability enters only through an explicit starting-integer sampling law.
- Logarithms live only on positive integer/real lifts, never directly on finite residue classes.
- Every same-object seam must carry forward and reverse/overlap evidence; shared observables or cardinality coincidences do not authorize transport.
- Every new theorem-bearing Agda module must contain no postulates, holes, unsafe options, unsolved metas, or placeholder RHSs.
- Any genuine remaining analytic/arithmetic wall is exported as a minimal typed hypothesis, not a Boolean success flag.

## Review Focus

- **Parity orientation:** odd/even bit conventions and binary-word order must agree with `BinaryBranchOutcomeEnumerationExact`; test `x = 1..16`, prefixes `m = 0..5` against direct iteration.
- **Residue reification uniqueness:** two words of the same length must not map to the same residue; test exhaustive words for small `m` and prove the general uniqueness theorem.
- **Transfer orientation:** observable-forward versus law/adjoint evolution must match `NonArchimedeanAdjointPowerTVWeldExact`; include an explicit negative test/firewall for the opposite orientation.
- **Sampling boundary blocks:** exact uniformity is only for complete `2^m` blocks; test arbitrary interval endpoints and the explicit leftover-block error.
- **Stopping promotion:** finite killed-cylinder or concentration statements must retain the chosen finite level, threshold, and sampling law; consolidated audit tests must reject any unconditional universal stopping promotion.

---

### Task 1: Literal Syracuse carrier and iteration (C1)

**Files:**
- Create: `DASHI/NumberTheory/Collatz/SyracuseExact.agda`
- Create: `scripts/check_collatz_syracuse_exact.sh`

**Interfaces:**
- Consumes: repository Nat arithmetic/parity primitives.
- Produces: `PositiveNat`, `shortcutSyracuse`, `syracuseIterate`, `shortcutSyracusePositive`, branch equations, `syracuseIterateSuc`.

- [ ] **Step 1: Write the static/executable failing check**
  - Require the module and theorem names above.
  - Reject `postulate`, `{!!}`, unsafe options, and placeholder RHSs.
  - Add small direct branch specimens for positive naturals `1..8`.
- [ ] **Step 2: Run the check and verify it fails because the module is absent.**
  - Run: `bash scripts/check_collatz_syracuse_exact.sh`
  - Expected: FAIL on missing `DASHI/NumberTheory/Collatz/SyracuseExact.agda`.
- [ ] **Step 3: Implement the minimal literal Syracuse carrier.**
  - `shortcutSyracuse : PositiveNat -> PositiveNat`
  - `syracuseIterate : Nat -> PositiveNat -> PositiveNat`
  - prove positivity, exact even/odd branch equations, and successor iteration law.
- [ ] **Step 4: Run static checks and Agda typecheck.**
  - Run: `bash scripts/check_collatz_syracuse_exact.sh`
  - Run the repository Agda checker on `DASHI/NumberTheory/Collatz/SyracuseExact.agda`.
  - Expected: PASS.
- [ ] **Step 5: Commit** `feat(collatz): add literal Syracuse dynamics`.

### Task 2: Parity itinerary observer and binary-word conversion (C2/C4)

**Files:**
- Create: `DASHI/NumberTheory/Collatz/SyracuseParityItineraryExact.agda`
- Modify: `scripts/check_collatz_syracuse_exact.sh`

**Interfaces:**
- Consumes: `shortcutSyracuse`, `syracuseIterate`; `DASHI.Core.BinaryBranchOutcomeEnumerationExact.BinaryWord`.
- Produces: `epsilon`, `parityPrefix`, `parityWord`, `parityWordShift`, `epsilonShift`, word/vector conversion theorems.

- [ ] **Step 1: Extend the check with orientation specimens.**
  - Assert parity prefixes for `1..16`, lengths `0..5`, match direct Syracuse iteration.
  - Assert the first bit is the parity of the current state and shifting the orbit drops that bit.
- [ ] **Step 2: Run and verify failure on missing itinerary definitions.**
- [ ] **Step 3: Implement itinerary definitions and source-written shift proofs.**
- [ ] **Step 4: Typecheck and rerun specimens.**
- [ ] **Step 5: Commit** `feat(collatz): add Syracuse parity itinerary`.

### Task 3: Forward residue-cylinder classification (C3 forward)

**Files:**
- Create: `DASHI/NumberTheory/Collatz/SyracuseParityCylinderExact.agda`
- Create: `scripts/check_collatz_syracuse_parity_cylinder.py`

**Interfaces:**
- Consumes: `parityWord`, `syracuseIterate`; binary words and Nat modular arithmetic.
- Produces: `residueOfParityWord`, `parityWordImpliesResidue`, executable small-word classification.

- [ ] **Step 1: Write exhaustive small-`m` tests (`m <= 6`).**
  - For each binary word, compute its candidate residue and verify every small integer with that prefix lies in the candidate class mod `2^m`.
- [ ] **Step 2: Run and verify failure before implementation.**
- [ ] **Step 3: Implement recursive `residueOfParityWord` and forward classification.**
- [ ] **Step 4: Typecheck and run exhaustive specimens.**
- [ ] **Step 5: Commit** `feat(collatz): classify Syracuse parity cylinders`.

### Task 4: Reverse reification and cylinder uniqueness (C5/C3 reverse)

**Files:**
- Modify: `DASHI/NumberTheory/Collatz/SyracuseParityCylinderExact.agda`
- Modify: `scripts/check_collatz_syracuse_parity_cylinder.py`

**Interfaces:**
- Consumes: `residueOfParityWord`, forward classification.
- Produces: `residueImpliesParityWord`, `parityCylinderIff`, `residueOfParityWordInjective`, unique residue-cylinder certificate.

- [ ] **Step 1: Add exhaustive uniqueness/reverse tests for all binary words through `m <= 7`.**
- [ ] **Step 2: Run and verify the reverse theorem is missing.**
- [ ] **Step 3: Prove reverse reification and uniqueness source-written, not by cardinality-only promotion.**
- [ ] **Step 4: Typecheck and rerun exhaustive checks.**
- [ ] **Step 5: Commit** `feat(collatz): reify parity cylinders back to residues`.

### Task 5: Exact affine Syracuse iterate (C6)

**Files:**
- Create: `DASHI/NumberTheory/Collatz/SyracuseAffineIterateExact.agda`
- Create: `scripts/check_collatz_syracuse_affine_iterate.py`

**Interfaces:**
- Consumes: parity words/cylinder equivalence and Syracuse iteration.
- Produces: `parityCount`, executable `affineAdditiveTerm`, and `syracuseAffineIterateExact` proving `2^m * S^m(x) = 3^(s_m(x)) * x + A_m(parityWord m x)`.

- [ ] **Step 1: Write direct arithmetic specimens for small `x,m`.**
- [ ] **Step 2: Run and verify failure before implementation.**
- [ ] **Step 3: Define the recursive additive term and prove the affine identity by induction on the parity word/iteration length.**
- [ ] **Step 4: Typecheck and run arithmetic specimens.**
- [ ] **Step 5: Commit** `feat(collatz): prove exact affine Syracuse iterate`.

### Task 6: Stopped log-drift decomposition (C7)

**Files:**
- Create: `DASHI/NumberTheory/Collatz/SyracuseLogDriftExact.agda`
- Create: `DASHI/NumberTheory/Collatz/SyracuseLogDriftBoundaryExact.agda`
- Create: `scripts/check_collatz_syracuse_log_boundary.sh`

**Interfaces:**
- Consumes: literal Syracuse iteration and affine/parity count data.
- Produces: exact stopped remainder representation; typed boundary separating algebraic identity from any unavailable real-log inequality.

- [ ] **Step 1: Add a failing audit that rejects `log` over `ZMod` and requires an explicit analytic boundary if the sharp real inequality is not source-owned.**
- [ ] **Step 2: Run and verify failure.**
- [ ] **Step 3: Implement the exact odd-step remainder accumulator and stopped-process interface.**
- [ ] **Step 4: Prove every currently available deterministic inequality; if `log(1+u) <= u` is not in the local formal library, export precisely that typed real-analysis hypothesis and compile all downstream algebra around it.**
- [ ] **Step 5: Typecheck and commit** `feat(collatz): add stopped Syracuse log drift`.

### Task 7: Same-object observer fibre (C9 foundation)

**Files:**
- Create: `DASHI/Analysis/CollatzSyracuseParityObserverExact.agda`

**Interfaces:**
- Consumes: `HyperformChartGluingExact.ObserverWithFibre`; `parityCylinderIff`.
- Produces: `syracuseParityObserver`, exact observer-fibre/congruence equivalence, negative promotion firewall.

- [ ] **Step 1: Add source-shape checks requiring explicit observer fibre and a false/nonconstructible `sharedObservableImpliesKernelEquality` promotion.**
- [ ] **Step 2: Verify failure.**
- [ ] **Step 3: Instantiate the fine/coarse observer and prove its fibre is exactly the residue cylinder.**
- [ ] **Step 4: Typecheck.**
- [ ] **Step 5: Commit** `feat(collatz): add parity observer fibre`.

### Task 8: Finite transfer/intertwining weld (C8)

**Files:**
- Create: `DASHI/Analysis/CollatzSyracuseFiniteTransferSameObjectWeldExact.agda`
- Read/Reuse: `DASHI.Analysis.NonArchimedeanAdjointPowerTVWeldExact`, existing source adapter modules for `CollatzRelMatrix`.
- Create: `scripts/check_collatz_transfer_orientation.py`

**Interfaces:**
- Consumes: parity observer/cylinder equivalence and the existing finite affine operator source receipts.
- Produces: a `SyracuseFiniteTransferWeld` record carrying finite source operator attribution, one-step supported-observable intertwining, iterated intertwining, and an explicit `fineKernelEquality = false` firewall.

- [ ] **Step 1: Determine and encode the orientation test from existing adjoint/law-vs-observable semantics.**
- [ ] **Step 2: Run the orientation check; it must fail until a theorem-bearing weld exists.**
- [ ] **Step 3: Prove the strongest correct intertwining equation. If the proposed orientation is algebraically false, prove/reify the correct adjoint/transfer statement and record the rejected orientation explicitly.**
- [ ] **Step 4: Typecheck and run finite small-cylinder orientation specimens.**
- [ ] **Step 5: Commit** `feat(collatz): weld Syracuse cylinders to finite transfer operator`.

### Task 9: Full cylinder interface match (C9)

**Files:**
- Create: `DASHI/Analysis/CollatzSyracuseCylinderInterfaceMatchExact.agda`

**Interfaces:**
- Consumes: observer fibre, finite transfer weld, hyperfabric pants seam pattern.
- Produces: `CollatzCylinderInterfaceMatch` covering word/cylinder identity, branch orientation, count-vs-probability normalization, time alignment, and observable/law orientation.

- [ ] **Step 1: Add a failing check that partial coordinate equality cannot construct the full match.**
- [ ] **Step 2: Implement the typed interface record and canonical constructor from all required coordinates.**
- [ ] **Step 3: Prove projection lemmas and negative partial-match firewalls.**
- [ ] **Step 4: Typecheck.**
- [ ] **Step 5: Commit** `feat(collatz): add full Syracuse cylinder interface match`.

### Task 10: Sampled-start pushforward (C11)

**Files:**
- Create: `DASHI/Analysis/CollatzSyracuseSamplingPushforwardExact.agda`
- Create: `scripts/check_collatz_sampling_pushforward.py`

**Interfaces:**
- Consumes: `parityCylinderIff`, finite counting/probability normalization utilities.
- Produces: finite interval sampling law, complete-block exact uniform pushforward, arbitrary-interval leftover-block bound and corresponding finite TV bound.

- [ ] **Step 1: Write complete-block and incomplete-block exhaustive tests for small intervals/prefix lengths.**
- [ ] **Step 2: Verify failure before implementation.**
- [ ] **Step 3: Prove exact uniformity for interval lengths divisible by `2^m`.**
- [ ] **Step 4: Prove explicit incomplete-block count/TV error; keep logarithmic weighting out of this base theorem.**
- [ ] **Step 5: Typecheck, run specimens, commit** `feat(collatz): prove parity-prefix sampling pushforward`.

### Task 11: Same-object prefix absorption and finite hitting route (C12b)

**Files:**
- Create: `DASHI/Analysis/CollatzSyracusePrefixAbsorptionWeldExact.agda`
- Create: `DASHI/Analysis/CollatzSyracuseUniformHittingBlockExact.agda`
- Create: `DASHI/Analysis/CollatzSyracuseGeometricSurvivalExact.agda`

**Interfaces:**
- Consumes: `FinitePrefixAbsorptionExact`, uniform hitting-block compiler, hitting-word padding, `FiniteUniformBranchingHittingTailExact`, sampling pushforward.
- Produces: source-path same-object absorption receipt; finite-level conditional uniform hitting block; geometric survivor-count theorem and sampled-start transport where killed-continuation hypotheses are actually proved.

- [ ] **Step 1: Add a test/check that an endpoint-only hit cannot stand in for a prefix hit and that padding preserves an actually killed prefix.**
- [ ] **Step 2: Instantiate `BinaryStoppingSystem` on the actual parity-cylinder semantics and close the source-path weld.**
- [ ] **Step 3: Reuse finite reachability only at explicitly stated finite levels/targets; compile the uniform block where the needed reachability inhabitant exists.**
- [ ] **Step 4: Instantiate the generic branching-tail compiler only after proving exact branch count, killed continuation, and aggregate recurrence; otherwise export exactly the missing field as a typed obligation.**
- [ ] **Step 5: Typecheck and commit** `feat(collatz): add same-object prefix absorption route`.

### Task 12: Repaired finite correlation transport (C10)

**Files:**
- Create: `DASHI/Analysis/CollatzSyracuseCylinderCorrelationExact.agda`

**Interfaces:**
- Consumes: `NonArchimedeanContinuousMixingBidiExact`, Hilbert correlation decay, cylinder interface match.
- Produces: finite cylinder correlation decay retaining the level-dependent prefactor `C_n` and supported-observable hypotheses.

- [ ] **Step 1: Add a static rejection check for any positive unit-prefactor theorem.**
- [ ] **Step 2: Implement correlation transport through the proven cylinder seam.**
- [ ] **Step 3: Prove the prefactor remains explicit and no kernel-equality promotion is used.**
- [ ] **Step 4: Typecheck.**
- [ ] **Step 5: Commit** `feat(collatz): transport repaired cylinder correlations`.

### Task 13: Genuine concentration compiler (C12a)

**Files:**
- Create: `DASHI/Analysis/CollatzSyracuseMixingConcentrationCompilerExact.agda`

**Interfaces:**
- Consumes: repaired cylinder correlation/TV results.
- Produces: theorem-bearing `CollatzConcentrationHypotheses` record with bounded centered parity observable and either an explicit strong/rho-mixing decay theorem or a pseudo-spectral-gap theorem sufficient for the selected concentration consumer.

- [ ] **Step 1: Add a failing firewall test: a plain field named `spectralGap` or eigenvalue-radius estimate is insufficient to construct the concentration receipt.**
- [ ] **Step 2: Search existing repo generic concentration/mixing primitives and select the shortest theorem-bearing route, preferring correlation/TV -> dependence coefficient.**
- [ ] **Step 3: Implement all generic compilers available in-repo and isolate any genuinely absent concentration inequality as one minimal typed analytic hypothesis with exact constants/observable bounds.**
- [ ] **Step 4: Typecheck and audit the hypothesis boundary.**
- [ ] **Step 5: Commit** `feat(collatz): add theorem-bearing concentration interface`.

### Task 14: Stopping/concentration transport (C13 route 1)

**Files:**
- Create: `DASHI/Analysis/CollatzSyracuseStoppingConcentrationExact.agda`

**Interfaces:**
- Consumes: sampling pushforward, parity concentration receipt, stopped log-drift remainder, exact negative drift.
- Produces: a stopping/concentration theorem explicitly parameterized by threshold, finite prefix length, sampling law, finite-level error, and any remaining analytic hypothesis.

- [ ] **Step 1: Add a check that no theorem in this module has an unconditional `∀ x : PositiveNat` Collatz-termination conclusion.**
- [ ] **Step 2: Prove/compile the exact negative drift sign in the available real-analysis carrier.**
- [ ] **Step 3: Combine parity deviation, remainder control and sampling transport into the strongest theorem supported by the paid hypotheses.**
- [ ] **Step 4: Typecheck.**
- [ ] **Step 5: Commit** `feat(collatz): transport concentration to Syracuse stopping`.

### Task 15: Consolidated max-cut audit and import surface (C14)

**Files:**
- Create: `DASHI/Analysis/CollatzSyracuseSameObjectMaxCutExact.agda`
- Create or modify: `DASHI/EverythingNonArchimedeanSpectralBidi.agda` only if the existing import policy accepts this Collatz-specific owner.
- Create: `scripts/check_collatz_syracuse_same_object_maxcut.sh`

**Interfaces:**
- Consumes: Tasks 1-14.
- Produces: explicit statuses `proved`, `compiledFromRepo`, `conditionalOnHypothesis`, `sourceSpecificOpen`, `refutedRoute`; consolidated promotion firewall; exact list of remaining walls.

- [ ] **Step 1: Add the final audit script.**
  - Require every module/theorem/status constructor.
  - Reject postulates/holes/unsafe options/placeholders.
  - Reject positive reuse of the old unit-prefactor theorem.
  - Reject direct finite-residue log observables.
  - Require negative same-kernel/universal-stopping promotion firewalls.
- [ ] **Step 2: Run the audit and verify missing consolidated owner.**
- [ ] **Step 3: Implement the max-cut owner with statuses derived from actual theorem inhabitants, not aspirational comments.**
- [ ] **Step 4: Run leaf typechecks, consolidated typecheck, all Collatz static/specimen checks, and relevant existing non-Archimedean checks.**
- [ ] **Step 5: Commit** `feat(collatz): consolidate Syracuse same-object max-cut`.

### Task 16: Final verification and frontier report

**Files:**
- Modify only audit/docs if verification exposes stale status text.

**Interfaces:**
- Consumes: entire implementation.
- Produces: exact paid/open/refuted frontier tied to source theorem names and checks.

- [ ] **Step 1: Run all new Collatz scripts plus the repository Agda typechecker over every new module in dependency order.**
- [ ] **Step 2: Run existing non-Archimedean spectral/static checks touched by the transfer/correlation imports.**
- [ ] **Step 3: Inspect the diff for attribution, accidental promotion, placeholders, and duplicate representations.**
- [ ] **Step 4: If all checks pass, record exact paid/open walls in the max-cut owner and commit any status-only correction.**
- [ ] **Step 5: Report the exact head, files changed, checks run, and the minimal remaining mathematical obligations; never summarize a conditional theorem as a Collatz proof.**
