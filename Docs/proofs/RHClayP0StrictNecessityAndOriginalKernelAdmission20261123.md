# RH/GRH P0 — what Clay actually requires, original proof source admission, and detector mincut (23 November 2026)

## Executive decision — stop treating optional geometry as mandatory proof debt

For Clay Riemann Hypothesis, the mathematical obligation is the **unconditional statement**: for every nontrivial Riemann-zeta zero \(\rho\), \(\Re\rho=1/2\). A proof may use any sound method. **Nothing in Clay requires** punctured ternary 27, Albert J0 dimension26, F4 dimension52, balanced ternary signs, dyadic flags 32768/1024/208, four prime ports, an even 52nd-order annihilator, special \(C^\infty\) flat-top smoothing, or any specific explicit formula. They are **optional components of our own hypothetical Weil-test proof route**, not universal theorem prerequisites. Clay does not require Lean or Agda; formal proof checking is a strong extra verification option. The published Clay prize rules separately require qualified publication, ≥2 years, and general mathematical acceptance before prize consideration. Official mathematical problem: https://www.claymath.org/millennium/riemann-hypothesis/ ; official rules: https://www.claymath.org/millennium-problems/rules/.

**P0A (higher priority): verify the existing externally authored exact RH/GRH Lean candidate in its OWN source-pinned environment.** It is a completely separate possible proof of RH. If genuinely kernel accepted with authentic standard axioms, and its statement matches the actual zeta problem, the 26J/dyadic/prime-port experimental work is NOT needed to establish the result. Proof **SOURCE-PRESENCE is not kernel acceptance**.

**P0B (alternate internal proof route): only if genuinely developing an independent original Weil-detector argument, the terminal requires a NEW strict signed bound from source information not already contained in the identity/zero-side positivity.** Improving the \(4 E_j\) smoothness envelope, or constructing more finite geometries, does NOT pay that bound. Defer optional numeric/geometry optimisation until a direct proof of E3 or a controlled impossibility/obstruction is identified.

## P0A: exact source-first verified inventory, no new compiler

Original Lean source: `chboishabba/riemann-hypothesis-lean` revision `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
- `src/Main.lean` Git blob **`dbd5db70bc11b35f18fa5751216ab335321e7bfc`**, independently fetched at that revision. Its exact declaration is `theorem riemannHypothesis : RiemannHypothesis := rhOfAll`; original other four endpoints consume `rhOfAll`, `allChi`, `claimAll.2.1`, `critAll`.
- `src/Statements.lean` blob **`1cd1bce93344065936b2b392b23306254e0785ef`**, independently fetched; includes the literal zeta nontrivial-zero and all-\(N\), all-Dirichlet-character terminal definitions. `Statements` imports Mathlib.
- Original `lean-toolchain=leanprover/lean4:v4.33.1` and `mathlib` manifest revision `0df444a360eaa60ab8c11dca51a86af692955474`. These source identity checks passed by remote source inspection; the full imported proof closure, axioms, and kernel validation have **NOT** been rerun here.
- **Existing DASHI owner, not duplicate:** merged `dashi_lean4` PR **#113** supplies `proofs/alpoge-lean433/fork_pin.json`, `RHAdmission.lean`, `RHTopCut.lean`, `RHGRHP0DirectionalSourceCut.lean`, `checkout_fork_source.sh`, and **`check_original_p0_admission.sh`**. The admitted source in `RHAdmission` imports `Main` in the isolated original version and prints axioms on five original terminal declarations. Reuse EXACT these files.
- `dashi_lean4@main` `lean-toolchain` was freshly verified as **Lean v4.28.0**, not v4.33.1 and not v4.35. The existing `MillenniumExternal/AlpogeRHBoundaryExact.lean` theorem `clay_of_admitted_mathlib` takes **an actual proof term** `admitted : _root_.RiemannHypothesis`. It does NOT construct that proof term by import in the v4.28 root. Never load foreign v4.33.1 `.olean` as a v4.28 kernel receipt; never import a bare named theorem as an axiom.
- The original candidate's Lean kernel/axiom status remains **external/reported, not independently attested by this run**. A valid type-checked Lean environment (with `#print axioms` restricted to standard `propext`, `Classical.choice`, `Quot.sound`) is more meaningful for theorem admission than the symbolic E2 plateau thresholds.

**Existing local command (on your development host; do not launch GitHub CI):**
```bash
bash proofs/alpoge-lean433/check_original_p0_admission.sh
```
The existing runner invokes the original source checkout pin checker, `lake build Main` in the v4.33.1 source, then `lake env lean` on `RHAdmission.lean`, and parses all five `#print axioms` receipts. It may require substantial local build time; do NOT mistake a timeout or source readback for a kernel pass. User preference is checkpointed ≤90s chunks and local execution; if time-constrained, perform source pin separately using the existing `checkout_fork_source.sh` and reserve the full build for an appropriate local execution environment. The current turn did NOT run Lean or lake.

**Trust after a PASS:** original v4.33.1 source-specific proof; for DASHI native v4.28 root formal admission, a compatible theorem term or formally checked translation still required. For Clay mathematical validity the exact theorem, standard-axiom proof and accepted exposition are the primary issues; the internal version transport is a DASHI software integration goal, not part of Clay's mathematical statement.

## P0B: the literal terminal is an independent theorem, not a normalization

Existing original Lean source on `dashi_lean4@main`:
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleCutset.lean` has `QuarticFourSignedPolePair.two_target_le_combinedCluster`: under the hypothetical off-line zero and original target band, **`2*D ≤ combinedCluster`**, with `D=W.combinedZeroHeightDefect rho`; its `false_of_quarticFourSignedPole_external_strict` excludes the zero only if an independent *strict reverse* estimate is supplied for the original off+Gamma expression.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierTerminal.lean` proves `postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack` and `canonicalLocalBudgetSlack_nonneg`. Its **unproved condition** `CompletedResidualWithLocalSlackUniformHighEstimate CV T` existentially requires a selected W with
  ```text
  completedSignedResidual + 1/2 * canonicalLocalBudgetSlack(EV)
      < 2 * combinedZeroHeightDefect rho .
  ```
  The file proves this is equivalent to the older `LiteralFarMinusMuUniformHighEstimate` under the original cutoff; **equivalence does not establish either**.
- The original zero-side and completed source geometry yields an algebraic obstruction. Write the true target \(d≥0\), target-zero contribution \(D≥2d\), and local upper-bound slack \(S≥0\). The proposed strict terminal is \(2D+S<4d\), whereas **\(2D+S−4d=2(D−2d)+S≥0\)**. A contradiction can be obtained only from a genuinely independent upper estimate that is incompatible with these inequalities if an off-critical zero exists. Algebraic restatement, reparametrisation, dyadic charts, or existing equality cannot provide that new estimate.
- Negative-control scalar fixture: \(d=1,\ D=2,\ S=0\) satisfies all the nonnegative inequalities and gives zero gap, not strict negative. This is **not a model of zeta zeros**; it proves only that the displayed inequalities alone do not imply the missing strict sign.

**P0B remaining true gates:** construct actual selected W and physically admissible detector if needed for this proof; independently prove a signed zero/Gamma/prime estimate strong enough to contradict the zero-side bound; make all kernel and source-normalization checks; cover all large heights and then the finite/computable low-height region. If E3 fails or cannot be separately estimated, **do not spend more time optimising E0/E2 26J, q=16, 1024, 208, 32768, or flat-top radius as if they were required Clay lemmas**.

## Priority / attribution matrix

| Item | Clay mathematical necessity | Current DASHI status | P0 action |
|---|---|---|---|
| Every nontrivial zeta zero has real part 1/2 | **Yes** | Unproved here | Primary theorem |
| Independent accepted proof in original pinned v4.33.1 candidate | Not a mandated *method*; sufficient if valid | Source root/Statements pinned, kernel **not locally run** | **First** |
| Compatible native v4.28 root term | Not demanded by Clay | Conditional imported proof term only | After v4.33.1 acceptance, if DASHI root integration needed |
| Independent signed E3 strict estimate for our original selected-W detector | Only for THAT strategy | **Open** | Alternate research route |
| E0 smooth carrier / E1 source adapter / E2 FarExact | Only if they are needed for E3 in THAT strategy | Partial math; kernel and full bound open | Conditional, not first |
| 27=1+26, 52=2×26, punctured sign chart | **No** | Exact source indexing, not an RH operator action | Archive as supporting cross-domain work |
| 4×256=1024, 208, 32768, box widths, chosen smoothness optimization | **No** | Exact number provenance and optional improved estimates | **Remove from critical path** |

**Execution policy:** no unlicensed redistribution of the external original Lean source; no CI; no fabricated kernel results; no assumption of acceptance; read source ownership. The mathematical Clay proof is independent of all optional geometries and independent of formal proof-assistant infrastructure. **RH and GRH remain unresolved in this acceptance ledger.**
