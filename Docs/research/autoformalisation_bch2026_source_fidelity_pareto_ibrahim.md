# Bastounis–Circelli–Hansen (2026): source-faithful autoformalisation max-cut

**Source:** Alexander Bastounis, Fabian Circelli and Anders C. Hansen, *Navier–Stokes lost in translation: Why Lean verification of AI autoformalisation does not guarantee correct natural language proofs*, **arXiv:2610.08144v1**, submitted 2026-10-06 10:58 UTC; 25 pages, 4 figures. Original article [HTML](https://arxiv.org/html/2610.08144v1), [arXiv abstract](https://arxiv.org/abs/2610.08144), DOI [10.48550/arXiv.2610.08144](https://doi.org/10.48550/arXiv.2610.08144).

**Status:** novel finite DASHI reconstruction and source correspondence audit. This is **not** a formalisation of the entire paper, its complete Appendix A hierarchy, or OpenAI's physical Navier–Stokes proof. No Lean/Agda kernel build has been observed. The historical audit is about text/code correspondence, not kernel unsoundness. Original mathematical/theoretical authorship, evidence layers and later versions remain distinct.

## Source thesis and two distinct tasks

The source §1 explicitly contrasts:

1. **Type (i)**: theorem *statement already faithfully encoded*; use AI to replace/translate an alleged NL proof by **any** Lean proof of the formal statement that compiles without sorry/extra axioms.
2. **Type (ii)**: semantic preservation of definitions, statements, dependencies **and**, if the asserted task is to validate the original proof, the written proof's mathematical reasoning. Type-(i) compilation does not establish type-(ii) correspondence.

The authors expressly disclaim determining whether OpenAI's NL paper is correct; they argue that the audited Lean proofs do not certify corresponding NL intermediate statements and proof strategies. Treat their conclusions as original argued claims unless independently checked against the fixed primary objects.

## Claim-by-claim exact finite proof cut

| Source locus | NL/historical source object | New formal reconstruction | Proof ceiling / open obligation |
|---|---|---|---|
| §2 Example 2.1 | p(x)=x³−x²−x+1 ≥0 for x≥−1; NL argument falsely sets p=(x−1)(x+1)² | Lean `polynomial_actual_factorisation` establishes actual p=(x−1)²(x+1), `polynomial_nonnegative_on_source_domain`, and explicit failure of printed factorisation at x=2. Agda proves a source-proof-route collision. | A correct theorem under a **different** proof is not validation of the original argument. |
| §2 Example 2.2 | NL diagonalises real symmetric n×n A before summing λᵢ²; cited AI proof instead uses direct symmetric matrix entries | Lean `symmetric_matrix_trace_square_entrywise` proves `0≤ΣᵢΣⱼ AᵢⱼAⱼᵢ` under symmetry for arbitrary finite n; Agda proves the methods remain different even for an identical conclusion. | The direct proof is correct but does not recreate the NL spectral-diagonalisation proof route. |
| §3.1 Example 3.1, source (8.19), comparison (3.1)/(3.2) | NL `||N⁻¹F||_{Cʸᵐ} ≤ C_m ||F||_{Cʸ^(m+4)}` | Audited **historical** Lean `norm_derivativeWord_inverse_le` has separate pure-coordinate jet hypotheses `w.length + 5`. Lean `source_budget_cannot_pay_audited_lean_jet` proves (m+5)≰(m+4) for all m. Agda exhibits source-specific derivative-debt collision. | Stronger assumption cost is real; additionally the pure-coordinate jet bounds and full torus Cʸᵐ supremum over all words must be formally compared. No functional analytic lemma (8.19) is proved or refuted. |
| §3.2 Example 3.3, source (10.19), comparison (3.4)/(3.5) | NL flux RHS `(C_T/R)[(B_R+1) B_R^(1/2)+R^(−3/4) B_R^(3/4)]`, for a.e. t | Historical Lean `exists_uniform_actual_pressure_flux_bound` requires additional `A_R/R + 1/R²`, with different Hölder/Riesz/Sobolev proof strategy and a different t-quantifier. Lean proves **independent-parameter RHS** mismatch at B=0,R=1; Agda proves forgetting `A_R` erases a source coordinate. | A symbolic RHS mismatch is **not** a PDE solution violating either inequality; actual `A_R,B_R` dependencies, constants and time quantifiers need independent audit. |
| §4 Example 4.3 | `n_e` is LEAST n with no natural roots to x₁+x₂−n=0, potentially undefined | Lean proves x₁=n,x₂=0 solves it for *every* n, hence no faithful minimum. `Nat.sInf ∅=0` creates a **defaulted different meaning**, on which the elementary rational square identity compiles. Agda gives a no-factorisation witness for losing existence. | Exposes definitional totalisation. Does not establish Appendix A's complexity-theoretic statements. |

### Fixed actual OpenAI code roots: reproduced, not guessed

- **Historical code author: OpenAI**, [fixed commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd](https://github.com/openai/NavierStokesAndEuler/tree/f9e8bc5b38b6e212696e8a30e3e91517af887bbd).
- [NavierStokes/SmoothFamilyTorusInverse.lean, lines 1059–1080](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/SmoothFamilyTorusInverse.lean#L1059-L1080): theorem `norm_derivativeWord_inverse_le` explicitly has two `SmoothFourierData.xJet (w.length + 5)` hypotheses. A word-dependent norm estimate does **not** automatically contain the omitted supremum over all words.
- [NavierStokes/R3/PressureFlux.lean, lines 576ff](https://github.com/openai/NavierStokesAndEuler/blob/f9e8bc5b38b6e212696e8a30e3e91517af887bbd/NavierStokes/R3/PressureFlux.lean#L576-L610): theorem `exists_uniform_actual_pressure_flux_bound` explicitly has `dissipationRoot(...)/R + 1/R²` multiplied by `cutoffL6^(1/2)+1`; source analysts identify this with an `A_R`-dependent RHS and a different proof route. **Do not** replace this historical commit with moving `main` or infer actual physical counterexamples.
- **Natural-language object:** OpenAI's *Finite time blowup for Navier–Stokes* manuscript, Eq. (8.19) and Eq. (10.19), as quoted and compared in the original BCH paper. The manuscript and historical Lean theorem source are different evidence objects.
- **Critic original:** BCH2026 paper; arXiv mirror, HTML, secondary overview and quotations are **one paper genealogy**, not independent replicas of the original paper's claims.

### Appendix A — actual theorem/dependency status

The paper's Appendix A proceeds through the following mathematically meaningful source sequence:

1. For `k≥9`, `B_e(n) := ∀ x∈N^k, p_e(n,x)≠0` and `d={e | ∃ n, B_e(n)}`. **Theorem A.3** claims `d` is Σ⁰₂-complete, reducing `NTOT={e | ∃ n, P_e(n) does not halt}` through computably encoded integer-coefficient polynomials. The source invokes nine-unknown DPRM and Post's theorem to conclude it is not decidable even by a Halting oracle.
2. For each integer `l≥2` and `k≥9`, the alternating-quantifier source family `B_e^(l)(n)` is given in (A.4a,b); **Theorem A.4** claims `d_l={e | ∃ n, B_e^(l)(n)}` is Σ⁰_l-complete, unbounded over finite levels.
3. The source connects that uniform family to the **SCI=∞** classification of this *presupposition-resolution problem*. The result is **not** a theorem that every concrete translation is undecidable, every AI model necessarily lies, or every Lean formal proof is unsound.

**DASHI implementation:** the Lean `LostInTranslationSCI` defines the precise `∃n∀x` shape, an existence-gated `Nat.find` construction, a true abstract decision-transport theorem along a many-one semantic reduction, and an abstract theorem of nondecidability **conditional on supplied effectiveness closure and an independently proved hard problem**. Agda `AutoformalisationBCH2026SCIInterface` requires genuine leastness and distinct Σ-level/DPRM/Post evidence, preserving `l≥2` and `k≥9`. It does **not** construct the nine-unknown polynomial representation, formal arithmetical hierarchy, completeness reduction or SCI infinite tower. Those are P0 **open**.

## Reuse, original genealogy and attribution rules

Existing **merged** DASHI owners reused rather than duplicated:

- `DASHI.Core.IntersectionalNonFactorability` — exact no-factorisation and post-composition theorem; do not attribute this mathematical proof to BCH/Crenshaw.
- `DASHI.Core.InterpretiveFormalisationCoreExact` — source translation / proof / interpretation distinction; do not promote interpretive role to equivalence.
- `DASHI.Foundations.ClaimScopeCertificateExact` — `notEstablishedHere` is not refutation.
- `DASHI.Core.AttributedSourceCore` and `DASHI.Core.SnowballAttributionProvenanceInvariantExact` — original source identities, roles and non-import of mathematical authority.
- `DASHI.Core.FirstImplementationTimestampExact` — first source-commit time is distinct from first typecheck and first kernel verified build. Chronology receipts must use actual Git SHA and UTC/local time.

Independently owned **unmerged** source donors: Agda #1255 and Lean #87 (source-bound Miller/Yan/Rodgers formalisation), Agda #1271 (periodic R735 local and small-data bounds), Lean #83 (time-series observation masking), and Lean #78 (math corpus ingress). They are conceptual inspirations only; no unmerged branch was copied into this new branch. The default `dashi_lean4` toolchain has `v4.35.0-rc3` while Mathlib source and manifest are `v4.28.0`; exact-head kernel acceptance remains pending, and this PR does not rewrite the global toolchain.

### Pareto / Ibrahim / snowball next steps

| Rank | Acceptance cut | What must NOT count |
|---|---|---|
| P0 | Exact-head `lake build AutoformalisationBCH2026` using the toolchain matching Mathlib 4.28, and focused Agda typechecks; record logs, SHA and proof declaration names | Static code scans, Python examples, CodeRabbit, or a different commit's CI |
| P0 | Source-formal theorem audit matrix for the historical commit; proof path and quantifier/norm/domain correspondence independently paid | Shared theorem names, coincident conclusion, paper reputation |
| P1 | Formal `Nat.sInf` default-vs-partial-presupposition with source-specific no-root proof (source-written in Lean) | Expanding algebraic identity while missing intended denominator witness |
| P1 | Genuine functional-analytic source (8.19) transfer: torus norms, all derivative words, 4 vs 5 jet assumptions, constants | Calling one extra input derivative harmless or treating jets as equal |
| P1 | Actual (10.19) analytic comparison: `A_R,B_R`, R, constants, a.e.-t vs ∀-t and pressure proof strategy | Inferring false PDE inequality from abstract RHS coordinates |
| P2 | SCI A.3/A.4: find exact prior repo computability/Diophantine hierarchy owners, implement uniform effective enumeration, nine-unknown DPRM, Post/strictness, and tower classification | Mere record flags or conditional reduction schema presented as Σ⁰_l completeness |
| P2 | Source-first severe falsification of attempted automatic translation, including withholding unsafe admission on missing witness | Reducing all fidelity to a single AI-score badge |

**Stop rules:** one original source per BCH paper/preprint/html mirror; do not re-attribute OpenAI code or historical Lean declarations to critics; do not treat a paper's *claim* of mismatch as a kernel result; do not treat a formal finite countermodel as a physical NS solution; maintain author/source/claim/implementation/validation as separate coordinates.
