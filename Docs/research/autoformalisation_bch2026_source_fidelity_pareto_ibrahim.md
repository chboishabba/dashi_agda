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


## 27 October donor discovery: Cameron Freer's actual Hilbert10 Lean spine

A focused 2026 literature and repository search found **Cameron Freer**,
[**Hilbert's tenth problem in Lean**](https://github.com/cameronfreer/hilbert10)
(original software, Apache-2.0, `CITATION.cff` version **2.4.0**).
This was **not** retrieved as an independent preprint affirming BCH2026,
and was not written by BCH, OpenAI or DASHI.

The **actual source files were fetched**, not simply a search-result snippet:

- [`Hilbert10/DPRM.lean`](https://github.com/cameronfreer/hilbert10/blob/main/Hilbert10/DPRM.lean)
  attributes the code to Cameron Freer. It contains
  `Hilbert10.REPred.dioph` and
  `Hilbert10.dioph_iff_rePred`, the semantic equivalence of
  Diophantine and recursively enumerable predicates on finite
  natural-number tuples. Freer's README reports the public spine
  typechecks and is axiom-audited; **we have not independently run
  its kernel build at a pinned SHA**.
- [`Hilbert10/Endpoints.lean`](https://github.com/cameronfreer/hilbert10/blob/main/Hilbert10/Endpoints.lean)
  contains `natSolvable_re_complete` and
  `not_computablePred_natSolvable`, as well as the integer-form
  endpoints. **Those are actual original donor declarations**,
  not BCH's `Sigma^0_2` minimum-presupposition theorem.
- [`Hilbert10/Universal.lean`](https://github.com/cameronfreer/hilbert10/blob/main/Hilbert10/Universal.lean)
  contains `exists_universal_mvPolynomial`:
  **`∃ k U, ∀ e x y, ... ↔ ∃ z : Fin k → Nat, U(e,x,y,z)=0`**.
  The universal `k` is fixed *before* inputs, which is stronger
  than merely choosing a different polynomial for every program.
  **There is nevertheless no source claim or theorem conclusion
  that `k≤9`**. The nine-unknown refinement BCH Theorems
  A.3/A.4 use thus remains a separate mathematical proof dependency.
- `Hilbert10/lean-toolchain` is **v4.35.0-rc4**, and its
  `lakefile.toml` pins Mathlib commit
  `d3739f06187591e81887886ca767b6a2dc1416ea`.
  **dashi_lean4** pins root Lean **v4.35.0-rc3** but Mathlib
  **v4.28.0**. We did **not** modify either original lockfile,
  pull external files into DASHI, or assert binary/library
  compatibility.

The companion Lean `LostInTranslationSCI.lean` adds an **exact
finite logical gate**:
`HasAtMostNineWitnesses R -> HasSomeWitnessCount R`, whereas
the reverse does **not** hold for arbitrary witness-count properties
(e.g. `R k := k=10`). This is *not* a claim that Freer's
polynomial requires ten variables: it proves that a source theorem
with an existential witness count cannot alone pay a uniform
nine-variable bound. It is a proof-obligation discriminator for
auditing a proposed DPRM reuse, and independently retains Freer's
source authorship.

**Updated Pareto/Snowball decision:** the *general semantic DPRM*
foundation no longer needs to be written from scratch if the
independent Freer library is accepted and ported carefully.
The remaining true frontier is (i) a compatible exact-head
mathlib/Lean import, (ii) either a faithful nine-unknown refinement
or a replacement construction proving BCH's `k≥9`
claim, (iii) the NTOT-to-`d` reduction and `Sigma^0_l`
alternating-quantifier hierarchy/Post theorem, and (iv) the
source's explicit SCI tower conclusion. A general H10
undecidability theorem alone does **not** imply A.3/A.4, nor
do different Mathlib versions magically identify theorem types.


## Primary-source Appendix completion audit (A.3/A.4/A.5/A.6, Oct 27)

Re-read [original arXiv HTML v1, Appendix A.2](https://arxiv.org/html/2610.08144v1).
Three *different* statements must remain typed separately:

1. **Theorem A.3** asserts the fixed `k>=9` natural-variable
   **`Sigma^0_2` completeness** of `d={e | ∃ n∀x p_e(n,x)!=0}`.
   The new Lean `LostInTranslationNineVariables.lean` has now proved
   the exact **logical reduction**
   `(∃n, ¬Halts(e,n)) <-> (∃n,∀x:Fin9 Nat,Q(e,n,x) != 0)`
   *conditional on* `∀ e n, Halts(e,n) <-> ∃x,Q(e,n,x)=0`.
   This cannot be upgraded to an **effective many-one reduction**
   until a true nine-unknown integer polynomial family, effective
   coefficient enumeration and computable index transformation are
   supplied. Universal polynomial existence with unspecified arity
   is insufficient.
2. **Theorem A.4** claims `Sigma^0_l` completeness at each
   `l>=2, k>=9`. Its proof alternates quantifiers and, at the last
   block, replaces the final computably enumerable relation by
   an **existential or universal nine-variable polynomial block
   depending on parity**, without increasing the alternation depth.
   Coefficient-level equality and the partial-recursive index
   selector are independently required. Source author credit belongs
   to BCH; classical DPRM and hierarchy/recursion authors retain
   their original theorems. Our typed debt interfaces are not an
   effective-presentation proof.
3. **Corollary A.5** states a *different* exact fixed-level fact:
   `SCI_A(chi_d_l)=l` **for each** `l>=2`. Only then does §A.2.1
   conclude that the **uniform problem across all finite levels**
   has SCI `+infinity`. It is incorrect to say *each individual*
   fixed-level problem has infinite SCI. Companion Lean
   `fixed_level_sci_unbounded_of_corollary_A5` formalises the
   elementary deduction `∀h∃l>=2, h<SCI_l` from explicit
   hypotheses `SCI_l=l`. The theorem
   `no_uniform_finite_height_if_all_fixed_levels_restrict`
   additionally requires that an alleged uniform method of height
   h would bound every fixed-level restriction by h. We have
   **not formalised the actual SCI towers** or proved those
   hypotheses, hence have **not kernel-proved SCI=infinity**.
4. **Remark A.6** distinguishes **NATURAL-number** witnesses
   (source use `k>=9`) from **INTEGER** unknowns. It references
   an integer ten-unknown result; that is a different coefficient/
   witness domain, *not* a nine-variable Nat DPRM theorem.

### Original roots behind the nine-vs-ten count

- **James P. Jones (1982)**, [*Universal diophantine equation*,
  Journal of Symbolic Logic 47(3), 549-571,
  DOI 10.2307/2273588](https://doi.org/10.2307/2273588).
  Original universal representation precursor, separate from
  BCH2026's argument and Freer's software implementation.
- **Yuri Matiyasevich** and the
  Davis–Putnam–Robinson–Matiyasevich tradition: classical original
  representation theorems, not 2026 DASHI contributions.
  The exact nine-Nat-witness bound is a *specific theorem* with
  a separate arity account; generic semantic DPRM does not show it.
- **Zhi-Wei Sun (submitted 2026-09-01)**,
  [*Ten unknowns for Hilbert's tenth problem over the integers*,
  arXiv:2609.01594](https://arxiv.org/abs/2609.01594).
  The author **claims** integer-solvability undecidability with
  ten unknowns, improving an eleven-unknown record. An unrelated
  low-tier AI-referee note questions a lemma, and no independent
  original-proof verification was performed here. This is a
  **contested source root**, NOT a repaired/more restrictive
  theorem that can be silently applied to the nine-Nat-variable
  BCH claim.

These new bibliography rows and their distinct *source roles* are
typed in `DASHI.Foundations.AutoformalisationBCH2026Sources`.
The original source's publication, derivative reprints, reviewer
claims, Lean source commits and successful kernel builds remain
different evidence coordinates.

### Exact boundary at end of this cut

Actual GitHub source declarations were written for selected
Examples 2.1, 2.2, 3.1, 3.3, 4.3, the finite `∃n∀x` shape and
the A.3 nine-variable logical equivalence, the additional witness-
arity acceptance obstruction, and the A.5 unbounded-level deduction.
The final **unpaid** proof roots are the numerical-nine-variable
polynomial construction (or an independently source-equivalent
replacement), effective enumerations and `NTOT` many-one
completeness, the `Sigma_l` quantifier hierarchy/Post theorem,
and the SCI tower/restriction semantics themselves. Stop
promoting source-written lemmas beyond those visible result types.


### Source §3.3 and §3.4: separate Euler prediction versus witnessed NS mismatch

The BCH authors explicitly **do not** conduct the same detailed
proof-by-proof Euler autoformalisation audit. In §3.3 they predict
a high likelihood of substantial Euler mistranslations based on
preliminary examinations. That is a **prediction/hypothesis**, not
a verified instance comparable to the paper's fixed Navier–Stokes
(8.19)/(10.19) discrepancies. No DASHI module treats the Euler
prediction as an already observed source-code counterexample.
The paper's §3.4 observes that proof search which accepts *any*
kernel-proof of the target statement may intentionally repair or
replace the reasoning from a bad original proof. A backward natural
language paraphrase of the Lean result also needs its own independent
translation-fidelity receipt, rather than automatically repairing
the proof-method discrepancy.

The pressure example's original notes also separate two legitimate
claim types: a bound true for **almost every** t versus one true for
**all** t once source-proven continuity upgrades the assertion.
They are not identical raw statements; a valid continuity upgrade
must be linked to the same quantity and physical source. The
simple numerical independent-coordinate counterexample in Lean #88
does not model actual Navier–Stokes pressures and must never be
promoted as a counterexample to either field inequality.
