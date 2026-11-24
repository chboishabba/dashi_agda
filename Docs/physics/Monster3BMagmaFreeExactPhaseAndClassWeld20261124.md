# Monster 3B — P5 Magma-free exact character, literal 4D and paired-phase Monster action

**24 November 2026 · PR #1545 · mathematical endpoint-first · no further user run is a prerequisite for this derivation.**

This cut responds to the user request **stop deferring substantive work to app execution**. We must distinguish (a) mathematics proved from existing source results, (b) committed original-source algorithms that could be evaluated when actual MM data is accessible, and (c) historical numerical Monster claims that are NOT observed merely because a program has been written. Existing user-executed input: canonical corrected Monster C,D, exact R^7=z_{3B}, rank90 actual MMV31 B-vacuum, C² modular eigenspaces of dimension12/78 and D modular sandwich; genuine full-class GAP/CTblLib selected faithful12 and Nebe dual-Sym²78. Steel original ordinary source file is cached on the user's machine but raw bytes and Magma executable are unavailable in this assistant runtime.

## 1. L12R literal 4D is accessible WITHOUT Steel, Magma or 196884D traces

The published original source fusion gives **source 4D**, exact 2.Suz.2 class5→6.Suz.2 class9→main54→MN3B33→Monster class10. However the actual MM Hit0 C word has only been proved to have order4 and C² relations, not that it belongs to that source class.

The mmgroup API has the actual Monster character method **\`MM.chi_powers()\`**, documented at <https://mmgroup.readthedocs.io/en/latest/api.html#mmgroup.MM.chi_powers>. For an actual Monster group word whose half-order power is a **2B involution**, it is usually able to recover its genuine **196883-dimensional** Monster character \(\chi_M(C)\) and \(\chi_M(C^2)\) quickly, using source group conjugation rather than a full 196884-dimensional matrix trace. This is exactly the case to attempt for the corrected order4 word with original source 4D target (source 4D squares to2B), but the method is probabilistic and can legitimately return a partial/missing value.

**New actual same-word classifier:** [\`scripts/monster3b_literal_mm_4d_character_class.py\`](../../scripts/monster3b_literal_mm_4d_character_class.py) reads the previously **authentic full Monster corrected C** from \`mmgroup_canonical_cover_hit0.json\`, computes \(\chi_{196883}(C)\) and the square trace using \`chi_powers\`, and generates a GAP class filter on the **actual original** \`CharacterTable("M")\`. It compares **order4 + degree196883 character value + square character** against all Monster classes, demands a **unique** match, and records a literal class-4D result only if the unique class is the source position10 labelled \`4D\`. Missing traces, multiple classes and a contrary class remain explicit negative/unknown source outcomes. It never equates the already-paid **source** class with an **actual MM word** by assumption. No Magma dependency and no new 28-hit quotient search.

## 2. Exact single-prime reconstruction of ALL degree12 Q(zeta3) character values

Let \(G=6.\mathrm{Suz}\), \(V\) the already source-selected faithful ordinary degree12 representation (GAP Irr153 or154), and \(\chi_V(g)\) its character. The faithful central order-three element has scalar \(\zeta_3^{\pm1}\), and the character field is \(\mathbb Q(\zeta_3)\) (original Steel character-field degree2 and Schur index1). As an algebraic integer, every character value belongs to \(\mathbb Z[\zeta_3]\): uniquely
\[
\boxed{\chi(g)=a+b\zeta_3,\qquad a,b\in\mathbb Z.}
\]
Finite-group representations are unitarizable, hence for the two embeddings \(|\chi(g)|\le12\) and \(|\sigma\chi(g)|\le12\). Therefore the field norm obeys
\[
\boxed{N(\chi(g))=a^2-ab+b^2\le 12^2=144.}
\]
Completing the square in either variable shows \(3a^2/4\le144\), \(3b^2/4\le144\), giving the integer bounds
\[
\boxed{|a|\le13,\quad|b|\le13.}
\]

The prime \(31\) splits in \(\mathbb Q(\zeta_3)\) with two different marked reductions \(\zeta_3\mapsto5\) and \(\zeta_3\mapsto25\). Suppose a **single actual inner group word** \(g\) has genuinely normalized multiplicity traces \(t_5,t_{25}\) in the two marked 12D constituents (same source words, correct 729-Weil cochain and central orientation). Then
\[
t_5=a+5b\bmod31,\qquad t_{25}=a+25b\bmod31.
\]
The distinct roots give
\[
\boxed{b=(t_5-t_{25})(5-25)^{-1}\bmod31,\quad a=t_5-5b\bmod31.}
\]
Each of \(a,b\) has size at most13, so its centered residue in \([-15,15]\) is the **unique integer coefficient**, not merely a modular guess. An exhaustive exact local calculation enumerated **517** integer pairs satisfying \(a^2-ab+b^2\le144\) and verified **517/517** recover faithfully with **zero collisions**. **No Magma and no Steel matrix entries are needed for this theorem**.

**Boundary:** the actual already-reported \(\mathrm{MMV}(31)\) matrices from the B-vacuum are \(\overline L_g=k_0(g)L_g\), with as-yet unknown source-specific **Weil-vacuum coefficient \(k_0(g)\)**. We must normalize the same physical word in BOTH phase branches coherently before calling \(t_5,t_{25}\) ordinary character traces. An unnormalized vacuum sandwich is NOT automatically a character value. This is the central unsolved phase/group gauge, now reduced to a finite scalar problem rather than a missing arbitrary 90D matrix.

## 3. Actual modular order-three scalar options are finite and explicit

For actual \(D\) and \(E=CDC^{-1}\), the source Monster group orders satisfy \(D^3=E^3=1\). If \(\overline L_g=k_gL_g\) with a genuine order3 linearized \(L_g\), then
\[
\overline L_g^3=k_g^3 I.
\]
Once the observed genuine MMV31 12D sandwich has scalar cube \(s_g\), \(k_g\) lies among at most three cubic roots of \(s_g\) in \(\mathbb F_{31}\). For both phases, there are at most nine candidate scalar pairs. Filter each pair by (i) ordinary \(\chi(g^2)=\overline{\chi(g)}\), (ii) norm bound \(a^2-ab+b^2\le144\), and (iii) nonnegative integer eigenvalue multiplicities
\[
n_{\zeta^2}=\frac{12-a-b}{3},\quad
n_1=n_{\zeta^2}+a,\quad n_\zeta=n_{\zeta^2}+b.
\]
The implemented original-data consumer [\`scripts/monster3b_quadratic12_character_lift.py\`](../../scripts/monster3b_quadratic12_character_lift.py) **enumerates all surviving scalars**, records the exact possible \(a,b\), and does NOT invent a single choice when the true group-cover cocycle is still unresolved. A local synthetic order3 example with eigen multiplicities (5,4,3) and vacuum scalars (7,9) leaves exactly THREE legitimate rephasing choices, of which the genuine \((a,b)=(2,1)\) is included. This correctly demonstrates why a single order3 word alone cannot fix the global source gauge.

## 4. Two real Monster modular primes and projective multiplication cocycle

The existing \`mmgroup\` package documents source \(\mathrm{MMV}(p)\) for \(p=3,7,15,31,127,255\); see <https://mmgroup.readthedocs.io/en/latest/api.html>. The source \(\mathbb Z[1/2]\) 196884-dimensional Monster module is represented in either \(p=31\) or \(p=127\). **Both are coprime to the actual \(|6.\mathrm{Suz}|=2690072985600\)**, so restricting these modular actions to the selected ordinary source subgroup is semisimple (Maschke); this does NOT assert the entire mod31 Monster representation is semisimple. Both primes split the order-three centre: \(p31:\zeta\mapsto5,25\); \(p127:\zeta\mapsto19,107\). The \(|a|,|b|\le13\) bound makes either split prime sufficient for a correctly normalized 12D two-phase character value, while their two independent reductions provide stronger source cross-checks once the actual word and Weil gauge are attached.

The existing genuine-source [\`scripts/monster3b_actual_mmv31_hom_projector.py\`](../../scripts/monster3b_actual_mmv31_hom_projector.py) now supports \`--prime 31|127\`, \`--opposite-phase\` and phase-specific receipt names without changing the already-reported source rank90 (p31 ζ5) result. For the literal signed-Schreier inner generator pair \(D,E=CDC^{-1}\) it computes genuine vacuum sandwich matrices \(D_0,E_0\), their authentic \(\mathrm{MMV}(p)\) products \(DE_0,ED_0\), and compares
\[
\boxed{E_0D_0=\alpha(D,E)(DE)_0,\quad
D_0E_0=\alpha(E,D)(ED)_0}
\]
using the **actual mmgroup RIGHT vector action and coefficient-column matrices**. This captures the original finite-field Weil projective 2-cocycle directly from the original Monster module, not from a synthetic group-algebra model. Unknown or nonscalar mismatches are recorded as such, not silently coerced. The already-existing original full-Monster \(R(C,D)^7=z_{3B}\) then provides an independent signed central-cover relation for the eventual cochain weld.

## 5. Actual *outer* phase transport is now a source operation too

The new [\`scripts/monster3b_mm31_outer_phase_pair.py\`](../../scripts/monster3b_mm31_outer_phase_pair.py) consumes both **original** \(\mathrm{MMV}(31)\) marked ζ5/ζ25 source receipts. It reconstructs each of the 90 actual Monster modular vectors from the saved **original E basis probes** and exact pivot rows, checks literal E-centre/6-B-vacuum equations, then computes
\[
U_{+-}=P_{B,\zeta^{-1}}\rho_W(C)|_{B,\zeta},\qquad
U_{-+}=P_{B,\zeta}\rho_W(C)|_{B,\zeta^{-1}}.
\]
These are actual Monster-origin \(90\times90\) **modular** maps between the two original marked sectors, not abstract guessed matrices. It computes their ranks, projected \(12/78\) eigenspace blocks and, with the **actual** \(J_\pm=\rho(C^2)\) vacuum matrices, compares
\[
\boxed{U_{-+}U_{+-}=\beta_+J_+,\quad
U_{+-}U_{-+}=\beta_-J_-}
\]
and retains the Weil coefficients \(\beta_\pm\). A source complex 12/90 outer lift and the literal class4D identity still require their proper original field/word attachment; the exact modular operation is meaningful by itself.

The [P5 coordinator](../../scripts/run_monster3b_p5_endpoint.py) now contains independent **literal class4D** source recognition (no Magma), optional two-phase MMV31 and exact bounded ordinary12 *candidate* reconstruction, optional true MMV127 and the paired actual modular outer C stage. \`--reuse-mod31-plus\` can retain the already user-paid 90D ζ5 original source receipt rather than repeating it.

## 6. Exact remaining mathematical lemmas and existing producers/consumers

| Lemma | Paid now without Magma | Open exact source/math weld | Producer→consumer |
|---|---|---|---|
| **M3B-L10A** | Proof exact 12D ordinary character values recover from two marked good-prime reductions with \(|a|,|b|\le13\); full finite cubic candidate enumeration; already Steel original source cached | Actual scalar/cochain normalization to unique ordinary character on SAME real group words and source GF31↔Qζ orientation; literal original Steel matrices only if numeric characteristic-zero basis requested | actual mmgroup MMV31 both marked phases + GAP original 12 character row → selected ordinary faithful12 |
| **M3B-L10B** | existing actual original modular 90D vacuum split; NEW second source inner generator \(CDC^{-1}\), literal D/E vacuum multiplication 2-cocycle, optional independent p127 | Solve 729 Weil phase and group/word coherence globally, obtain source equivariant char0 12D Hom isomorphism (or rigorous algebraic lift); do NOT infer from single modular sample | Monster actual group words + original 729 finite Weil → GAP selected 6Suz irreps/real Hom |
| **M3B-L10C** | exact characteristic-zero dual Sym²78/90 functor and 210-class character identity already solved, plus bounded mod31 route to original 12 character | Original source ordinary 12D matrices if requesting numeric complex operators; no independent 78D unknown | faithful12 source+Nebe dual-Sym²78 → 90 |
| **M3B-L12R** | NEW literal MM \(\chi_{196883}\)→GAP unique 4D class classifier; NEW paired actual modular outer \(C\) action and square \(\beta\); original corrected C,D, \(R^7=z\) source already observed | Source actual \(\chi_{196883}(C)\) receipt not yet run in assistant runtime, actual 4D identification not yet reported, compatible outer ordinary Weil scalar/standard group-word map still open | mmgroup \`chi_powers\`, original Monster 4D table class10, actual \(\mathrm{MMV}(31)\) paired phase → original 6Suz.2/Monster outer and Paper10 |

**Standing invariant:** preserve original K class20 vs extraspecial z centre, source 4D class vs literal MM word, original ζ sign, rank90 \(12+78\) and full signed \(R^7=z\) residual. The original character-field equivalence is NOT an automatic literal characteristic-zero Monster Hom matrix. **No Magma executable, source GModule or user workstation rerun was necessary to derive the mathematics here.** The new source scripts are written and GitHub-source readback can establish their presence, but no claim is made they executed with mmgroup/GAP on the author's workstation or passed an authentic new Monster source gate.
