# Monster 3B P5 — gauge-invariant original 12→78 operator intertwiner via the existing 729 Weil cube

**24 November 2026 | PR #1545 | M3B-L10A/B/C/L12R | endpoint first, no new certification lane.**

## Original sources and the genuine remaining object

The original \(\mathrm{MMV}(31)\) B-vacuum in the **actual** Monster module has dimension90 and the original literal corrected \(C^2\) decomposes it into dimensions \(12+78\). Genuine Monster group words \(D,E=CDC^{-1}\) have order3, preserve the 3B centre and, when they commute with the actual \(C^2\)-projector, give **original 12×12 and 78×78 modular matrices** on those two spaces. The source GAP/CTblLib match selected the faithful12 and **Nebe dual symmetric-square** 78, not the independent faithful78. The previous 729 donor is the exact source \`toe_cyclotomic_operator.compile_shape\` and \`Monster3BFiniteSchrodingerFullActionLawExact.agda\`, with the actual euler/point-projector and appropriate \(q=2v^\top Ev\). These are original source-producer contributions, NOT new representations built here.

The scalar from the 729 model is not a truly free order-three guess. For a source inner order-three \(g\), define its selected model Weil operator \(K_{g,s}\) (chosen \(\Delta^{-r}\) gauge; centre index \(s\in\{1,2\}\)). The previous source projective multiplication theorem gives \(\alpha_s(g,h)\) exactly and hence
\[
\boxed{\gamma_{g,s}I_{729}=K_{g,s}^3,\qquad
       \gamma_{g,s}=\alpha_s(g,g)\alpha_s(g,g^2).}
\]
This is now written directly to each phase of [the original 729 model receipt](../../scripts/monster3b_original729_weil_source_cocycle_weld.py) for both authentic words \(D\) and \(E\). Source group order3 then forces the actual complementary multiplicity matrix \(B_{g,s}\), *in the correctly matched Weil section*, to obey
\[
\boxed{B_{g,s}^3=\gamma_{g,s}^{-1}I_{90}},
\]
separately on original 12 and 78 block eigenspaces. The model \(\gamma\) is recorded in exact \(\mathbb Q(\zeta_3)\); reducing it at the marked prime \(31\) root5 or25 is a new, independent source compatibility check, NOT proof of a complex basis identification.

## Gauge-invariant **character** identity — no choice of cubic root

Let \(B_{12,g},B_{78,g}\) be original two source modular block matrices divided by the exact source-model B-vacuum coefficient \(\kappa_{g,s}\), and \(\gamma_g=K_g^3\). For a complex honest representation of the selected faithful12 and its dual-Sym²78, there is a scalar \(c_g\) satisfying
\[
A_{12,g}=c_gB_{12,g},\qquad A_{78,g}=c_gB_{78,g},\qquad c_g^3=\gamma_g.
\]
This scalar need not be known to prove a new **projective-gauge-invariant identity**. Since \(A_{12,g}^3=I\), the classical degree78 symmetric-square character formula is
\[
2\operatorname{tr}(A_{78,g})
=\operatorname{tr}(A_{12,g}^{-1})^2+
 \operatorname{tr}(A_{12,g}^{-2}).
\]
From \(B_{12,g}^3=\gamma_g^{-1}I\) obtain
\(B_{12,g}^{-1}=\gamma_g B_{12,g}^2\),
\(B_{12,g}^{-2}=\gamma_g B_{12,g}\).
After substituting \(c_g^3=\gamma_g\) and dividing by \(c_g\), all choices of cubic root cancel:
\[
\boxed{2\operatorname{tr}(B_{78,g})=
\operatorname{tr}(B_{12,g})+
\gamma_g\left[\operatorname{tr}(B_{12,g}^2)\right]^2.}
\]
No source-central \(\zeta\)/\(\zeta^2\) branch is discarded. The expression is valid over \(\mathbb F_{31}\) even when a particular cubic root is not selected inside that field. It tests the actual source **78 family vs source 12** more strongly than the dimension identity 12+78, although a character match alone does not imply matrix equivalence.

[Source original 12/78 projective character checker](../../scripts/monster3b_actual_order3_projective_sym2_weld.py) retains \(g=D,E\), phase \(s\), \(\kappa_{g,s}=0\) as a genuine obstruction, original \(C^2\) eigenspace source and exact canonical Monster word provenance. It checks both cubes and the 78 trace. The bounded faithful12 coefficient inversion \(\mathbb Z[\zeta_3]\to\mathbb F_{31}\times\mathbb F_{31}\) is only permitted if the original two phase word/source identities agree; it never resolves the full 6Suz scalar cochain from one order3 trace.

**Independent local algorithmic fixture:** six possible \(\mu_6\) cubic phases \(c_g\in\{1,\zeta,\zeta^2,-1,-\zeta,-\zeta^2\}\) were tested directly in Python on a 12+78 eigenvalue construction. All six satisfy the exact formula, including both possible \(\gamma=\pm1\). A deliberately corrupted 78 trace fails. This is a finite **model verification**, NOT a fresh original MMV31 workstation observation.

## Stronger **operator** construction — simultaneously original D,E

The cubic relation actually gives the **entire target 78D matrix**, not merely its trace. The dual action of an ordinary faithful12 matrix is \((A_{12,g}^{-1})^\top\), so
\[
c_g B_{78,g}\sim
\operatorname{Sym}^2\left((c_gB_{12,g})^{-T}\right).
\]
The factor \(c_g\) cancels because \(c_g^3=\gamma_g\), giving
\[
\boxed{B_{78,g}\sim \gamma_g^{-1}
     \operatorname{Sym}^2((B_{12,g}^{-1})^\top)
   =\gamma_g\,\operatorname{Sym}^2((B_{12,g}^2)^\top).}
\]
The last equality uses \(B_{12,g}^{-1}=\gamma_gB_{12,g}^2\) and avoids matrix inversion on 12D altogether. All exponents/signs are exact; the dual vs primal Sym² distinction matters because of the common centre phase. For \(g=D,E\), form
\(T_g=\gamma_g\operatorname{Sym}^2((B_{12,g}^2)^\top)\) using the actual projected 12D block in the *same signed source phase*. The true algebraic objective is a **single** invertible transport \(F_s\) satisfying
\[
\boxed{F_sB_{78,D}=T_DF_s,\qquad
       F_sB_{78,E}=T_EF_s.}
\]
This prevents cheating by independently conjugating the two generator matrices into the desired form.

[New constructive original 78↔Sym² operator source](../../scripts/monster3b_actual_projective_sym2_intertwiner.py) constructs \(\operatorname{Sym}^2\) on the actual 78 monomial indices \((i,j),0\le i\le j<12\). It avoids the naive 6084-unknown simultaneous Kronecker kernel. Search a small deterministic family \(h(D,E)=aD+bE+cDE\) for a **simple shared eigenvalue \(\lambda\in\mathbb F_{31}\)** of original and derived 78D operators. Its one-dimensional source/target eigenspaces select a candidate map up to scale. Starting at those source/target eigenvectors, propagate the SAME finite words in D,E, keeping only independent source vectors by incremental exact \(\mathbb F_{31}\) elimination. Once 78 vectors are spanned, set
\[
F=(\text{78 target columns})(\text{78 source columns})^{-1}
\]
and verify all \(78^2\) entries of BOTH intertwining equations, invertibility and the inverse equations. This constructs an actual finite-field linear operator when successful, not just a matching character or a generic recognition socket. It is not a proof of global \(6.\mathrm{Suz}.2\) equivalence unless the full literal standard-generator and outer relations are supplied.

**Independent local algorithm test completed:** a synthetic degree12 source with two genuinely different order-three generators, plus a \(78D\) dual-Sym² target, a hidden random invertible \(78D\) change of basis and a nontrivial \(\gamma_D=-1\), was used to test this algorithm independently in local NumPy. It recovered \(F\) with a full 78-dimensional cyclic span, maximum 12 letters in the generated source words, and exact simultaneous D/E equations. A wrong 78 generator was rejected. This test establishes the algorithm works on at least one original-shaped noncommuting example; the actual original Monster operator result remains unexecuted in this environment. The repository script is committed and has GitHub readback, not falsely claimed a user-workstation acceptance result.

## P0–P6 / remaining exact mathematical source obligations

| Lemma | Mathematical delivery now paid | Real source-specific endpoint still open |
|---|---|---|
| **M3B-L10A** | original \(\mathbb Q(\zeta_3)\) bounded character inverse and direct order3 729 model scalar \(\gamma_{g,s}\); no Steel/Magma mathematical prerequisite | pair original signed MM phases/source 6Suz word globally; character candidates need honest section |
| **M3B-L10B** | existing 729 kernel, vacuum \(\kappa_{g,s}\), D/E projective cocycle, actual-source modular 12D/78D cubic equations and inverse 90D projective compensation; exact R⁷ constraint | genuinely identical source MM 729 E polarization, global normalizer cocycle and char0 Hom transport |
| **M3B-L10C** | original 12→dual Sym²78 full **operator** functor and new constructive **simultaneous source D/E modular 78D intertwiner algorithm**, not an independently guessed 78D action | actual original MMV31 receipt needs to satisfy/generate \(F\); characteristic-zero faithful12 standard generators and same-Hom 78 transport still open |
| **M3B-L12R** | original Monster \(R^7=z_{3B}\), model unique order7 rephase and complementary 90D signed residual; original literal C4D classification algorithm | selected original MM word class4D result, full phase-inverting outer actual operators and 6Suz.2 group relators |

**Producer→consumer:** original AtlasRep 2.Suz:2 matrices + TOE compiler and 729 point projector → actual mmgroup original E/corrected C,D and signed R7 → genuine MMV31 phase-specific 90/12/78 B-vacuum blocks → [source Weil cubic](../../scripts/monster3b_original729_weil_source_cocycle_weld.py) → [projective 12→78 trace/cubic identity](../../scripts/monster3b_actual_order3_projective_sym2_weld.py) → [original two-word operator intertwiner compiler](../../scripts/monster3b_actual_projective_sym2_intertwiner.py) → actual Ibrahim \(\operatorname{Hom}_E(H_s,W_s)\) 12/78 and Paper10. Retain zero mode/vacuum, signed centre, diagonal class20 kernel versus extraspecial centre, source phase ζ/ζ², actual word order, \(\mathbb F_3/\mathbb F_{31}/\mathbb Q(\zeta_3)\) fields, and explicit source versus chosen model gauges. **No user workstation run or Magma is a prerequisite for this new mathematics or implementation.**
