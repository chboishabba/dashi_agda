# Monster 3B / GAP — exact double-C3 Fourier descent, original class-20 selector, and signed phase residual

**24 November 2026 · PR #1545 · mathematical endpoint-first GAP source cut.**
Use the attached Langlands signed-residual analogy **only as motivation**: it is NOT a Monster/Langlands group homomorphism, not evidence from Langlands, and not a P-vs-NP theorem. This note works strictly with the ORIGINAL Barraclough–Wilson/Bray–Wilson **Monster 3B** character-table objects and source GAP producer \`scripts/monster_3b_suzuki_main_quotient_match.g\` (existing on \`master\`). The mathematical result is standard complex character/Clifford theory applied to this already-identified normal kernel, not a newly postulated 90D representation.

## 1. The two order-three objects are NOT interchangeable

The source main group \(\widetilde N=3^{1+12}:6.\mathrm{Suz}.2\) has:
- \(Z_E=Z(E)=\langle z\rangle\cong C_3\), identified by the **two-element order-three class** lying in \(\ker(\text{main}\to6.\mathrm{Suz}.2)\). This is the genuine original 3B-phase centre.
- \(K=\langle k\rangle\cong C_3\), the distinct **normal diagonal quotient kernel**, source \(\{1\}\cup\text{main class 20}\), lying in \(\ker(\text{main}\to MN3B)\). This is NOT the original \(z\) and does NOT produce the same Fourier mode.

The published \(\widetilde N\to N=MN3B\) kills K, **not** \(Z_E\). Outer conjugation interchanges each of \(k,k^{-1}\), and likewise the two nontrivial \(z\)-eigenphases. The original full main character table reports one class value for \(\{k,k^{-1}\}\), not an arbitrary separately marked value for \(k\).

## 2. A general one-class irreducible character theorem

Let \(V\) be an irreducible complex \(\widetilde N\)-module, \(\chi\) its ordinary character, \(d=\chi(1)\), and let K be that actual normal order-three kernel with \(k,k^2\) conjugate. Define
\[
\Pi_K=\tfrac13(1+\rho(k)+\rho(k^2)).
\]
K is normal, hence \(\Pi_K\) is CENTRAL in \(\mathbf C[\widetilde N]\). By irreducibility, \(\Pi_K=0\) or \(\Pi_K=I\). Using \(\chi(k)=\chi(k^2)\),
\[
\operatorname{rank}\Pi_K=\frac{d+2\chi(k)}3\in\{0,d\},
\qquad\boxed{\chi(k)\in\{d,-d/2\}.}
\]
Furthermore \(\boxed{V\text{ descends to }N\iff \chi(k)=d}\). This determines descent **from one original main-table class**. A negative result is an exact nonzero diagonal-central-phase obstruction, not a failed numerical test.

For the published Barraclough–Wilson \(1458\)-Heisenberg times outer \(24=12+12\) split and \(156=78+78\) split, for the **Monster-selected** degree-12 and degree-78 pairs, the source full-class \(MN3B\) matcher requires one descended and one non-descended component. Other scanned degree-78 families may have no K-trivial component (or no unique one) and must be *skipped*, not treated as a fatal counterexample to the theorem. The exact class-20 alternatives must therefore be
\[
\begin{array}{c|rr}
\text{main irreducible degree}&\text{descended }\chi(k)&\text{rejected }\chi(k)\\
17496&17496&-8748\\
113724&113724&-56862
\end{array}
\]
These are *theorem-forced candidate values*, not fabricated runtime CTblLib output.

The original GAP producer now derives this dichotomy directly from **source class 20**, compares it against the original full-character MN3B descent (which remains a separate necessary same-object check), and records original source positions/traces. No \`PossibleClassFusions\`, arbitrarily chosen 78-family, guessed \(12a/78a\) assignment or full-group MM word is introduced.

## 3. SECOND source C3 projector: real 3B phase, not quotient K support

On the **same** selected descended main-module \(V_d\), the original extraspecial centre \(z\in Z_E\) is retained in N, and its two nontrivial phase eigenspaces are exchanged by the outer element. In the two selected original paired-character families, the zero/identity eigenphase of \(z\) is absent. Therefore
\[
\boxed{\chi_d(z)=-d/2,\qquad
\dim V_{d,\zeta}=\dim V_{d,\zeta^2}=d/2.}
\]
For the two genuine selected main irreducibles the **double central signature** is
\[
\boxed{(\chi_{17496}(k),\chi_{17496}(z))=(17496,-8748),}
\qquad
\boxed{(\chi_{113724}(k),\chi_{113724}(z))=(113724,-56862).}
\]
This is an exact **commuting-square type distinction**: K-invariants are ALL of each selected representation, while the actual 3B trivial phase is ZERO. Confusing the killed diagonal-kernel \(C_3\) mode with the actual \(3B\) zero mode changes the mathematical object.

## 4. Marked, signed phase transport: full outer characters are only the even quotient

For any complex representation \(W\) of an inertia group \(I=C_N(z)\), the marked phase projectors are
\[
P_s=\tfrac13(1+\zeta^{-s}\rho(z)+\zeta^{-2s}\rho(z^2)),\quad s=0,1,2.
\]
Their even and odd components under the true outer inversion are
\[
\boxed{P_1+P_2=\tfrac13(2-\rho(z)-\rho(z^2)),}
\quad
\boxed{P_1-P_2=\tfrac{\zeta^2-\zeta}{3}\bigl(\rho(z)-\rho(z^2)\bigr).}
\]
An outer element with \(ozo^{-1}=z^{-1}\) fixes the first and NEGATES the second. No unmarked outer-paired character can canonically name which phase is \(\zeta\) and which \(\zeta^2\); **but the marked matrix operator \(P_1-P_2\) survives as signed orientation data**. It is not the centre-zero projector \(P_0\), not the class-20 K projector and not an element of the ordinary outer-invariant character ring. A change \(z\leftrightarrow z^{-1}\) swaps the sign and the labels together. Do not claim that a full \`MN3B\` class-sum alone selects this oriented odd operator.

For a phase-preserving \(g\), if \(\chi_W(z^jg)\) is available in the MARKED inertia model, then
\[
\chi_{W_s}(g)=\tfrac13\sum_{j=0}^2\zeta^{-sj}\chi_W(z^jg).
\]
The *original* complete main/MN3B class fusion and centralizer/inertia table remain the producer for that action; class **positions** in the outer table do NOT by themselves specify a chosen \(z\) generator or class product \(z^jg\).

This is the only useful part of the attached S3/Langlands example for Monster 3B: preserving the signed odd residual under an involution, **not** transferring Langlands conductor or computational complexity claims.

## 5. The 12/78 central phase must be the SAME — but do not throw away the Weil scalar

Let the original source 729-extension \(\psi_s\) act by \(\psi_s(z)=\zeta^s\) and \(\psi_s(t)=\zeta^{u_s}\), where t is the central order-three Suzuki scalar in the same original split source. The multiplicities \(U_{12},U_{78}\) have Suzuki t phases \(\zeta^{k_{12}},\zeta^{k_{78}}\); the original paid K is generated by \(zt^\epsilon\) for \(\epsilon=\pm1\). Source K descent is
\[
s+\epsilon(u_s+k_{12})\equiv s+\epsilon(u_s+k_{78})\equiv0\pmod3.
\]
Hence \(\boxed{k_{12}\equiv k_{78}\pmod3}\): the phase-preserving \(12a/12b\) and \(78a/78b\) choices are a **linked pair**, subject only to simultaneous phase inversion as a gauge. The existing GAP full-character matcher computed \`common729C3MatchedPairs\` but previously allowed 0, 1 or 2. Once both source pair families genuinely descend through the **same K using the same 729-extension**, this theorem requires **exactly 2** matching conjugate pairs. The native producer now enforces it, without choosing which original member is 'a' or 'b'. This is a mathematically stronger branch condition; runtime acceptance against actual original GAP is still unobserved in this session.

## 6. 78 family remains a SOURCE SELECTION, not a fixed pre-assumption

The original GAP producer correctly scans ALL degree-78 outer families, then matches selected \(113724\)-dimensional constituents by the exact full \(MN3B\to M\) restriction. Do NOT change this to faithful-78 preselection. The selected 78 still has central \(C_2\) signature:
\[
\chi_{12\oplus78}(t_2)=\begin{cases}-90&78\text{ faithful to }6.\mathrm{Suz},\\+66&78\text{ the Nebe }\operatorname{Sym}^2(12)\text{ or dual family},\end{cases}
\]
using the existing source \(6.\mathrm{Suz}\) central involution. The already derived genuine paired N-class ratio \(\theta_{113724}(t_2)/\theta_{17496}(t_2)=+13/2\) versus \(-13/2\) is independent of the common nonzero Weil parity trace but still requires the actual selected t2 CLASS. C2/C3 combined signatures are a **shortcut to eliminate incompatible families**, never evidence that identical central signs imply full character equality.

## 7. Owners, consumers and exact frontier

**Paid source mathematics:** normal kernel K and distinct actual extraspecial z; class20 central idempotent dichotomy; original full-character decomposition and phase/Clifford split as published/encoded original sources; signed \(P_1-P_2\) orientation transport; common selected 12/78 Suzuki central phase; previous central-product \(N=EH\).

**New source-native GAP deliverable:** enhanced existing \`scripts/monster_3b_suzuki_main_quotient_match.g\`, with original qKernel3 position and original 1458, 17496, 113724 characters, forcing class20 selector == full-char descent, double-C3 trace identities, and exact two-way 12/78 C3 phase matching. It still retains all original 210-class and Monster source conditions and emits the actual selected source positions and trace metadata only **if GAP runs**.

**Unpaid original mathematical endpoints:** (A) attach a particular user-local MM \`Hit0\` quotient word to the genuinely selected 6.Suz.2 source complement H and original class coordinates; (B) choose/transport a marked E-centre z orientation to realize the odd phase projector on original \(\rho_W\) in a specified basis; (C) produce original complex Monster \(\rho_W\), source Weil \(K_s\) and numerical 12×12/78×78 Hom operators for those same selected elements; (D) distinguish actual selected 78 family in a real exact GAP receipt; the script currently cannot execute without GAP/CTblLib. No new numerical facts about GAP-selected families or full Monster element orders are asserted.

**Producer→consumer:** Barraclough–Wilson original tables/quotient, Bray–Wilson Monster diagonal central-product and BMW restriction → \`IbrahimMonster3BPrimarySupplementKernelClass20SnowballExact\` / \`IbrahimMonster3BDiagonalKernelPaidSignGaugeCorrectionExact\` → original GAP main quotient matcher and original \`render_monster_3b_suzuki_main_quotient_match.py\`; marked centre data → \`IbrahimMonster3BPhaseOrientationGaugeSnowballExact\`, original \(P_s\) and source \`IbrahimMonster3BLinearMultiplicityHomSpaceExact\`; source selected main/MN3B degrees and genuine 6.Suz central signs → \`Monster3BActualZetaPromotionPipelineExact\`, Paper10, and P2/P3/P4/P5 roadmap. Original Sym²78 attribution: Nebe (2025). **No generic certificate loop, no duplicated Langlands machinery, no 90D guessed representation.**

**Local check:** exact SymPy matrices for \(C_3\rtimes C_2\) with k eigenvalues \(\zeta,\zeta^2\) give character at k=-1, \(P_K=0\), and \(oP_1o^{-1}=P_2\), plus exact integer class-20 dichotomy for 17496/113724. Not a GAP/CTblLib or Monster source execution.