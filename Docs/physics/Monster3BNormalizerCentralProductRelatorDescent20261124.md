# Monster 3B — canonical central-product normalizer lift, characteristic-3 relators and one-class 12/78 discriminator

24 November 2026. Endpoint-first construction for PR #1545. This is **one coherent mathematical maximal cut** on the original normalizer, not another Hit-0 script, test loop or a new model. All representation structures below use the original Monster \(3B\) normalizer and the published Barraclough–Wilson / Bray–Wilson group construction. They do not prove that a **particular** user-local MM word is the published lifted standard generator.

## 0. Correct source and group type

Existing producers:
- Barraclough–Wilson 2007 §5 and N3BetcTables primary supplemental maps: original main table \(3^{1+12}:6.\mathrm{Suz}.2\), quotient to \(MN3B=3^{1+12}.2.\mathrm{Suz}.2\), and group maps main→6.Suz.2, 6.Suz.2→main, main→MN3B→Monster.
- Bray–Wilson 2006, DOI 10.1016/j.jalgebra.2005.12.017: the two diagonal central-product kernels, with the actual Monster quotient discriminated by original words.
- Existing Ibrahim diagonal-kernel owner: the **invariant** order-3 kernel \(K=\{1\}\cup\text{main class 20}\) is already source-paid, and generator sign \(t_1t_2\) versus \(t_1t_2^{-1}\) is a **phase-orientation coordinate**, not a missing abstract subgroup.
- Existing original GAP producer 'scripts/monster3b_atlas_suz2b_monster_4class_source_fusion.g': source split 6.Suz.2→main, original main→6.Suz.2 quotient, original main→MN3B diagonal C3 quotient, original MN3B→Monster fusion; do not turn a class map into a chosen MM word.
- Existing original source-selected character and faithful-vs-Sym² producer 'scripts/monster_3b_suzuki_main_quotient_match.g' and 'IbrahimMonster3BSuzukiMainQuotientSameObjectSnowballExact.agda'. The producer already iterates ALL degree-78 families, tests original main split, MN3B descent and Monster occurrence; no new 210-class matcher is introduced here.
- Existing 'scripts/monster_3b_actual_kernel_structure.g': actual \(E\) is an extraspecial exponent-three \(3^{1+12}\), original E/Z dimension 12, and centre order three. Character-level and finite-Monster-group status must not be conflated with local execution.

Let \(\widetilde N=E\rtimes\widehat Q\) be the published SPLIT main model with \(\widehat Q=6.\mathrm{Suz}.2\). Let \(z\) generate \(Z(E)\cong C_3\) and \(t\) the normal central \(C_3\) in the INNER \(6.\mathrm{Suz}\subseteq\widehat Q\). The \(\widehat Q\) action on \(E\) factors through \(\widehat Q/\langle t\rangle\cong 2.\mathrm{Suz}:2\); the outer involution inverts both appropriate order-three centres.

In a fixed sign convention write \(K=\langle(z,t^\epsilon)\rangle\), \(\epsilon=\pm1\), as a normal diagonal subgroup of order three. \(K\) is central in the inner \(E\rtimes6.\mathrm{Suz}\) but **not necessarily central in the whole outer group**: outer conjugation may invert it. The original main class 20 determines the SUBGROUP \(K\) even if the sign word varies under \(z\leftrightarrow z^{-1}\).

The actual normalizer source model is
\[
\boxed{N=\widetilde N/K=(E\rtimes(6.\mathrm{Suz}.2))/K.}
\]
This is a central-product model on the phase-preserving inner subgroup, not an arbitrary split extension by \(2.\mathrm{Suz}:2\).

## 1. Source 6.Suz.2 gives a COHERENT normalizer lift in one construction

Since every nonidentity element of \(K\) has a nontrivial \(E\)-component, \(K\cap E=K\cap\widehat Q=1\). Both \(E\) and \(\widehat Q\) **inject** in \(N\). Write \(H\le N\) for the injected image of \(\widehat Q=6.\mathrm{Suz}.2\). The group factorization is
\[
\boxed{N=EH,\quad E\cap H=Z(E)\cong C_3,\quad
N/E\simeq H/(E\cap H)\simeq2.\mathrm{Suz}:2.}
\]
The two inclusions are the **same original normalizer**; \(H\) is a true source group, not 28 synthetic candidate matrices.

Let \(q_C,q_D\in N/E\) be any selected quotient generators that correspond to the chosen \(2.\mathrm{Suz}:2\) source generator pair. Choose genuine source lifts \(h_C,h_D\in H\). If \(R(q_C,q_D)=1\) is **any** quotient word relation, then
\[
\boxed{R(h_C,h_D)\in H\cap E=Z(E),}
\]
automatically. Thus **all noncentral \(E/Z(E)\) relator residues vanish simultaneously** for the coherent source lifts; the only remaining relator data in \(H\) are the prescribed order-three central-cover phases. The simultaneous vector correction system from the earlier roadmap is a coordinate reconstruction of these existing source lifts for a chosen MM word pair, **not an independent abstract existence obstruction**.

For a user-local MM candidate \(c,d\in N\) with the same N/E quotient images, write \(c=e_C h_C\), \(d=e_Dh_D\) for some original \(e_C,e_D\in E\). These are the source-correct simultaneous \(E\)-corrections, though the numerical \(e_C,e_D\) require original MM coordinate identification. Correcting to \(h_C,h_D\) yields the whole source cover's relators at once rather than solving every relator as an unrelated 24-trit problem.

**Important new non-splitting boundary:** the inner \(6.\mathrm{Suz}\to2.\mathrm{Suz}\) central \(C_3\)-cover is non-split: \(6.\mathrm{Suz}\) is perfect; a splitting would give \(6.\mathrm{Suz}\simeq C_3\times2.\mathrm{Suz}\), which has nontrivial abelianization. Therefore **demanding that every full \(2.\mathrm{Suz}\) quotient relator be literally \(1\) in the chosen source \(6.\mathrm{Suz}\) complement is mathematically wrong**. Some are supposed to be the nontrivial central element. This does not by itself exclude a different 2.Suz section in the whole \(N\) using \(E\)-corrections; it shows the correct source endpoint must retain the genuine 6.Suz central-cover relations. The ATLAS GF(3) semipresentation is a quotient screen, not a full-group identity specification.

## 2. Coprime-power lifts can be explicitly solved, not searched

Suppose \(x\in N\) projects to an element of **known exact order** \(m\) in the actual quotient \(N/E\), with \(\gcd(m,3)=1\). Then \(x^m\in E\) and \(E\) has exponent three, so \(x^{3m}=1\). Pick \(n\) such that \(n\equiv1\pmod m\) and \(n\equiv0\pmod3\). Thus
\[
\boxed{x'=x^n,\qquad x'E=xE,\qquad (x')^m=1,\qquad
\operatorname{ord}(x')=m.}
\]
Concrete source values: \(m=4\implies n=9\); \(m=7\implies n=15\); \(m=56\implies n=57\).

Hence for an authentic source quotient C of order four, \(C'=C^9\) is an **explicit genuine order-four Monster lift** without brute-force kernel searches; it retains the same quotient C and centre multiplier. Its source \(E\)-conjugacy uniqueness for a fixed C4 preimage follows from Schur–Zassenhaus because \(E\) is a normal odd-order Hall subgroup there. Any **individually** chosen quotient element of order 56 or 7 also has a coprime-power lift, but this does NOT imply that the WORD \((CD)\) or the prescribed seventh-order relator can be repaired independently while keeping all generators' other relations.

One must confirm the projected C has order four in actual \(N/E\), not merely in a possibly unfaithful quotient matrix image. This is supplied at the original source-group identification, not by characteristic polynomials alone.

## 3. Genuine D-order-three obstacle in the arbitrary-word coordinate route

The original ATLAS \(\overline D\) matrix, source SHA256 433ba0f0373995b159859df00dd5a5005355fdbf8b59a31d651aeaf43ffcd15f, has over \(\mathbb F_3\)
\[
\operatorname{rank}(D-I)=6,\quad
\operatorname{rank}(D-I)^2=2,\quad
(D-I)^3=0.
\]
This was independently derived by exact GF(3) elimination from the original 12x12 MeatAxe source matrix on 'master'. The **exact Jordan type is \(3^2\,2^2\,1^2\)** (two 3-blocks, two 2-blocks, two 1-blocks). Therefore
\[
\dim\ker(D-I)=6,\quad
\mathrm{im}(I+D+D^2)=\mathrm{im}(D-I)^2\ \text{has dimension }2,
\]
and
\[
\boxed{\dim\left(\ker(D-I)/\mathrm{im}(D-I)^2\right)=4.}
\]
For an arbitrary actual candidate word \(d\) with quotient order three, let \(r=d^3\bmod Z(E)\in E/Z(E)\). It is fixed by D. Changing \(d\) to \(e(u)d\) changes the **vector residual** to
\[
r+(I+D+D^2)u=r+(D-I)^2u.
\]
So the four-dimensional class \([r]\) is the exact *potential* obstruction to an order-three lift modulo Z(E). It is NOT automatically zero in an arbitrary extension of C3 by E, so prior claims that all three-primary lifts can be fixed by CRT would be false.

**But the genuine Monster normalizer source removes this vector obstruction for coherent source quotient lifts**: choose \(h_D\in H\) above the same D; then \(h_D^3\in H\cap E=Z(E)\) and its vector residual is zero. Every other word d above the same quotient element differs by E, so its [r] necessarily vanishes. Its **central** \(h_D^3=z^k\) may be nontrivial and is the valid 6.Suz-cover relation, NOT automatically a failure.

This solves the **abstract vector-lift existence** from the original central-product structure while retaining four explicit coordinate equations for connecting an arbitrary selected Hit0 word to it.

## 4. The true diagonal descent phase, including the 729-extension scalar

The source has an actual \(\psi_s\), extension of the \(729\)-dimensional Heisenberg irreducible to the inner \(E\rtimes6.\mathrm{Suz}\). Let
\[
\psi_s(z)=\zeta^s I,\quad \psi_s(t)=\zeta^{u_s}I,\quad
\eta_a(t)=\zeta^{k_a}I\quad(a=12,78).
\]
The 729-extension central scalar \(u_s\) **must not be silently set to zero**. The tensor \(\psi_s\otimes\eta_a\) descends through the SAME original diagonal K exactly when
\[
\boxed{s+\epsilon(u_s+k_a)\equiv0\pmod3.}
\]
For both a=12 and 78 on the same phase s and same \(\psi_s\), this forces
\[
\boxed{k_{12}=k_{78}\pmod3.}
\]
This is the source-correct common-phase constraint. The short formula \(s+\epsilon k_a=0\) is valid only after explicitly proving a gauge \(u_s=0\); the original source does not grant that for free. The already-paid class-20 kernel, actual \(6.\mathrm{Suz}\) centre and published main→MN3B quotient supply the right object. Inverting z reverses s and all paired character labels; it changes only orientation, not the central-product module.

Changing a chosen extension \(K_s\) to \(K'_s=\nu K_s\) multiplies **both** multiplicity actions by the same \(\nu^{-1}\). The 12a/b and 78a/b family labels cannot undergo independent character twists. On the perfect phase-preserving \(6.\mathrm{Suz}\) inner factor, any one-dimensional character twist is trivial; on the outer extension a separate outer-sign twist may exist, acting simultaneously on the paired action. This fixes the correct scalar/cocycle accounting in the existing 'Monster3BNormalizerCocycleCancellationExact.agda' consumer.

## 5. A one-class faithful-78 vs Nebe-Sym² discriminator with no Weil gauge

Let \(t_2\in6.\mathrm{Suz}\subset H\) be the original **central order-two** element, with genuine order two in H and quotient symplectic action \(-I_{12}\) on \(E/Z(E)\). It is **not** the diagonal order-three generator t above. Its action on a 729-dimensional Schrödinger irrep is conjugate, up to scalar sign, to the parity operator \(e_x\mapsto e_{-x}\), whose trace is \(+1\). Since \(t_2^2=1\), \(\operatorname{tr}K_s(t_2)=\sigma\in\{+1,-1\}\), the same for both conjugate central phases.

The source faithful 12 character has \(t_2\)-scalar \(-1\), hence \(\eta_{12}(t_2)=-12\). A faithful 78 has scalar \(-1\), while Nebe's \(\operatorname{Sym}^2(12)\) or its dual has scalar \(+1\). Thus for the FULL original normalizer pair characters (the two nontrivial phases combined),
\[
\theta_{17496}(t_2)=-24\sigma,\qquad
\theta_{113724}(t_2)=156\sigma\,\varepsilon_{78},
\quad \varepsilon_{78}\in\{-1,+1\},
\]
and therefore
\[
\boxed{
\frac{\theta_{113724}(t_2)}{\theta_{17496}(t_2)}
=\begin{cases}
+13/2&\text{faithful degree 78},\\
-13/2&\text{nonfaithful Sym}^2(12)\text{ or dual.}
\end{cases}}
\]
The ratio cancels the UNKNOWN 729-Weil trace sign \(\sigma\), both absolute central-\(\zeta\) labels and the 729 common extension gauge. **One original 6.Suz central-involution class with its two selected N-character values is sufficient** to distinguish these two families, *provided the class is genuinely attached to the same original \(t_2\)*. The original existing GAP matcher already exports selected \(\chi(C_2)\) and full all-class family rows. This is a mathematical reduction of its necessary information, not a claim that the actual runtime values were observed in this session.

A more general gauge-invariant identity: for any phase-preserving \(g\in I\), let \(\tau_{a,s}(g)=\frac13\sum_{j=0}^2\zeta^{-sj}\theta_{d_a}(z^jg)\). Then \(\tau_{a,s}(g)=\chi_{K_s}(g)\chi_{S_{a,s}}(g)\). Whenever the common factor and denominator are nonzero,
\[
\frac{\tau_{78,s}(g)}{\tau_{12,s}(g)}
=\frac{\chi_{S_{78,s}}(g)}{\chi_{S_{12,s}}(g)}.
\]
It eliminates the Heisenberg extension character completely. Where the common Weil trace is zero, BOTH numerator and denominator vanish and division is invalid; the original direct N-projectors/Hom operators remain available.

## 6. Exact mathematical endpoint status and old-gate repair

**Source-abstractly settled:** true \(N=EH\) central-product lift; all quotient-word relators of coherent H lifts land in \(Z(E)\) (rather than arbitrary E); abstract D-vector obstruction vanishes for actual source lifts; every prime-to-three cyclic quotient lift has explicit power solution; the true common diagonal phase and reciprocal scalar gauge are fixed algebraically; one central-involution trace ratio distinguishes the faithful-78 versus symmetric-square-78 family using already-existing source character tables. Together with preceding group-algebra N-isotypic projectors, this constructs actual \(S_{12,s}\oplus S_{78,s}\) abstractly.

**Still open and genuinely source-specific:** identify Hit0 or another member of the 28 matrix-word candidates with chosen **actual elements of the injected source H=6.Suz.2** (rather than only their image in GSp12(3)); produce concrete E correction words \(e_C,e_D\), the central-cover phase values of all chosen relators and the corresponding source GAP/Monster class coordinates; obtain \(\rho_W(h_C),\rho_W(h_D)\) in the original complex representation to instantiate explicit matrices on the already-defined Hom subspaces. The original full-character matcher already selects the 78 family *conditionally on running original source tables*: no new script or independent 210-class numerical discovery is needed to solve the structural endpoint.

**Do not re-open as mathematical blockers:** canonical \(729\times90\) decomposition, 12+78 phase-paired original N-character family, abstract full-group-lift existence from the published central product, and faithful-vs-Sym² central-sign criterion. **Do not claim** a numeric selected family without a source value, a chosen Hit0-to-source isomorphism, full relator identities in the non-split 6.Suz cover, a 90D numeric matrix, or formal kernel certification.

Producer→consumer: original Barraclough–Wilson main/6.Suz.2/MN3B and Bray–Wilson diagonal kernel → original 'IbrahimMonster3BDiagonalKernelPaidSignGaugeCorrectionExact', 'IbrahimMonster3BSuzukiMainQuotientSameObjectSnowballExact' and \`scripts/monster_3b_suzuki_main_quotient_match.g\`; original ATLAS 12D generator matrices and PR #1545 28 candidates → source quotient-to-H coordinate attachment; existing 'Monster3BAtlasSymplecticSimilitudeHeisenbergLiftExact' and 'Monster3BNormalizerCocycleCancellationExact' → paired \(K\otimes L\) phase coherence; original 'IbrahimMonster3BLinearMultiplicityHomSpaceExact', 'Monster3BActualZetaPromotionPipelineExact', and Paper 10 → actual source representation endpoint. No new background task, Agda/Lean proof postulate or generic certificate created.
