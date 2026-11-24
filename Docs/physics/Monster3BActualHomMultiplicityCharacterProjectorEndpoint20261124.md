# Monster 3B / Paper 10 — actual 90D Hom action and canonical 12+78 character projectors

24 November 2026. **Endpoint-first mathematical construction, not a certification run.** The problem is the actual characteristic-zero representation of the Monster 3B normalizer on the **same** multiplicity carrier, not a formal \`Fin 90\` set, a synthetic GF(3) quotient, or repetition of the already-paid character-level 12+78 arithmetic.

## Primary mathematical and repository source owners

- Barraclough–Wilson (2007), *The Character Table of a Maximal Subgroup of the Monster*, DOI 10.1112/S1461157000001352: extension of each nontrivial 729D extraspecial character to the phase-preserving \(3^{1+12}:6.\mathrm{Suz}\) inertia, phase exchange under the outer involution, main character/induction mechanism.
- Dietrich–Lee–Pisani–Popiel (2026), original \`MonsterSubgroups\` word producer, pinned source blob \`c8fb3a305a6b7d08e9c33a265cfb3e6e84848be2\); existing \`scripts/monster_3b_mmgroup_source_symplectic_basis.py\` exports actual E basis / E normalizer actions. User-reported authentic \`mmgroup 1.0.8\` extraction, exact 28 powered quotient candidates on PR #1545.
- Original GAP/CTblLib 210-class \(6.\mathrm{Suz}\), \(6.\mathrm{Suz}.2\), main, MN3B and Monster source/character fusions; user-local CTblLib 1.3.11 results, with source word-to-class matching kept separate.
- \`DASHI/Wikimedia/IbrahimMonster3BPhaseResolvedCharacterTwelveSeventyEightWeldExact.agda\`: the **already available** character/Clifford degrees \(17496=2\cdot729\cdot12\), \(113724=2\cdot729\cdot78\), hence phase \(8748+56862=65610\); not literal 90D matrices.
- \`DASHI/Wikimedia/IbrahimMonster3BLinearMultiplicityHomSpaceExact.agda\`: actual Hom and evaluation contract; \`DASHI/Moonshine/Monster3BMultiplicityEvaluationExact.agda\` finite-basis donor, not same-object certificate.
- \`DASHI/Moonshine/Monster3BNormalizerCocycleCancellationExact.agda\`, \`DASHI/Moonshine/Monster3BAtlasSymplecticSimilitudeHeisenbergLiftExact.agda\`, \`DASHI/Moonshine/Monster3BActualZetaPromotionPipelineExact.agda\`: existing downstream consumers; **do not duplicate** their generic algebra.

## 1. Exact actual-carrier construction

Let \(W\) be the *original characteristic-zero Monster weight-two module*, \(\dim W=196884\), and \(z\in\mathbb M\) the chosen actual 3B element. Its traces satisfy \(\chi_W(z)=\chi_W(z^2)=54\). For \(s=1,2\), put
\[
P_s=\frac13\sum_{j=0}^2\zeta^{-sj}\rho_W(z)^j,\qquad W_s=P_sW.
\]
Then \(\dim W_0=65664\), \(\dim W_1=\dim W_2=65610\). For the *actual* \(E=3^{1+12}\) with centre \(\langle z\rangle\), \(H_s\) is the unique irreducible 729D \(E\)-module of central phase \(\zeta^s\). Thus
\[
S_s:=\operatorname{Hom}_E(H_s,W_s),\quad \dim S_s=65610/729=90,
\quad \Phi_s:H_s\otimes S_s\longrightarrow W_s,\quad h\otimes f\mapsto f(h).
\]
By semisimplicity and Stone–von Neumann, \(\Phi_s\) is an \(E\)-equivariant isomorphism. This is an **actual-carrier abstract theorem**; it does not assign an arbitrary external basis to \(S_s\).

Choose the authentic commuting modulation subgroup \(B=\langle B_1,\ldots,B_6\rangle\subset E\), \(|B|=729\), with the original source polarization and \(B\cap Z(E)=1\). Its fixed-point operator inside \(W_s\) is
\[
\Pi_{0,s}=\frac1{729}\sum_{b\in B}\rho_W(b)|_{W_s}.
\]
In \(H_s\), the \(B\)-fixed space is the single Schrödinger vacuum line \(\mathbb C e_0\). Evaluation \(f\mapsto f(e_0)\) therefore gives the *actual* isomorphism
\[
\boxed{S_s\cong \Pi_{0,s}W_s,\quad \dim \Pi_{0,s}W_s=90.}
\]
Let \(T_x\) for \(x\in\mathbb F_3^6\) be the actual six-axis translation words. Set \(\Pi_{x,s}=T_x\Pi_{0,s}T_x^{-1}\). Their ranges partition \(W_s\); writing \(u\in\Pi_{0,s}W_s\), the maps
\[
\Phi_s(e_x\otimes u)=T_xu,\qquad
\Psi_s(w)=\sum_x e_x\otimes T_x^{-1}\Pi_{x,s}w
\]
are mutual inverses. Their identities follow from the actual E commutators and the complete set of 729 modulation eigenspaces, not from \(729\cdot90\) numerology.

## 2. Actual normalizer action is a Hom functor, not a guessed 90D matrix

Let \(I\) be the *phase-preserving inertia subgroup* acting on E; use the original \(6.\mathrm{Suz}\) inertia quotient with its correct centre and fixed source section, not the full phase-exchanging outer group. The cited Barraclough–Wilson construction supplies an ordinary linear extension \(K_s(g)\) of \(H_s\) for this phase-preserving group (with its specified extension gauge), satisfying
\[
K_s(g)\pi_s(e)K_s(g)^{-1}=\pi_s(geg^{-1}).
\]
For \(f\in S_s\) define
\[
\boxed{(L_s(g)f)(h)=\rho_W(g)\,f(K_s(g)^{-1}h).}
\]
The right side remains E-equivariant, by the displayed conjugacy identity, and belongs to \(\operatorname{Hom}_E(H_s,W_s)\). Since both \(K_s\) and the original \(\rho_W\) are honest representations of the *same* chosen phase-preserving extension, \(L_s(gh)=L_s(g)L_s(h)\), \(L_s(1)=1\) on the **actual** Hom carrier; moreover
\[
\rho_W(g)\Phi_s=\Phi_s(K_s(g)\otimes L_s(g)).
\]
This gives an **explicit basis-free construction** of all \(90\)-dimensional multiplicity operators with no need for a synthetic 90D model or a \(65610\times65610\) matrix.

For the outer centre-inverting generator \(o\), \(\rho(o)\) maps \(W_s\to W_{-s}\). Choose an honest source-compatible phase-changing intertwiner \(K_o:H_s\to H_{-s}\) and define
\[
L_o:S_s\to S_{-s},\quad (L_of)(h')=\rho(o) f(K_o^{-1}h').
\]
This is **not** an endomorphism of one phase \(S_s\). If source \(K_g\) is only projective (e.g. an unnormalized Weil gauge), \(L\) is inverse-projective, exactly as already handled by \`Monster3BNormalizerCocycleCancellationExact\`. The unambiguous full action is \(K\otimes L\); scalar choices must be fixed jointly.

### Matrix-free concrete evaluation once original rho_W is available

With \(\Phi_s\) and actual original \(B,T_x\), write \(K_s(g)e_0=\sum_x k_xe_x\), where at least one \(k_x\ne0\). For \(u\in\Pi_{0,s}W_s\),
\[
\boxed{L_s(g)u=k_x^{-1}T_x^{-1}\Pi_{x,s}\rho_W(g)u\qquad(k_x\ne0).}
\]
Every valid nonzero \(x\) gives the **same** \(L_s(g)u\), because \(\rho_W(g)\Phi_s(e_0\otimes u)=\Phi_s(K_s(g)e_0\otimes L_s(g)u)\). This computes each 90D operator from the *same original source action*, a single Weil-vacuum column, and 729-weight projectors; it avoids dense full-sector tensor matrices. It is not yet 90×90 numerical entries without an actual characteristic-zero \(\rho_W(g)\) or equivalent source intertwining data.

## 3. Unique, genuine constituent operators by central character projectors

**Source premise:** the actual character of the just-constructed \(L_s\) on the selected inertia group is \(\chi_{12}+\chi_{78}\), with \(\chi_{12},\chi_{78}\) the *source-identified* two distinct irreducible characters in the original GAP/CTblLib 210-class ordering and with correct central \(C_2\), \(C_3\) and outer phase assignment. The existing Ibrahim phase-resolved source weld pays the associated *Clifford/character occurrence*, not by itself the equality \(\chi_{L_s}=\chi_{12}+\chi_{78}\) on **this actual** Hom carrier. That equality is the remaining same-object attachment, not a demand to prove the degree numerology again.

Write \(Q=I/E\) for the correctly chosen phase-preserving quotient on which \(L_s\) descends after fixing \(K_s\)'s extension (if the section retains a nontrivial scalar kernel, use the actual quotient extension rather than falsely descending). For \(a=12,78\) the standard central idempotent in \(\mathbb C[Q]\) is
\[
e_a=\frac{\chi_a(1)}{|Q|}\sum_{q\in Q}\chi_a(q^{-1})\,L_s(q).
\]
They satisfy \(e_{12}^2=e_{12}\), \(e_{78}^2=e_{78}\), \(e_{12}e_{78}=0\), \(e_{12}+e_{78}=1_{S_s}\), and
\[
\boxed{S_s=S_{12,s}\oplus S_{78,s},\quad
S_{a,s}=\operatorname{im}e_a,\quad
\dim S_{12,s}=12,\quad\dim S_{78,s}=78.}
\]
The actual individual operators are \(L_{a,s}(q)=L_s(q)|_{S_{a,s}}\). Thus **the constituent subspaces and their operators are mathematically unique** once the same-object character hypothesis and original \(K_s,\rho_W\) action are fixed. There is no arbitrary choice of \(12\oplus78\) carrier and no arbitrary generated character table.

The outer action \(L_o\) conjugates these projectors according to the genuine source outer automorphism: it maps \(S_{a,s}\) to the corresponding transported \(\chi_a^o\) isotypic subspace in \(S_{-s}\). It is NOT safe to assume that an outer generator preserves each individual phase or independently fixes each character label without the original class map.

For computing a *specific* 90D matrix, pick a basis of the actual 90D space \(\Pi_{0,s}W_s\), evaluate each \(L_s(q)\) by the boxed one-column formula, then project by \(e_{12},e_{78}\). Different bases give conjugate matrices; the representation is the same.

## 4. Stronger normalized trace/source-character bridge

For any \(g\in I\) commuting with z,
\[
\chi_{W_s}(g)=\frac13\sum_{j=0}^{2}\zeta^{-sj}\chi_W(z^jg).
\]
If the chosen \(K_s(g)\) has nonzero trace, \(\chi_{S_s}(g)=\chi_{W_s}(g)/\chi_{H_s}(K_s(g))\). **At zero Heisenberg trace, division is invalid**; use the direct \(\Pi_{0,s}\) projector construction or actual Hom action. The full 210-class character comparison is used to attach this exact \(\chi_{S_s}\) to the source \(\chi_{12}+\chi_{78}\). Character values alone do not specify a preferred basis or scalar extension, but irreducible characters *uniquely determine complex representations up to equivalence*. That is enough for the representation existence/decomposition theorem; exact source-normalized matrices additionally require original action or an explicit intertwiner.

## 5. Actual remaining endpoint lemmas, no certification diversion

- **M3B-L09R (same-object Hom):** instantiate \(\rho_W\), actual E and source \(B,T_x\); establish \(\Pi_{0,s}\), the complete 729 projector resolution and both-sided \(\Phi_s,\Psi_s\) using the original characteristic-zero carrier.
- **M3B-L10R (source 90D operators):** attach the honest original \(K_s\) extension to the same source \(6.\mathrm{Suz}\) inertia and define \(L_s\) by the Hom formula. Derive the matrix-free one-column operator on \(\Pi_{0,s}W_s\), including independence of selected nonzero coefficient and actual outer paired \(L_o\).
- **M3B-L11R (character projectors):** prove \(\chi_{L_s}=\chi_{12}+\chi_{78}\) in the **original 210-class and central-sign coordinates** using the existing selected-character weld, actual \(\rho_W\) and source \(\chi_{H_s}\). Then the two displayed idempotents automatically give genuine 12D and 78D constituent carriers and operators, with no further abstract group representation existence problem.
- **M3B-L12R (outer coherence):** source word correction / full relator group lift M3B-L04–L07, and source-consistent reciprocal scalar gauges. The outer \(\lambda=-1\) maps \(S_s\to S_{-s}\); do not assume it acts internally on \(S_s\) or is strict symplectic.
- **M3B-L13R (faithful class):** distinguish selected 78 from the alternative symmetric-square family at the genuine source class/central-\(C_2\) level if any ambiguity remains; do not reopen the already source-paid 8748/56862 character-occurrence arithmetic.

**Solved at mathematical theorem level:** the Hom functor defines the original \(90\)-dimensional operator action once actual \(\rho_W\) and extended \(K_s\) are chosen; canonical central character idempotents then split it uniquely, *if the real multiplicity character equality is established*. Both phases and their exchange admit the same functorial construction. **Not yet numerically produced or same-object attached:** original \(\rho_W\) operators, original \(K_s\) extension/lift gauge attached to the selected C,D words, actual class/character equality on \(S_s\), and coherent full Monster relator corrections. No fixed 90×90 entries, characteristic-zero action or class identity are invented.

Reference ownership: Barraclough–Wilson 2007, original MonsterSubgroups and ATLAS, GAP/CTblLib, standard Stone–von Neumann/Clifford/Schur character idempotents; existing Ibrahim/JFine source character programme, DASHI source-to-model action and Paper 10 finite cyclotomic original operators. Do not claim Weil theory or finite-group central idempotents as novel.
