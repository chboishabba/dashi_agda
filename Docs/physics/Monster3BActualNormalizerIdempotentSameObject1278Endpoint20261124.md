# Monster 3B — source-first actual-normalizer idempotents directly construct the 12+78 Hom summands

**24 November 2026 · PR #1545 · mathematical endpoint, prior to certification.**
This advances [the preceding Hom/Weil construction](Monster3BActualHomMultiplicityCharacterProjectorEndpoint20261124.md) by avoiding a circular requirement to compute the entire 90-dimensional \`L_s\` character *before* locating its 12- and 78-dimensional source summands. The actual Monster normalizer restriction already specifies its large paired irreducible components at the character/Clifford level, and a complex group-algebra projector directly realizes those components **on the same actual Monster carrier**.

## 1. Original owned input (and its exact strength)

The existing original modules are:
- \`DASHI/Wikimedia/IbrahimMonster3BModernRestrictionTwelveSeventyEightOccurrenceSnowballExact.agda\` — Breuer–Magaard–Wilson restricted-character protocol (95 candidates, four coefficient-one constituents), and An–Wilson Table A.17 degree inventory; unique accepted **degree multiset** \(\{143,17496,65520,113724\}\) for the restricted \(196883\) character.
- \`DASHI/Wikimedia/IbrahimMonster3BPhaseResolvedCharacterTwelveSeventyEightWeldExact.agda\` — original Barraclough–Wilson extraspecial \(729\)-character extension, outer phase-exchange, paired outer degrees \(17496=2\cdot729\cdot12\) and \(113724=2\cdot729\cdot78\), correct character/Clifford (not coordinate) interpretation.
- \`DASHI/Wikimedia/IbrahimMonster3BSuzukiMultiplicityCharacterSnowballExact.agda\` — \(\psi_s\otimes\eta\) inflation/tensor-induction mechanism, with \(\eta\) an irreducible \(6.\mathrm{Suz}\)-character, and still-needed actual chosen \`12a/12b\` and \`78a/78b\` central/phase orientation.
- \`scripts/check_monster27_voa_3b_primitive_charge_exact.py\` — actual weight-two \(196884\), \(3B\) trace \(54\), and central phase dimensions \(65664,65610,65610\).

Use \(N\) for the ORIGINAL full source \(3B\)-normalizer actor underlying those selected character rows (with the published \(\mathrm{MN3B}\)/Monster fusion, not a made-up group or guessed abstract \(2.\mathrm{Suz}:2\) embedding). Let \(W=\mathbb C\oplus V_{196883}\) be the actual weight-two Monster representation, and \(\rho:N\to GL(W)\) its restriction. We make the following **exact source-rooted premise** explicit:

> \((R_{\rm actual})\) The genuine complex restriction \(V_{196883}|_N\) has four pairwise distinct irreducible characters, each of multiplicity one, with degrees \(143,17496,65520,113724\). The degree \(17496\) and \(113724\) summands are the genuine **outer-paired nontrivial-\(z\)** Clifford constituents from the Barraclough–Wilson construction, with \(z\in E=3^{1+12}\) the same source 3B central element. The remaining \(143,65520\) summands are centre-trivial. The source character labels/rows rather than only degree arithmetic fix which \(\theta_{17496},\theta_{113724}\) these mean.

**Do not collapse the two source inputs:** a unique degree multiset alone cannot identify character labels, the actual element \(z\) or a preferred \(12a/12b\) orientation. The original Ibrahim phase-resolved weld and Barraclough–Wilson source identify the *families* but do not supply concrete matrices. The selected 210-class matching remains necessary for pinned labels and original lift identity.

## 2. Canonical original-module projectors: full normalizer FIRST

For each source-identified irreducible normalizer character \(\theta_d\) of degree \(d\in\{143,17496,65520,113724\}\), define its **central idempotent in the group algebra of the actual \(N\)** and its action on the actual \(W\):
\[
\mathbf E_d:=\frac{d}{|N|}\sum_{g\in N}\theta_d(g^{-1})\rho(g)\in\operatorname{End}_{\mathbb C}(W).
\]
Class-sum form uses the original 210-class coordinates and the original class sizes:
\[
\mathbf E_d=\frac{d}{|N|}\sum_{C\subseteq N}|C|\theta_d(C^{-1})\rho(c_C).
\]
The class-sum displayed is a shorthand for the operator **class sum** \(\sum_{g\in C}\rho(g)\); a single \(\rho(c_C)\) must not replace it unless the representation is scalar on the whole class. The exact valid compressed form is
\[
\boxed{\mathbf E_d=\frac{d}{|N|}\sum_C\theta_d(C^{-1})\sum_{g\in C}\rho(g).}
\]
The sum is a mathematical finite formula, *not* a claim that all Monster matrices were explicitly enumerated. Standard character orthogonality and complete reducibility yield:
\(\mathbf E_d^2=\mathbf E_d\), \(\mathbf E_d\mathbf E_e=0\) for \(d\ne e\), and
\[
W=\mathbf E_{\rm triv}W\oplus \mathbf E_{143}W\oplus
\mathbf E_{65520}W\oplus \mathbf E_{17496}W\oplus \mathbf E_{113724}W,
\]
with respective dimensions \(1,143,65520,17496,113724\). The numerical sum is **exactly**
\[
1+143+65520+17496+113724=196884.
\]
There is no room for a further summand *if* \(R_{\rm actual}\) is the genuine complete restriction; the arithmetic by itself cannot certify completeness. Denote \(\mathbf E_{12}^{N}:=\mathbf E_{17496}\), \(\mathbf E_{78}^{N}:=\mathbf E_{113724}\).

## 3. Source-central projectors SECOND and exact ranks without any 90×90 matrix

For the actual order-three centre \(z\), set
\[
P_s=\frac13\sum_{j=0}^2\zeta^{-sj}\rho(z)^j,\qquad s=0,1,2.
\]
Each \(\mathbf E_d\) is **central in the original group algebra of \(N\)**, so \(\mathbf E_dP_s=P_s\mathbf E_d\), even though \(z\) need not be central in \(N\) (the outer automorphism interchanges \(s=1,2\)). Therefore
\[
W_{12,s}=P_s\mathbf E_{17496}W,\quad
W_{78,s}=P_s\mathbf E_{113724}W
\]
are **literal subspaces of the same actual \(W\)**. For \(s=1,2\), the genuine original outer element \(o\) with \(ozo^{-1}=z^{-1}\) maps \(W_{a,1}\) isomorphically onto \(W_{a,2}\), since \(\mathbf E_d\) commutes with \(\rho(o)\). The source paired constituents have no central-zero component, so
\[
\boxed{\dim W_{12,s}=\frac{17496}{2}=8748,\qquad
\dim W_{78,s}=\frac{113724}{2}=56862,\quad s=1,2.}
\]
Moreover \(W_s=W_{12,s}\oplus W_{78,s}\), by completeness of \(R_{\rm actual}\) and the zero-centre character of the other constituents, with \(\dim W_s=65610\). This equality is **an actual carrier decomposition**, not merely a dimension count.

## 4. Heisenberg Hom THIRD: the actual 12- and 78-dimensional spaces

The phase-preserving subgroup \(I=C_N(z)\) contains \(E\), and \(\mathbf E_d\) commutes with \(I\), while each \(P_s\) commutes with \(I\). Thus \(W_{a,s}\) is an **actual \(E\rtimes I\)-stable constituent** (with the correct original group extension). Choose the genuine central-phase Heisenberg irrep \(H_s\) of dimension \(729\). The original \(W_{a,s}|_E\) is a sum of copies of \(H_s\), by Stone–von Neumann in characteristic zero. Define, without selecting any arbitrary model carrier,
\[
\boxed{S_{a,s}:=\operatorname{Hom}_E(H_s,P_s\mathbf E_{d_a}W),
\qquad d_{12}=17496,\ d_{78}=113724.}
\]
Exact dimensions:
\[
\dim S_{12,s}=\frac{8748}{729}=12,\quad
\dim S_{78,s}=\frac{56862}{729}=78.
\]
The additive Hom functor yields the **canonical source-level same-object splitting**
\[
\boxed{S_s=\operatorname{Hom}_E(H_s,P_sW)
=S_{12,s}\oplus S_{78,s},\qquad \dim S_s=90.}
\]
It also yields the actual 729-factor evaluation **componentwise**:
\[
\Phi_{a,s}:H_s\otimes S_{a,s}\stackrel\sim\longrightarrow W_{a,s},
\quad h\otimes f\longmapsto f(h).
\]
No new 12D, 78D or 90D representation is guessed: the constituent operators are **restrictions of the genuine original Monster action**, transported through the source-compatible \(729\)-module extension.

### Actual inertia operators directly from the source

Barraclough–Wilson's source \(729\)-dimensional Heisenberg irrep extension \(K_s(g)\) on the genuine phase-preserving inertia \(I\), with the original scalar/cover conventions, defines
\[
(L_{a,s}(g)f)(h)=\rho(g)f(K_s(g)^{-1}h),\quad g\in I.
\]
Because \(\mathbf E_{d_a}\) commutes with \(\rho(g)\), this preserves \(S_{a,s}\). If \(K_s\) is an honest representation of the **same chosen** \(I\) extension, each \(L_{a,s}\) is an ordinary representation; if a projective source gauge is selected, each \(L_{a,s}\) is inverse-projective and becomes honest only on the correct extended source, with existing \`Monster3BNormalizerCocycleCancellationExact\` cancellation. The outer element maps \(S_{a,s}\to S_{a,-s}\) through the appropriate phase-changing \(K_o\). It preserves the outer normalizer *degree label* \(d_a\) automatically because \(\mathbf E_{d_a}\) is central in \(\mathbb C[N]\); it need not preserve an individually named \(12a\) or \(12b\) inertia character.

**This solves the abstract same-object EXISTENCE of the constituent operators from the original restricted Monster representation and the source \(729\) extension**, provided \(R_{\rm actual}\) applies to that exact representation/normalizer. It does NOT give their numerical entries or a specific original source class/phase gauge.

## 5. Source-first block operator extraction, no character-division pitfalls

The earlier single Weil-column formula now restricts **directly** to each canonical source block:
for \(u\in\Pi_{0,s}W_{a,s}\) and \(K_s(g)e_0=\sum_x k_xe_x\), choose any \(x\) with \(k_x\ne0\). Then
\[
\boxed{L_{a,s}(g)u=k_x^{-1}T_x^{-1}\Pi_{x,s}\rho(g)\mathbf E_{d_a}u.}
\]
Since \(\mathbf E_{d_a}u=u\), it is a projector into the correct original constituent with the actual \(6.\mathrm{Suz}\) action. No need to divide a character value by \(\operatorname{tr}K_s(g)\), which may be zero. No need to search arbitrary \(90\times90\) matrices or construct a gigantic \(65610\times65610\) tensor action.

**Source-character extraction for original table coordinates** remains possible after the group/action attachment:
\(\chi_{W_s}(g)=3^{-1}\sum_j\zeta^{-sj}\chi_W(z^jg)\), and for nonzero \(\chi_{H_s}(K_s(g))\), \(\chi_{S_s}(g)=\chi_{W_s}(g)/\chi_{H_s}(K_s(g))\). The new direct original-\(N\) isotypic projectors bypass this division altogether for *existence and same-object splitting*. Original \(\theta_{d_a}\) full class rows/central phases remain necessary to pin ATLAS/CTblLib labels and the source C/D word-to-class identification.

## 6. Exact frontier after this mathematical cut

**Paid at mathematical theorem level under the actual source restriction \(R_{\rm actual}\):**
- Direct group-algebra construction \(\mathbf E_{17496},\mathbf E_{113724}\) as endomorphisms of the *same actual complex Monster weight-two carrier*;
- commuting \(\mathbf E_d\) and phase \(P_s\) projectors, original outer phase swap, ranks \(8748,56862\), exact original \(W_s=W_{12,s}\oplus W_{78,s}\);
- actual \(S_{12,s},S_{78,s}\) **as Hom subspaces of the very same \(S_s\)**, dimensions \(12,78\);
- legitimate, original-action-defined inertia operators on these subspaces via the chosen \(K_s\) and \(\rho\), and the single-column formula.

**Still a mathematical source-attachment obligation, not a generic lack of theory:**
1. **R_actual / selected source row correspondence**: the existing restricted degree multiset / Barraclough–Wilson paired identification must be transported onto the *same* actual \(N\) and \(\rho|_N\) as the selected MM group words. The source argument supports existence abstractly; no full literal \(196884\)-matrix identification or unambiguous \(12a/12b,78a/78b\) absolute orientation is supplied by the finite GF3 quotient hits.
2. **Literal \(\rho(g)\) and \(K_s(g)\) source normalizations**: needed for actual numerical 12×12, 78×78 and 90×90 matrix entries on the selected Monster elements, and for the reciprocal phase gauge. Their **abstract operators** exist on the original \(W\) even when no numeric basis is printed.
3. **Coherent full-group C,D lifts** and exact original semipresentation relator membership/corrections, including the previously distinguished \(-1\) central similitude; the group-algebra character projectors do not solve the group-extension problem.

**Mathematical endpoint priority:** identify the selected ATLAS C,D original group words with the genuine source normalizer/class fusion, then evaluate the already-defined \(\mathbf E_d\), \(P_s\), \(K_s,L_s\) operators in coherent class/phase coordinates. *No further generic certificate scripts or repeated quotient searches*. Certification once endpoints solved.

### Owner / producer→consumer routing

Breuer–Magaard–Wilson restriction, An–Wilson degree inventory, Ibrahim modern occurrence source → actual \(R_{\rm actual}\) and source \(\theta_{17496},\theta_{113724}\) → original \(N\)-character idempotents on \(W\);
Ibrahim phase-resolved Barraclough–Wilson \(729\) extension and Clifford phase pairing → \(P_s\), \(K_s\), \(\mathbf E_d\)-commutation → actual \(S_{12,s},S_{78,s}\);
\`DASHI/Wikimedia/IbrahimMonster3BLinearMultiplicityHomSpaceExact.agda\`, \`DASHI/Moonshine/Monster3BMultiplicityEvaluationExact.agda\` → \(\Phi_{a,s},\Psi_{a,s}\) and original Hom consumer;
\`DASHI/Moonshine/Monster3BNormalizerCocycleCancellationExact.agda\`, \`DASHI/Moonshine/Monster3BAtlasSymplecticSimilitudeHeisenbergLiftExact.agda\` → coherent action / paired central phase;
\`DASHI/Moonshine/Monster3BActualZetaPromotionPipelineExact.agda\`, Paper 10 signed Fourier/cyclotomic operators → full same-object final result.

Source credit: original Monster, Barraclough–Wilson, Breuer–Magaard–Wilson, An–Wilson, ATLAS, GAP/CTblLib; existing Ibrahim/JFine and DASHI endpoint consumers; standard complex representation theory/central primitive idempotents are prior art.