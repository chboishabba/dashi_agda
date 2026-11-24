# Monster 3B — exact-field 12→78→90 source operators and original 210-class character endpoint

**24 November 2026 · PR #1545 · P5 mathematical endpoint-first reduction.** This builds on the user's authentic GAP 4.16dev/CTblLib 1.3.11 selected \`6.Suz\` Irr153/154 (faithful 12) and Irr79/80 (NONfaithful Nebe dual-Sym² 78), the original selected central \(C_2\) trace \(+66\), and unique original 4D source-class fusion. These source results are paid; **do not re-run the selected 78-family search**.

## 1. Complete exact 210-class character from ONE faithful12 row

Let \(G=6.\mathrm{Suz}\), \(\zeta^2+\zeta+1=0\), \(K=\mathbb Q(\zeta)\), \(\sigma(\zeta)=\zeta^{-1}\). Choose an original **characteristic-zero** faithful 12 irreducible \(V_s\) with ordinary character \(\chi\), one of original \(G\)-table positions 153/154, with original source central \(C_3\)-scalar \(\zeta^s\). The prior authentic source restriction and the full 210-class direct/dual Sym² character equality identify the **same-phase** 78 as \(\operatorname{Sym}^2(V_s^\vee)\), and the selected actual inner multiplicity representation has type
\[
S_s|_G\cong V_s\oplus\operatorname{Sym}^2(V_s^\vee).
\]
For any \(g\in G\), finite-group dual characters are complex conjugates, here equal to \(\sigma\) on \(K\); the symmetric-square character is \(\frac12(\psi(g)^2+\psi(g^2))\) for \(\psi=\sigma\chi\). Hence
\[
\boxed{\chi_{90,s}(g)=\chi(g)+\frac{\sigma(\chi(g))^2+\sigma(\chi(g^2))}{2}.}
\]
For every one of the original 210 conjugacy classes \(C\), the existing \`6.Suz\` \`PowerMap(six,2)\` tells us the class \(C^2\), and the existing original selected \(\chi_{153}\)/\(\chi_{154}\) full character row supplies the values. **No 78D matrices, 90D matrices, fresh class search or unmarked phase guesses are needed to construct the entire selected ordinary 90D class character.** Equality with the actual \(S_s\) action is contingent on the same original 729 Weil extension gauge and the source N-module/phase attachment established in the earlier character and Hom ledgers.

This formula also supplies exact finite source fingerprints for any genuine ordinary12 source generator. If \(\rho_V(g)=A_g\in GL_{12}(K)\), then \(\chi(g)=\mathrm{tr}(A_g)\), \(\chi(g^2)=\mathrm{tr}(A_g^2)\); no evaluation of original 78D character rows is necessary to predict its 90D trace.

## 2. All inner 90D matrices lie in \(\mathbb Q(\zeta_3)\) and are explicitly functorial

Allan Steel's original [Ordinary Representations Database](https://magma.maths.usyd.edu.au/~allan/reps/db/) lists a faithful ordinary complex degree12 \`6.Suz\` representation, character-field degree 2, Schur index 1. Its original [Magma input file](https://magma.maths.usyd.edu.au/~allan/reps/db/d12.6Suz.nfdeg2.M) is \`d12.6Suz.nfdeg2.M\` (Steel original author; page updated Dec 2024). The nontrivial Suzuki \(C_3\) centre acts by \(\zeta^{\pm1}\), giving \(\mathbb Q(\zeta)\subseteq K_{\rm character}\). Since the character-field degree is 2, **\(K_{\rm character}=\mathbb Q(\zeta)=\mathbb Q(\sqrt{-3})\)**. Schur index one means a faithful 12 module can be defined over this *same* minimal character field.

For an original \(12\times12\) generator \(A_g\) over \(K\), take the **contragredient** \(B_g=(A_g^{-1})^\top\). Let \(S_2(B_g)\) be its natural representation on the \(78\) polynomial basis elements \(e_i e_j\), \(1\le i\le j\le12\). Thus an exact original-selected 90D matrix representation is
\[
\boxed{\mathcal L_s(g)=
\begin{pmatrix}
A_g&0\\0&S_2((A_g^{-1})^\top)
\end{pmatrix}\in GL_{90}(K).}
\]
In source basis, this is a **representation equivalent to** the actual same-phase multiplicity representation; identifying the source basis with the actual Monster \(\operatorname{Hom}_E(H_s,W_s)\) is the still-unpaid intertwiner. The outer extension is NOT automatically a \(90\times90\) endomorphism of one phase: it maps \(S_s\to S_{-s}\).

**Explicit derived 78D entries without libraries or hidden choices:** for the symmetric polynomial basis \(e_i e_j\) and \(B=(b_{ui})\), the coefficient from input \(i\le j\) to output \(u\le v\) is
\[
(S_2B)_{(u,v),(i,j)}=
\begin{cases}
b_{ui}^2 & i=j,\ u=v,\\
2b_{ui}b_{vi} & i=j,\ u<v,\\
b_{ui}b_{uj} & i<j,\ u=v,\\
b_{ui}b_{vj}+b_{vi}b_{uj} & i<j,\ u<v.
\end{cases}
\]
The formula is in \(\mathbb Q(\zeta)\), exact under arbitrary denominators and matrices over that field. This is the explicit mathematical endpoint of the 78/90 **construction**; original source generator coordinates are still needed to print the numerical entries.

For \(\operatorname{tr}(A_g)=t\) and \(\operatorname{tr}(A_g^2)=t_2\), finite-group unitarity/character duality gives \(\operatorname{tr}S_2(B_g)=\frac12(\sigma(t)^2+\sigma(t_2))\). This is implemented as an exact \(\mathbb Q(\zeta)\) invariant, not a floating-point tolerance.

## 3. Actual 12/78 projection requires ONLY one genuine central involution

For actual \(S_s=\operatorname{Hom}_E(H_s,W_s)\), the original source \(6.\mathrm{Suz}\) central order-two element \(t_2\) acts by \(J_s=L_s(t_2)\) with eigenvalues \(-1\) on the faithful 12 and \(+1\) on the nonfaithful dual Sym² 78. Hence
\[
\boxed{\Pi_{12,s}=(I-J_s)/2,\qquad\Pi_{78,s}=(I+J_s)/2,}
\quad \mathrm{rk}\Pi_{12,s}=12,\ \mathrm{rk}\Pi_{78,s}=78,\ \mathrm{tr}J_s=66.
\]
**Type safety:** do not use \(\rho_W(t_2)\) directly as \(J_s\) on the full 65,610D eigensector; \(\rho_W(t_2)\) includes a 729D Weil operator, and the central projection is on the 90D Hom factor **after** dividing out the chosen genuine \(\rho_{H_s}\) extension.

## 4. One real source acquisition and operator pipeline, no new character search

The committed [\`scripts/monster3b_steel_ordinary12_to90.py\`](../../scripts/monster3b_steel_ordinary12_to90.py) performs two strictly separated tasks:

1. \`--acquire\` retrieves Steel's original Magma source on a networked workstation to ignored \`.dashi/monster3b-steel-ordinary12/d12.6Suz.nfdeg2.M\`, preserving SHA256, attribution, original file and a structure/inventory record. It **does not execute Magma text as Python**, publish copyright-sensitive source copies or infer the standard-generator map.
2. Given an *actual source-normalized* JSON of **12×12 matrices** with entries \([a,b]\) meaning \(a+b\zeta\), \`--matrix-json\` derives exact \(78\times78\) and \(90\times90\) matrices, central idempotent rank metadata and trace invariants, keeping the origin, SHA256 and source generator labels. This is a generic **exact functor** and does not assert that an arbitrary user-supplied JSON is already a specific Monster source action.

\`\`\`bash
python3 scripts/monster3b_steel_ordinary12_to90.py --acquire
python3 scripts/monster3b_steel_ordinary12_to90.py --schema
# Once the original Magma module's actual generator conventions have been
# inspected and its source-normalized faithful12 generators exported:
python3 scripts/monster3b_steel_ordinary12_to90.py --matrix-json path/to/steel12.json
\`\`\`

The original file's raw \`.M\` bytes could not be retrieved in this runtime: browsing rejects \`application/vnd.wolfram.mathematica.package\`, and container network DNS is unavailable. **No Magma input file contents, numerical generator matrix entries, source standard generator names or actual source basis correspondence are guessed.** Magma's documented \`ActionGenerators(M)\`, \`GModuleAction(M)\`, and \`Representation(M)\` are the appropriate authentic producer APIs once the original file is opened and its \`ModGrp\` identifier established. The user's already-run GAP source characterization is not requested again.

## 5. Phase, producer–consumer, exact remaining lemmas

**M3B-L10A (original-source acquisition / field alignment, UNPAID):** obtain Steel's actual \`.M\` source and its original \(G=6.\mathrm{Suz}\) module; recover genuine matrix generator names, action side, exact field embedding \(\mathbb Q(\zeta)\), and source standard-word map. Identify its faithful12 character as GAP Irr153 **or** 154 with a *marked* Suzuki central \(C_3\) generator; the other is its \(\sigma\)-conjugate. Mapping to the original published \(6.\mathrm{Suz}.2\) cover/ATLAS generator convention is not inferred from character rows alone.

**M3B-L10B (same Monster Hom intertwiner, UNPAID):** identify the selected normalizer standard generator words with genuine \`mmgroup\` C/D and central-cover relators and construct an original-source \(6.\mathrm{Suz}\)-equivariant isomorphism from Steel's ordinary faithful12 carrier \(V_{12,s}\) onto the **actual** \(S_{12,s}=\operatorname{Hom}_E(H_s,P_sE_{17496}W)\). The previous 28 GF3 source quotient candidate pairs are initial generator alignment data, NOT complex faithful12 matrices.

**M3B-L10C (DERIVED now, numerical source attachment pending):** with 12D actual source matrices, the full selected inner 90D matrices follow by \(A\oplus S_2((A^{-1})^\top)\); the source 210-class trace formula above and C2 projector require no extra 78D mathematical construction. The original outer \(\zeta\leftrightarrow\zeta^2\) action, \(\mathrm{MN3B}\) diagonal class20 K, actual extraspecial centre z and coherent 729 Weil phase remain separate typed structures.

**M3B-L12R (outer gauge / word attachment, UNPAID):** transport the phase-exchanging element \(S_s\to S_{-s}\), source chosen class4D and literal mmgroup element-word correspondence, preserving the correct 6.Suz.2 central-cover scalars. The already source-proved **4D CLASS** does not prove **Hit0 word is 4D**.

**Original producers:** Steel ordinary faithful12 matrices; GAP/CTblLib \`6.Suz\` Irr153/154, original square map and central class signature; Barraclough–Wilson/Bray–Wilson real \`6.Suz.2\`/main/MN3B normalizer; user's authentic \`mmgroup\` 12D GF3 quotient witness; Ibrahim original 12/78 phase/clifford/ Hom and actual 729D Weil extension. **Consumers:** full source 90D \(6.\mathrm{Suz}\) multiplicity character, explicit exact 78/90 operators, genuine Monster same-object \(\operatorname{Hom}_E\) and Paper 10 signed cyclotomic/outer endpoint. Attribution of the symmetric-square family to Nebe; standard character theory and symmetric-functor matrices are prior art.

**Status:** complete inner 12→78→90 mathematical functor and source provider identified; synthetic central-\(C_3\) arithmetic checked locally (not authentic matrices); genuine Steel source bytes and actual Monster group-word/complex Hom transport remain open. Certification intentionally deferred.
