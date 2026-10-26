# ATLAS \(2.Suz{:}2\) D4: exact source-compatible \(4E\) submodule / H4 bridge

**26 October 2026 | Original source owner PR #1098 | Model owner PR #1148 | Monster characters PR #1250.**

## Original mathematics and unchanged source attribution

1. **ATLAS of Group Representations** owns the original \(2.Suz{:}2\) GF(3) dimension-12 standard matrices and Suzuki generator presentation. The existing #1098 manifest \`data/atlas/monster3b_suz12_source_manifest_20261012.json\` stores original byte hashes, copy location and acquisition lineage. The copied mirror is not an independent original source. https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Suz/
2. **Barraclough–Wilson (2007)** own the original Monster \(3B\) normalizer and \(3^{1+12}\) character and quotient computation (DOI 10.1112/S1461157000001352). **Breuer–Magaard–Wilson** (2026, *J. Algebra* 703; DOI 10.1016/j.jalgebra.2025.09.034), with the published original executable 2024 supplementary protocol, distinguish the auxiliary split \(H/X\) from the selected diagonal \(H/D_i\), https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/htm/ctblm.htm, §9. The finite source subgroup is in the original ATLAS \(2.Suz{:}2\) representation. It is NOT automatically a selected Monster generator/element word.
3. **Serre** and ordinary finite representation theory own the character decomposition \(D_4\) into \(A_1,A_2,B_1,B_2,E\) over characteristic not dividing 8.
4. **Earlier repository implementation #1098** owns the actual source-word D4, its original invariant nondegenerate alternating form \(J_{12}\), the exact source fingerprint, and the H6 central cocycle. New work herein only constructs a **D4-stable 8-dimensional symplectic submodule from those exact objects**, with fully explicit matrices and a different \(4E\) representation.
5. **Earlier repository #1148** owns the geometric nine-cell JFine \(2A_1+B_1+B_2+2E\) eight-trit module (relative coordinates) and the modified \(A_1+A_2+2B_1+2B_2+E\) model. These are NOT the same D4 representations as the new ATLAS \(4E\) module. Ibrahim Snowball/Attribution owners retain their original claim-type and cross-source rules.

## Newly completed *source-finite* symplectic construction

Let \(M,R\in GL_{12}(\mathbf F_3)\) denote the **pre-existing source word D4** (\(M^2=1,\ R^2=-1,\ MRM=R^{-1}\)), and let the original source \(J_{12}\) satisfy
\[
R^T J_{12}R=J_{12},\qquad M^TJ_{12}M=-J_{12}.
\]

1. Use the literal source matrix projector \(P_+=(I+M)/2=2(I+M)\) over \(\mathbf F_3\). It has rank **6**. The eigenspace \(L_+=\ker(M-I)\) is Lagrangian, since for \(v,w\in L_+\), \(J(v,w)=-J(v,w)\) and 2 is invertible mod3.
2. Define \(B(v,w)=J(v,Rw)\) on \(L_+\). Because \(R^{-1}=-R\) and \(J\) is alternating, \(B\) is a **symmetric**, nondegenerate bilinear form of dimension six. Exact rank6/source matrix symmetry are verified.
3. Extract a lexicographically first 4-dimensional subspace \(A\subset L_+\) on which \(B_A\) is nonsingular. Let \(Y=RA\cdot B_A^{-1}\). Set \(X=[A\mid Y]\), a **12×8** explicit embedding. Then
\[
X^TJ_{12}X=J_8,\qquad
RX=XR_8,\quad MX=XM_8,
\]
where
\[
R_8=\begin{pmatrix}0&-B_A^{-1}\\ B_A&0\end{pmatrix},
\qquad
M_8=\begin{pmatrix}I_4&0\\0&-I_4\end{pmatrix}.
\]
Check \(R_8^2=-I_8,\ M_8^2=I_8,\ M_8R_8M_8=R_8^{-1}\), symplectic multiplier +1 on R and −1 on M. This is a full D4 and alternating-form **intertwiner**, not merely a trace or degree match.
4. The \(B\)-orthogonal complement \(A^{\perp_B}\subset L_+\) has dimension two and induces a source-stable symplectic \(4\)-space orthogonal to \(X\). The exact source decomposition is
\[
(\mathbf F_3^{12},J_{12},D_4)
\cong (4E,J_8)\ \perp\ (2E,J_4).
\]
All eight original trits are retained; no extra field/cardinality numerology is introduced.
5. Via the already-owned normalized-centre gauge \(t=c+a\cdot b\), the source \(R_8,M_8\) lift to group automorphisms of the standard **four-pair \(H_4\)** law \((a,b,c)(a',b',c')=(a+a',b+b',c+c'+b\cdot a')\). The new independent local implementation checks all \(3^8\) quotient vectors against **nine Heisenberg generators** and **both** D4 generators: \(3^8\cdot 9\cdot 2=\mathbf{118098}\) product equalities, in addition to the exact matrix identities. This is a finite calculation; the actual Agda theorem/kernel for the concrete 12×8 matrix is pending.

### What this bypasses, and what it cannot

**Bypassed:** the old specific nonembedding objection 'an eight-dimensional H4-sized source-compatible symplectic D4 carrier cannot occur inside this 12D ATLAS action'. It **does** occur, of type \(4E\). It can be transported through the pre-existing #1148 abstract \(H_4\)-phase Fourier equivalence once the D4 action on its input is replaced by the actual source-compatible \(4E\).

**Not bypassed:** The original geometric JFine action, or #1148's \(A_1+A_2+2B_1+2B_2+E\), has a half-turn-fixed 6D subspace and \(r^2\) trace **+4** on the quotient. The source \(4E\) has \(r^2=-I_8\), fixed dimension 0, trace **−8**. Since \(r^2\) is central in D4, these are *not isomorphic D4 representations*. Any D4-equivariant injection of the old modified 8D module into the source12D with \(r^2=-I_{12}\) would kill the +1 eigenspace, and thus cannot be injective. The source-compatible alternative changes the D4 action, not the original geometry for free.

**Still open and not 'locally passed':** (a) source ATLAS generator ↔ BMW auxiliary H/X 14D action exact same-generator/basis weld; (b) actual selected Monster diagonal \(H/D_i\) and corresponding class fusion; (c) full original \(6.Suz\) degree78 family/main→MN3B→Monster character receipt in #1250; (d) actual E-module \(W_\zeta\) multiplicity/Hom normalizer operator in #1098; (e) Agda kernel proof of concrete source matrix, not just Agda-computable character equations; (f) any physical claim.

## Pareto/Ibrahim/snowball next tests and execution

**New source-finite checkpoint** (this PR):

\`\`\`sh
bash scripts/check_monster3b_gf729_d4_source_ambient_cut.sh
# Or independently:
python3 scripts/monster3b_atlas_d4_fourE_h4_source_submodule.py \
  --receipt build/monster3b_atlas_d4_fourE_source.json
\`\`\`

Source-written Agda import:
\`DASHI/Moonshine/Monster3BAtlasD4FourESourceSubmoduleExact.agda\`
from \`Monster3BActualKernelCharacterRound4Validation.agda\`. Its type-level \(4E\) versus old A2-character exact equations are NOT a machine-certified 12×8 matrix.

**Next high-value consumer is not more finite geometry**: execute the existing #1250 \`scripts/check_monster_3b_suzuki_main_quotient_match.sh\` and \`scripts/monster_3b_suzuki_all_conductors_export.g\` with original CTblLib/GAP and pin a source table+class-fusion certificate. Alternatively, extract a unique exact source table/fusion receipt from the original BMW/BW supplementary data, with explicit original class/character labels and unchanged checksum. Then instantiate the existing #1098 Hom/action and whole-character-first Ibrahim route. Do not replace a missing original-source receipt with another D4-based trace coincidence.

**Status discipline:** local exact finite calculations passed; newly committed source is present in GitHub and runner, but exact-head committed-checkout execution and Agda/GAP kernel/character receipt were not observed. Source provenance preserved at each edge.


## Primary-web-source fusion recut: source half-turn is Monster 2B, not 2A

**Additional ORIGINAL SOURCE ROOT newly recovered:** Simon P. Norton & Robert A. Wilson, *Anatomy of the Monster: II*, *Proceedings of the London Mathematical Society* 84 (2002), 581–598, DOI [10.1112/S0024611502013357](https://doi.org/10.1112/S0024611502013357). The relevant paper text was read through a [reproduction of its original contents](https://paperzz.com/doc/8563265/anatomy-of-the-monster--ii---school-of-mathematical-sciences) (§1 Lemma 3 discussion), **not** treated as an independently authored article; the journal's primary DOI record authenticates the original paper. It explicitly assigns the *central* involution \(-1_A\) in the Monster \(3B\)-centralizer \(2.Suz\) to Monster conjugacy class **2B** (and additionally identifies another \(+2A\) Suzuki class that also fuses to Monster 2B). This is a historical pre-existing result, NOT a new group-theoretic discovery.

**Independent original source root:** R. W. Barraclough & R. A. Wilson, *Conjugacy Class Representatives in the Monster Group*, *LMS J. Comput. Math.* 8 (2005), 205–216, DOI [10.1112/S1461157000000966](https://doi.org/10.1112/S1461157000000966), original **Table 2** visibly gives Monster **2A** as a square of an element in class **4B** (entry \`2A: 4B(0)\`). Different 2005 paper and result, but sharing Wilson as author does not turn it into independent confirmation of the first source's \(-1_A\) class: it supplies a different *power-map premise*.

**Original SAME STANDARD GENERATOR confirmation:** Barraclough–Wilson (2007), §3.1, p. 163 [original manuscript](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B22657E05FCEDF5E9017AE6A4421FB96/S1461157000001352a.pdf/the-character-table-of-a-maximal-subgroup-of-the-monster.pdf) explicitly constructs the normalizer model from original ATLAS standard-generator matrices \((C_2,D_2)\) for \(2.Suz{:}2\) on \(\mathbf F_3^{12}\) and \((C_6,D_6)\) for \(6.Suz{:}2\), with the named quotient map \(C_6\mapsto C_2,\ D_6\mapsto D_2\). Thus our original #1098 source pair uses the very same *type and generator convention* as the published source quotient model (after the independently checked ATLAS semi-presentation). This is much stronger support than merely a matching "Suz" name, but still NOT literal Monster \(H/D_i\) generator words or the absolute phase choice.

**Exact group inference, with source-role boundary:** The newly verified source \(D_4\) has \(r^2=-I_{12}\) and multiplier+1, hence \(r^2\) is the unique central involution of its \(2.Suz\) subgroup. It therefore carries the original published **2B** fusion in the actual Monster \(3B\)-centralizer, upon the original ATLAS-to-Monster subgroup identification. Any order-two lift through the odd extraspecial normal kernel is conjugate under the kernel (Schur–Zassenhaus in the preimage of \(C_2\)), so the 2B assignment is independent of which complementary lift is chosen. Since \(4B^2\) is Monster 2A, **this specific source \(r\) cannot be Monster class 4B**. The actual source Monster class of \(r\) among order-four classes remains unidentified; it requires a further original fusion/class receipt. Do not promote this to a class name for the full D4 without another test.

**Consequences for earlier frontiers:** The conditional JFine C4 source screen using \((r:4B,\ r^2:2A)\) is a valid screen of its *own hypothetical class pattern*, but it **cannot describe the actual ATLAS subgroup constructed here**. Likewise the old full pointed-D4 residual character \([53,-3,-3,-49,-49]\) assumes this 4B/2A class pattern and remains a legitimate conditional obstruction, not a result for the newly sourced \(r\). The old bound \(|\operatorname{tr}_{W_\zeta}(r^2)|\le90\) is consistent with the 2B family, and the source-compatible \(4E\) eight-trit half-turn itself has no fixed nonzero quotient vectors. Do not reissue those traces with invalid source substitutions.

**Formal/source interface:** \`DASHI/Moonshine/Monster3BAtlasD4PublishedTwoBClassGateExact.agda\` imports existing claim-attribution/Snowball owners, separately credits Norton–Wilson (2002), Barraclough–Wilson (2005, 2007), and builds a typed \`twoA ≠ twoB\` contradiction for a putative \`source-r-is-4B\` assignment *under explicitly source-attributed class facts*. An Agda source equality is not a kernel proof of the original external fusion; a direct GAP/Monster element-word replay of the selected diagonal quotient is not claimed. This is a **P1 partial paid by primary scholarship, with P0 exact-generator quotient and actual selected-78 still unexecuted**.
