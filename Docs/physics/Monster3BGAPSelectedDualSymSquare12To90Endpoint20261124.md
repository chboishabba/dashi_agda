# Monster 3B — authentic GAP selects the dual-symmetric-square 90D source type

24 November 2026 · PR #1545 · mathematical endpoint FIRST; not certification.

## Authentic workstation result (reported, not independently replayed here)

The user's \`run_monster3b_gap_endpoint.py\` completed both original GAP stages with \`EXIT_0\` (10.142s / 6.669s), \`MAIN_AND_FUSION_SOURCE_MATCHED\`, using GAP \`4.16dev\` and CTblLib \`1.3.11\`. Run directory \`build/monster3b-gap-endpoint/run-20261124T043102Z-3955713\`. The original 41,490-byte raw main JSON has not been mounted here; the user supplied its complete source-results summary and its SHA256 \`507a9508e6377fd51d9e4b728690191451071cb537ed296922fc33d71d196598\`. The original fusion JSON SHA256 was reported as \`4b5b12cdfad130b882acac48a06e9d3ed84a6a470062b6f86f74beaa31b6c7e2\`. These are user-reported authentic source results, not invented local execution or independently inspected raw bytes.

- Faithful source \`6.Suz\` degree12 Irr positions **153,154**: \`\\chi_{115}\` and \`\\chi_{115}^{\\ast2}\`.
- Monster-selected \`6.Suz\` degree78 Irr positions **79,80**: \`\\chi_{78}\` and \`\\chi_{78}^{\\ast2}\`. The original GAP full-class matcher returns **nonfaithful, full-character equal to Nebe's \`Sym²(12)\`/dual family** (\`selected_78_faithful=false\`, \`selected_78_is_nebe_sym2_full_character_equal=true\`). The former faithful-78 target is NOT the actual selected family.
- Actual selected degree90 Suzuki central C2 trace **+66**, not -90; source common central C3 phase pairings **2**.
- Main class20 K-diagonal trace pairs **[17496,-8748]**, **[113724,-56862]**. Source main descending Irr **327** and **253** map to MN3B Irr **146** and **109**, each multiplicity ONE in the Monster weight-two restriction. True extraspecial 3B centre is main class **2**, NOT diagonal K class **20**, and has selected traces \(-8748,-56862\).
- The exact original stored source four-class chain is **2.Suz.2 class 5 → 6.Suz.2 class 9 → main class 54 → MN3B class 33 → Monster class 10 = 4D**. This uniquely chooses the *source class* under its stated square-to-2B premise. It does **not** identify any user-local \`mmgroup\` Hit0 word with that element or class.

Original producers: Barraclough–Wilson, Bray–Wilson, Breuer–Magaard–Wilson, CTblLib, Nebe; scripts \`monster_3b_suzuki_main_quotient_match.g\`, \`monster3b_atlas_suz2b_monster_4class_source_fusion.g\`, \`run_monster3b_gap_endpoint.py\`; Ibrahim 3B phase-resolved/linear Hom source owners.

## The stronger SAME-PHASE 90D theorem (no guessed representation)

Let \(G=6.\mathrm{Suz}\), \(V_k\) one of the two actual selected faithful *complex* 12D irreducibles. For central order-three \(t_3\in G\), write \(V_k(t_3)=\zeta^kI\), \(k\in\{1,2\}\). Faithfulness makes \(k\ne0\). Then \(\operatorname{Sym}^2V_k\) has central scalar \(\zeta^{2k}=\zeta^{-k}\), while \(\operatorname{Sym}^2(V_k^\vee)\) has central scalar \(\zeta^{-2k}=\zeta^k\).

The **full 210-class** source equality identifies the selected 78 conjugate family as the direct/dual Sym² of the source 12 conjugate pair. The two exact same-C3 12/78 pairings force the *dual* Sym² of the **same** 12 phase (the direct square carries the opposite phase). Thus, after fixing the common genuine 729-extension gauge,
\[
\boxed{S_k|_{6.\mathrm{Suz}}\cong V_k\oplus\operatorname{Sym}^2(V_k^\vee).}
\]
This is a theorem about the *source-selected representation type* (up to a source-compatible intertwiner), not a numeric same-Monster-basis equality. For any genuine **complex faithful12** source generator \(A_g\in GL_{12}(\mathbb C)\), the corresponding whole 90D inner action is derived by
\[
\boxed{L_k(g)\sim A_g\oplus\operatorname{Sym}^2\big((A_g^{-1})^\top\big).}
\]
Do **not** substitute the original ATLAS **GF(3)** quotient \(12\times12\) matrices for the different complex faithful 12D matrices. The outer element exchanges the paired \(k\) sectors and requires source gauge/word alignment.

## A TWO-TERM replacement for the 210-class projector on the actual Hom carrier

For the genuine source central Suzuki involution \(t_2\in Z(6.\mathrm{Suz})\), let \(J_s=L_s(t_2)\) on the **actual** \(\operatorname{Hom}_E(H_s,W_s)\) (with the original 729D factor removed). The faithful12 has \(J_s=-I_{12}\); dual Sym²12 has \(J_s=+I_{78}\). Consequently
\[
J_s^2=I,\qquad\operatorname{tr}J_s=-12+78=\boxed{66},
\]
\[
\boxed{P_{12,s}=\tfrac12(I-J_s),\quad P_{78,s}=\tfrac12(I+J_s)}
\]
are canonical, orthogonal, of ranks \(12,78\). The original outer normalizer phase map preserves the unique central-order-two source element and maps each block to its opposite-\(\zeta\) phase copy. **Important:** \(\rho_W(t_2)\) on the full \(65{,}610\)-dimensional sector includes the nontrivial 729D Weil action, so one must use \(J_s\) on the Hom carrier, not these two terms directly on \(W_s\).

## Mathematical endpoint now remaining

The selected faithful-vs-Sym² 78 branch, general 78D character search, generic 90D matrix construction, and original **source** four-class ambiguity are **closed**. The unsolved source-specific work is (i) original complex **faithful12** source generator matrices with genuine \(6.\mathrm{Suz}.2\) cover/gauge, (ii) an original same-object intertwiner into the Monster's 12D Hom subspace, and (iii) genuine user-local \`mmgroup\` C/D word-to-H/class-4D identification and central phase lift. Once (i)-(ii) are attached, the 78 and entire 90D actions follow from dual Sym² by an appropriate original intertwiner; one must not claim numerical 78D operator entries before that attachment. The original printed full source 12/78 character rows and group normalizer/Hom consumers remain in force.

**New GAP source improvement (not a request to rerun):** retain explicit same-C3 and dual/direct Sym² original Irr-position pair arrays, and require the two same-C3 pairings of a Nebe-selected family to be the **dual** Sym² pairs. Original report already gives full family equality and two same-C3 matches; absolute a/b naming has NOT been inferred from the unmarked count. No formal kernel/certification cycle is initiated.


## 6. Existing REAL characteristic-zero 6.Suz degree12 matrix producer FOUND

**External original producer: Allan Steel, Ordinary Representations Database** (<https://magma.maths.usyd.edu.au/~allan/reps/db/>), whose published selection explicitly lists **degree 12, group 6.Suz, characteristic-field degree 2, Schur index 1** (faithful; its page marks the degree as minimal faithful). The exact linked file is **\`d12.6Suz.nfdeg2.M\`** at <https://magma.maths.usyd.edu.au/~allan/reps/db/d12.6Suz.nfdeg2.M>. This is a **Magma-readable ordinary (characteristic-zero) representation source**, NOT the finite ATLAS \`6SuzG1-f7r12aB0\`, \`f13\`, \`f25\` data and NOT the 12D quotient \(\mathbb F_3\) symplectic representation. Attribution to Steel's original ordinary representation construction must be retained; no matrices are invented or copied from the download.

**Precise acquisition boundary:** the verified web listing and file URL establish an existing source for the required ordinary degree12 matrix representation. Raw \`.M\` bytes were NOT retrieved/inspected in this session (web returns unsupported source content type; sandbox network DNS unavailable). It is not yet known whether the Magma source is immediately GAP-readable, supplies both Galois-conjugate blocks or standard-word correspondence, or whether it is licensed for redistribution. **Do not vendor silently or claim its matrices were executed.**

**Next endpoint cut, NO new matrix construction:** obtain/read the cited original \`.M\` source, recover original standard \`6.Suz\` generator words and the quadratic character field, check its original selected 12 character equals GAP source \`Irr(6.Suz)[153]\` or \`[154]\` in the identical 210-class order, then align its standard generators with source \`6.Suz.2\`/MN3B/MM words and chosen 729 phase. Once a concrete \(12\times12\) original complex standard-source \(A_g\) is aligned, the selected \(78\) and \(90\) matrices are **functorially** given by \(\operatorname{Sym}^2((A_g^{-1})^\top)\), and the last remaining step is same-object Monster Hom isotypic intertwiner and outer phase swap. This is an **actual external producer discovery**, not proof that all remaining endpoints have been paid.

Source context: GAP AtlasRep's published 6.Suz available matrices list 12D over GF(7), GF(13), GF(25), but no listed ordinary 12D. Primary Steel database linked above fills exactly that missing characteristic-zero data-source role.


### Minimal field sharpened to \(\mathbb Q(\zeta_3)\)

Steel's listing gives character-field degree **2** and Schur index **1** for the faithful ordinary degree12 \(6.\mathrm{Suz}\) representation. Since the central order-three Suzuki generator acts on this faithful irreducible as \(\zeta_3^{\pm1}I\), its character value \(12\zeta_3^{\pm1}\) generates \(\mathbb Q(\zeta_3)\). This is itself degree two over \(\mathbb Q\); hence the character field is **exactly**
\[
\boxed{\mathbb Q(\zeta_3)=\mathbb Q(\sqrt{-3}).}
\]
Schur index one permits the ordinary representation to be defined over that very field. Consequently the selected \(V_{12}\oplus\operatorname{Sym}^2(V_{12}^\vee)\) **inner \(6.\mathrm{Suz}\) 90D action** may be represented entirely over \(\mathbb Q(\zeta_3)\), because taking inverses, transposes, symmetric squares and direct sums does not extend the base field. This result concerns the 12/90D *multiplicity representation*; it does not assert that all \(729\)-dimensional Weil operators or the original full Monster matrices are already represented in the same source basis. It also does not supply the actual 12D matrix entries, which remain in Steel's original external Magma file pending inspection.
