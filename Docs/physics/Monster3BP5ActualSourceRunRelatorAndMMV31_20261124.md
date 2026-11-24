# Monster 3B — first authentic integrated P5 run: actual Monster cover and 90D MMV(31) vacuum

**24 November 2026 · PR #1545 · source-specific mathematical P5 result, NOT proof-certification.** Provenance: user-supplied workstation run report ("Monster 3B — P5 Integrated Workstation Execution Report") from \`research/monster3b-mmgroup-atlas-generator-transport-20261123\` at prior GitHub head \`ad2ceb1aa06e42f84903c682e053851230b21b8a\`. The original machine-local JSON/NPZ binary files were not uploaded here, so we accurately record the report's **observations** rather than pretending independent file-by-file or group-kernel readback.

**Run directory on user's workstation** (NOT a web URL): \`build/monster3b-p5-endpoint/run-20261124T071452Z-174442/\`. Run commands: \`python3 scripts/test_monster3b_p5_endpoint_local.py\`; \`python3 scripts/run_monster3b_p5_endpoint.py --all --actual-mod31-hom --timeout 900\`.

## 1. Reported stage receipts

| Stage | Reported runtime | Result | Mathematical/source status |
|---|---:|---|---|
| \`local_tests\` | 0.88 s | PASS pure algorithms | No source Monster theorem inferred |
| Steel \`--acquire\` | 0.24 s | EXIT_0 | Original \`d12.6Suz.nfdeg2.M\` **now exists on workstation**, SHA/provenance recorded |
| Steel Magma GModule exporter | 0.12 s | EXIT_2 | **Magma binary absent** (\`Magma not found on PATH\`); no complex ordinary12 generator entries |
| Genuine full \`mmgroup\` canonical words | 78.96 s | EXIT_0 | Exact actual MM corrected C/D cover, affine Heisenberg lift paid |
| Genuine \`MMV(31)\` B-vacuum | 77.94 s | EXIT_0 | 90 independent Monster modular vectors and \(C^2\) 12/78 splitting, D block sandwiches |

Consolidated runner status \`STAGED_MATHEMATICAL_ENDPOINTS_WITH_REMAINING_SOURCE_ATTACHMENT\`: **not** the same as saying every lemma endpoint passed.

## 2. Literal full-Monster group relations: the unique printed central residue

Corrected source Hit0 words are full actual Monster \`MM\` elements, after solving the 12D noncentral affine E defect. Reported original receipt \`mmgroup_canonical_cover_hit0.json\` has

\[
\boxed{C^4=1,\quad D^3=1,\quad (CD)^{56}=1,\quad C^2=(CD)^{28}.}
\]

Let \(R(C,D)=c\,d\,c\,d\,c\,d\,d\,c\,d\,d\), with lowercase \(c=C^{-1}\), \(d=D^{-1}\), exactly the ten-letter original ATLAS semipresentation relator. Its actual Monster lift satisfies
\[
\boxed{R(C,D)^7=z_{3B}^{\,1}\ne1.}
\]
Together with the already original GF3 quotient order-seven condition, this forces **actual \(\operatorname{ord}(R)=21\)**, and \(R^7\) is the **specific original \(3B\) centre**, not a generic untyped scalar. This is a genuine *central-cover relator*, not a contradiction to an order-seven **quotient** presentation.

**Critical signed correction (do not assume \(z\) central in full normalizer).** In the original extraspecial group \(z=z_E\) is central, but the outer \(C\) **inverts it**: \(CzC^{-1}=z^{-1}\); \(D\) preserves \(z\). For \(C'=z^aC,D'=z^bD\), \(a,b\in\mathbb F_3\), inverse letters contribute \(+a\) and \(-b\) respectively, conjugated by the sign \((-1)^{\#\mathrm{preceding\ }c}\). For the literal ten-letter \(R=cdcdcddcdd\), the signed sums of both contributions are **zero**. Thus
\[
\boxed{R(z^aC,z^bD)=R(C,D)}
\]
for all nine pairs \((a,b)\). Also \((z^aC)^4=C^4\) and \((z^bD)^3=D^3\). The nontrivial relator is therefore **rigid under simple central rephasing** in the actual signed cover. The statement \((z^aC)^4=z^a\) would be false here and MUST NOT enter source code or Paper 10. This gauge invariance does **not** show the entire group extension is nonsplit, nor does it give a literal 4D class for the user-local corrected \(C\).

This exact sign algebra is now part of \`monster3b_mmgroup_canonical_cover_words.py\` (zero extra expensive \`mmgroup\` calls): \`signed_relator_rephase()\` produces all nine signed F3 cases and the source receipt records the reported order-21 consequence. Both workstation-reported code errors were corrected on PR #1545:
- \`monster3b_atlas_mmgroup_cross_source_intertwiner_gate.py\`: Hom kernel direction is \`kernel([(b,c),(cand,d)])\`, so \(\ C T=T b,\ D T=T\,cand\); previous order silently reversed this.
- \`monster3b_mmgroup_canonical_cover_words.py\`: actual affine correction rows are \(\omega(u,v)=u_b\cdot v_a-v_b\cdot u_a\), encoded as \`[(-x)%3 for x in v[6:]]+list(v[:6])\`; the original unary-minus-on-list expression was not executable. Shared \`correction_rows()\` now owns both the selftest and the full-group runtime path. A nontrivial conjugacy regression was added to the pure-algorithm suite.

## 3. Actual Monster-module multiplicity source in characteristic 31

The source \`monster3b_actual_mmv31_hom_projector.py\` constructs \(\mathbb F_{31}\)-linear *actual Monster vectors* in the 196884-dimensional native MMV module, using the actual E centre and six B generators:

\[
P_{\zeta}=\tfrac13(I+\zeta^{-1}\rho(z)+\zeta^{-2}\rho(z^2)),\quad
P_B=\prod_{i=1}^6\tfrac13(I+\rho(B_i)+\rho(B_i)^2),
\quad\zeta=5\in\mathbb F_{31}.
\]

The workstation report records **90 actual independent B-vacuum vectors**. The original corrected \(C^2\) induces an involution \(J\) on this genuine 90D modular carrier with \(J^2=I\), and **actual eigenspace dimensions \(+1:78\), \(-1:12\)**, matching the already source-selected complex \(-I_{12}\oplus I_{78}\) character type. The actual \(D\) vacuum sandwich commutes with \(J\) and the script produced separate source-derived \(12\times12\) and \(78\times78\) modular block matrices.

This is much stronger than an ungrounded \(\mathrm{Fin}(90)\) representation: its vectors are derived from **the original Monster action itself**. At the same time, a B-vacuum sandwich is \(k_0(D)L_D\) with **unknown Weil-vacuum coefficient** \(k_0(D)\) until the original \(729\) extension gauge is fixed. \(\mathbb F_{31}\) eigenvectors are NOT literal \(\mathbb Q(\zeta_3)\) matrices or a characteristic-zero Monster-Hom intertwiner.

Notably **\(31\nmid |6.\mathrm{Suz}|=2690072985600\)** (factorization \(2^{14}3^8 5^2\cdot7\cdot11\cdot13\)); modular \(6.\mathrm{Suz}\) representations in characteristic31 are semisimple (Maschke). This helps design a direct modular reduction of **Steel's original ordinary faithful12** once source generator words match, but does not itself supply the missing isomorphism or the complex field embedding. \(\zeta=5\) and its conjugate \(\zeta^{-1}=25\) provide two **separate marked** mod31 phase orientations; do not silently identify them.

**Reported machine-local artifacts** (not included as binary attachments in this turn):
\`actual_mmv31_hom/mmv31_hom_status.json\`,
\`actual_mmv31_hom/actual_C2_on_90_mod31.npz\`,
\`actual_mmv31_hom/actual_C2_12_78_mod31.npz\`,
\`actual_mmv31_hom/actual_D_12_78_vacuum_sandwich_mod31.npz\`.

## 4. Endpoint ledger and next mathematical source weld

- **L10A:** actual original Steel \`.M\` **acquired**; source file **not executed** since \`magma\` unavailable. Extracting faithful ordinary12 matrices and matching both original GAP Irr153/154 class rows still open.
- **L10B:** actual canonical Monster \(C,D\) full-group words, exact signed relators and a genuine **mod31** Monster 90D vacuum with 12/78 eigenblocks **paid by workstation report**. Standard \(6.\mathrm{Suz}\) word identity, Weil scalar and characteristic-zero source Hom intertwiner still open.
- **L10C:** exact \(A\oplus\mathrm{Sym}^2((A^{-1})^\top)\) operator functor already implemented; numeric original complex matrices remain blocked by L10A's Magma execution / alternative exact source-parser acquisition.
- **L12R:** exact full-Monster group central cover relators and outer z-inversion now **paid**; original published source **class** 4D already paid from GAP. The **literal MM word→class4D**, full source \(\alpha\) word map and characteristic-zero outer \(90\)-intertwiner/729 Weil gauge are still open. The \(R^7=z\) relation is the important new central-phase input, not a failure to identify class4D.

**Original producers:** Steel's ordinary \(6.\mathrm{Suz}\) 12D Magma module; authentic 2026 Dietrich–Lee–Pisani–Popiel MonsterSubgroups word source and mmgroup; original GAP/CTblLib Barraclough–Wilson/Bray–Wilson/Suzuki table + Nebe Sym²78 full character source; user's literal \`MMV(31)\` receipts. **Consumers:** exact \(\mathbb Q(\zeta_3)\) source representation and its mod31 reductions, characteristic-zero \(\operatorname{Hom}_E(H_s,W_s)\) weld, original outer/Weil source gauge, Ibrahim phase-resolved 12/78, Paper 10.

**Work strategy:** do not restart the full 78/90 original GAP source search, the 28 quotient witnesses or the 78s full Monster source projection. The next high-value original-source action is inspecting the **already cached Steel \`.M\`** and making a Magma-free exact extraction if its literal format permits, or executing its original Magma module if Magma is made available; then compare its 12D reduction (ζ→5 or 25) with the genuinely original MMV31 12D source block using the correct source group words and residual \(R^7=z\). One source-alignment programme, not piecemeal certificates.

**Provenance boundary:** authentic workstation execution details are transcribed from the supplied P5 report; no independent access to workstation paths, original JSON or \`.npz\` was available here. This document records source acceptance with that explicit boundary and is not a claim of full endpoint theorem certification.


## 5. New source-inner generator reduction: two authentic modular 12D actions

**After the reported workstation run, a further exact generator reduction was implemented; it has NOT been re-executed on the workstation.** Let \(G=\langle C,D\rangle\le\mathbb M\), and define the sign homomorphism \(\lambda:G\to\{\pm1\}\) from its action on the selected centre \(z_{3B}\), with \(\lambda(C)=-1,\lambda(D)=1\). The Reidemeister–Schreier transversal \(\{1,C\}\) gives a generating set for its centre-preserving kernel:

\[
\boxed{\ker\lambda=\left\langle D,\;CDC^{-1},\;C^2\right\rangle.}
\]

This is an exact **group-theoretic** result about the actual generated subgroup \(G\), not a claim that \(G\) has already been proven equal to the entire original published normalizer \(H\). The corrected Monster element \(CDC^{-1}\) has order three and preserves \(z\), so it supplies a **second independent source inner generator** for the original \(90D\) modular B-vacuum, in addition to the already-observed \(D\). The actual Monster word is derived directly as a group product of the already reported corrected \(C,D\), not invented.

**New committed consumer** \`scripts/monster3b_actual_mmv31_hom_projector.py\` retains every existing \`D\` artifact and additionally, when a canonical cover receipt is given, computes the genuine projected \(90D\) \(CDC^{-1}\) vacuum sandwich over \(\mathbb F_{31}\), its rank, cubic scalar diagnostic, and, if it commutes with the source \(C^2\) involution, the induced \(12D\) and \(78D\) blocks on the *same original modular eigenbasis*. It writes \`actual_CDCinv_vacuum_sandwich_mod31.npz\` and \`actual_CDCinv_12_78_vacuum_sandwich_mod31.npz\` conditionally, preserving the source \(k_0(CDC^{-1})\) Weil-vacuum scalar as **unknown**, just like \(k_0(D)\).

These two phase-preserving group words replace a single-generator modular diagnostic with a **source generator pair** for the index-two kernel. They are a more useful comparison target for a future exact \(\mathbb Q(\zeta_3)\to\mathbb F_{31}\) reduction of Steel's faithful12 matrices. Scalar normalization and original abstract-to-MM word map remain genuine mathematical inputs, and no new modular execution is falsely claimed.
