# Monster 3B — P5 integrated workstation implementation (L10A/L10B/L10C/L12R)

**24 November 2026 · PR #1545 · mathematical endpoint first.** This is the canonical implementation handoff for the user's request to complete the remaining source work before their workstation run. It reuses the authentic GAP 4.16dev/CTblLib 1.3.11 character selection and source 4D class-fusion receipts (already paid); original \`mmgroup\` 1.0.8 Heisenberg manifest and powered Hit0 GF(3) quotient; original Steel ordinary \(6.\mathrm{Suz}\) Magma degree12 source; original Ibrahim/JFine characteristic-zero representation-theoretic Hom and Weil owners. No new source-group, alternative faithful78, synthetic Fin90 or unrelated research stack is introduced.

## One command (on workstation with Magma, GAP/CTblLib and mmgroup)

Check out/pull PR #1545 branch \`research/monster3b-mmgroup-atlas-generator-transport-20261123\` targeting \`master\`.

\`\`\`bash
python3 scripts/test_monster3b_p5_endpoint_local.py
python3 scripts/run_monster3b_p5_endpoint.py --all --actual-mod31-hom --timeout 900
\`\`\`

The runner creates one fresh \`build/monster3b-p5-endpoint/run-UTC-PID/\` with \`endpoint_summary.json\` and per-stage logs and original source outputs; it does NOT overwrite previous receipts. If Steel's Magma file uses a \`GModule\` symbol other than \`M\`, inspect \`.dashi/monster3b-steel-ordinary12/source_inventory.json\` and use \`--module ActualSymbol\`. The original Steel file can be supplied explicitly with \`--source-file path/to/d12.6Suz.nfdeg2.M\`; this avoids a network download. The optional actual \(MMV(31)\) full-module source step is selected by \`--actual-mod31-hom\` and may take longer than the basic original group-word/GAP/Magma stages. \`--skip-mmgroup\`, \`--skip-magma\`, \`--skip-gap\` allow source-specific failures to be isolated. **If the original characteristic-zero Monster Hom12 matrices exist**, provide \`--hom <original-char0-Hom12.json>\`; only then may the exact complex 12×12 intertwiner be computed. \`--outer-map <original-6Suz-outer-word-map.json>\` likewise requires authentic source outer generator images.

## L10A — original genuine Steel GModule and original GAP-selected character (implemented)

1. \`scripts/monster3b_steel_ordinary12_to90.py --acquire\` downloads **only** the original Allan Steel \`d12.6Suz.nfdeg2.M\` (minimal-degree faithful ordinary \(6.\mathrm{Suz}\), character-field degree 2, Schur index 1) to a user-local ignored \`.dashi/\` path, records SHA256, and does not execute the downloaded source as Python or commit/redistribute the original code.
2. \`scripts/monster3b_steel_magma_export.py --magma --module M\` loads **the original file in Magma** using its actual \`GModule\` and \`Representation(M)\` producer, extracts all genuine ordinary \(12\times12\) matrices in exact \([a,b]\in\mathbb Q(\zeta_3)\), records original group word labels, orders, \(\operatorname{tr}A\), and \(\operatorname{tr}A^2\). Its original primitive cubic root is retained and the absolute \(\zeta\) label is NOT guessed.
3. \`scripts/monster3b_gap_ordinary12_class_fingerprint.py --run-gap\` uses the ORIGINAL 210-class GAP \`6.Suz\` table, \`Irr[153]\`, \`Irr[154]\), class order and square map. For each original Magma generator/word, emit **all** class positions compatible with its exact order and faithful12 traces, in both Galois orientations. It does not claim the original group standard-generator identity from a matching class fingerprint alone.

**L10A code complete; original source execution/absolute standard-word-to-GAP correspondence remains an input-dependent group identification.** A character table determines a representation *type*, not a canonical abstract-to-Monster element word.

## L10C — no independent 78D construction needed (implemented)

\`scripts/monster3b_steel_ordinary12_to90.py --matrix-json\` reads exact original Steel \(A_g\) and produces
\[
B_g=(A_g^{-1})^\top,\quad
L_{78}(g)=\operatorname{Sym}^2 B_g,\quad
L_{90}(g)=A_g\oplus L_{78}(g),
\]
all over \(\mathbb Q(\zeta_3)\) in explicit ordered quadratic-polynomial basis \(\{e_i e_j:1\le i\le j\le12\}\), with exact character checks
\(\chi_{90}(g)=\chi_{12}(g)+\frac12(\sigma\chi_{12}(g)^2+\sigma\chi_{12}(g^2))\).
It is permitted to leave original Irr153/154 selection \`null\` while the source GAP word/class alignment is unresolved; it MUST NOT silently label an unassigned orientation as selected.

**Mathematical and algorithmic 78/90 derivation complete; numeric matrices are produced only when genuine original Steel matrices arrive.**

## L10B — genuine Monster source words and actual module (implemented at two separately typed levels)

**Full Monster group:** \`scripts/monster3b_mmgroup_canonical_cover_words.py\` consumes the already-sourced \`monster3b-authentic-manifest.json\` and constructs exact original group Hit0 words \(C=(gh^{-1})^{15},D=(hg^3)^8\), checks their existing ATLAS GF(3) intertwiner (one-dimensional Hom and exact alternating form), derives the actual 12-coordinate Heisenberg affine conjugation defects and eliminates ALL of them simultaneously using unique extraspecial corrections \(e(u)\), \(e(v)\) over \(\mathbb F_3\). It produces actual corrected MM word strings plus literal central-cover relator residues (including whether they truly equal original centre powers) and original word orders. It **does not** force nontrivial \(6.\mathrm{Suz}\) central-cover relators to be identity or infer actual class 4D from one power order.

**Original Monster modular Hom vacuum (new genuine carrier):** \`scripts/monster3b_actual_mmv31_hom_projector.py\` constructs the actual \(MMV(31)\) 3B nontrivial centre eigensector, takes **factorized** six commuting B-projectors, and extracts 90 independent actual B-fixed vectors using exact ambient \(\mathbb F_{31}\) row reduction on all 196884 original coordinates. This is an actual same-**source Monster vector** carrier over \(\mathbb F_{31}\), not an abstract 90D fixture. If the canonical corrected C has \(C^2\) acting by pure inversion on B, it constructs its induced \(90\times90\) matrix, \(J^2\) central scalar and exact 12/78 eigenspaces if the source target dimensions are observed. For phase-preserving D it computes the **actual B-vacuum sandwich** \(P_B \rho(D) P_B=k_0(D)L_D\) on those original projected vectors. When \(k_0\ne0\) and the central involution commutes with this action, it extracts actual 12D and 78D mod31 blocks **up to the unknown Weil scalar \(k_0\)**. The optional run checkpoints after 10 independent vectors; no direct characteristic-zero promotion is claimed.

**Actual complex Hom source boundary:** \`scripts/monster3b_ordinary12_hom_outer_weld.py\` solves 144-variable exact \(\mathbb Q(\zeta_3)\) intertwiner equations \(FA_g=B_gF\) only when genuine *characteristic-zero* Monster Hom action matrices \(B_g\) with the SAME source generator-word/gauge convention have been supplied. The original public mmgroup vector model is available in selected **modular** characteristics; \(\mathbb F_{31}\) source vectors and a GF3 quotient intertwiner do not uniquely supply this literal complex Hom basis/representation. Without authentic \(\rho_W\), the script exits **NEEDS_CHARACTERISTIC_ZERO_MONSTER_HOM12_ACTION**, NOT a false success.

## L12R — outer phase, same group cover and 4D (implemented where original source attaches)

The canonical MM words stage records actual \(C\) centre inversion (\(\lambda=-1\)), \(D\) centre preservation (\(\lambda=1\)), exact centre residues and \(C^2\) quotient involution. The source GAP receipt has already selected **source** Monster **4D** uniquely via \`2.Suz.2(5)→6.Suz.2(9)→main(54)→MN3B(33)→Monster(10)\`. A particular user-local corrected C word is NOT automatically proved to lie in 4D.

Given an authentic outer automorphism \(\alpha\) specified on the SAME original \(6.\mathrm{Suz}\) standard-generator words, the exact Qζ solver computes a 12D **semilinear** outer map \(U\) from
\(U\sigma(A_g)=A_{\alpha(g)}U\);
then the matching dual Sym²78 and total 90D outer transport are automatically
\(U_{78}=\operatorname{Sym}^2((U^{-1})^\top)\),
\(U_{90}=U\oplus U_{78}\).
Both \(U\sigma(U)\) and \(U_{90}\sigma(U_{90})\) remain explicit matrices to be compared with the **actual** central-cover/outer-square relators, not arbitrarily set to 1.

**L12R source-word/central-cover equations implemented; selected standard-generator map and complex outer gauge must come from true original sources.** Do not use mod31 or original quotient alone to certify literal Monster class 4D.

## Phase/lemma ledger and residual producer ownership

| Lemma | Executable producer | Necessary authentic input | Mathematical disposition |
|---|---|---|---|
| L10A | Steel acquisition → Magma export → GAP class fingerprint | Original Magma source with correct module symbol; exact GAP 153/154 chars | **Software ready**, actual standard generator→specific 210-class/Monster word map remains source data |
| L10B | MM canonical source word/affine correction → MMV31 Hom → Qζ linear intertwiner | Original MM manifest; optional original complex Monster Hom12 action | **Group and modular algorithms ready**, literal char0 same-object Hom not inferable without char0 original action |
| L10C | Steel 12→dual Sym²78→90 over Qζ | Original 12D generator matrices from Steel | **Exact mathematical and software construction complete** |
| L12R | Original MM centre/relator receipt → source outer word α → Qζ semilinear 12/78/90 | Original outer standard-generator word map and char0 gauge | **Source equations ready**, literal source word/class4D identity and phase-normalization open |

**Existing source producers and actual consumers:** Steel ordinary degree12 Magma GModule, GAP/CTblLib original full 210-class faithful12 and 78 source families and unique class4D fusion, original Dietrich–Lee–Pisani–Popiel Monster group words, original mmgroup modular faithful Monster action, original Barraclough–Wilson/Bray–Wilson group-cover \(E H\) and diagonal C3 kernel; downstream Ibrahim actual \(\operatorname{Hom}_E(H_s,W_s)\), original phase-resolved Clifford 12/78 and the Weil-cocycle cancellation, \`Monster3BActualZetaPromotionPipelineExact\`, Paper 10. The source's original irreducible selection is **nonfaithful Nebe dual Sym²78** with \(C_2\) trace +66 and original source class4D; DO NOT reopen faithful78/Sym² family selection or invent a new abstract 90D representation.

**No source execution claimed in this conversation:** no Magma binary, CTblLib GAP runtime or \`mmgroup\` in this container. The committed local pure-algorithm smoke suite may be run first; a pending external source should yield explicit statuses, not fictitious success.
