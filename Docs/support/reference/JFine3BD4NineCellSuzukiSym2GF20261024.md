> **25 OCTOBER 2026 — PRIMARY-SOURCE MAX-CUT CORRECTION (latest):** Barraclough–Wilson §5.1 permits *any* irreducible \(6.\mathrm{Suz}\) character as the inflated 729 tensor factor. Earlier faithful-78 **preselection** in the repository main-quotient GAP script was a local filter, NOT the Monster's proven selection. PR #1250 now scans **all** degree-78 outer families and requires the original full main-table split, exact MN3B descent, and positive occurrence in the restricted Monster character to select exactly one. The source-selected family's faithfulness and central C2 trace (either -90 or +66 for the 90-sector) are **OUTPUTS**, not preconditions. Nebe's Sym²78 and faithful78 remain different 6.Suz representations when their central C2 actions differ. Any earlier claim that the Monster *already selects* faithful78 is superseded. See [actual 6.Suz source-family ledger](./Monster3B6SuzExistingSourceFamilyMaxCut20261025.md). The matcher and its revised validator are source-written; no GAP/Agda execution receipt is available in this turn.\n\n> **25 October 2026 — source-family correction:** the existing full Monster-to-6.Suz quotient matcher selects *faithful* degree-78 characters, while Nebe's Sym²(faithful12)=78 descends to 3.Suz and is nonfaithful to 6.Suz. Matching C3 phases or norm8100 cannot identify these two families: their degree90 central C2 traces are -90 and +66, respectively. See [the source-family max-cut audit](./Monster3B6SuzExistingSourceFamilyMaxCut20261025.md). The actual selected Monster pair requires the unexecuted GAP quotient receipt; earlier geometric/Sym² predictions are separate conditional constructions.

> **25 Oct phase refinement:** the original four C3 fingerprints are not four equally viable Monster-diagonal candidates. If 12 and 78 share one extended 729 representation and the same paid quotient kernel, their central phases must agree, retaining only 90ζ / 90ζ². The zeta-field norm distinguishes direct Sym² (5292) from dual Sym² (8100) without fixing phase naming. See [zeta diagonal norm cutset](./JFine3BZetaCyclotomicDiagonalNorm20261025.md). This remains a conditional common-factor/quotient result, not a measured Monster same-object action.

# JFine–Monster 3B: reuse of D4, 12+78, 12G and finite-field owners
**Audit date:** 2026-10-24. **Status:** exact finite D4 computation completed locally; 6.Suz class-identity screen source-written; no GAP/Agda kernel receipt.

## Primary attribution
- Conway and Norton, *Monstrous Moonshine* (1979), DOI 10.1112/blms/11.3.308; Ford, McKay and Norton, *More on replicable functions* (1994), source for McKay–Thompson series.
- Barraclough and Wilson, *The Character Table of a Maximal Subgroup of the Monster* (2007), DOI 10.1112/S1461157000001352: extraspecial inertia and `6.Suz` irreducible-character constructions.
- R. W. Barraclough, *Some Calculations Related to the Monster Group* (PhD thesis, 2005), §5.3: historical GF31 eigenvalue reconstruction for degree729 and GF103/GF223 rational degree1458 checks. https://webspace.maths.qmul.ac.uk/r.a.wilson/RWBphd.pdf
- GAP/CTblLib 6.Suz character tables, source positions and class power maps: https://www.gap-system.org/Packages/ctbllib.html .
- Source-established symmetric-square identity `chi_Sym²U(g)=(chi_U(g)^2+chi_U(g²))/2`. For the covering Suzuki 12, see **Gabriele Nebe**, *Symmetrizations of quadratic and Hermitian forms* (2025), DOI 10.1007/s10801-025-01399-2. Its degree78 example need not be a **faithful** 6.Suz constituent.
- Monster ATLAS power maps: https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M/; OEIS A007247 (4B q¹ 52), A058485 (12G q¹ -2), and A007257 (6D q¹ -2) are *transcriptions*, not original character proofs.

## Reused in-repo mathematical owners
- `DASHI/Biology/D4NineCellOrbitCompressionExact.agda`: literal nine-position D4 action and quotient-plus-residual; `TernaryMonsterSymmetryCandidateExact.agda`: raw nine-position character `[9,1,1,3,3]=3A1+B1+B2+2E`.
- `DASHI/Foundations/D4SO3NineIrrepRestrictionExact.agda`: **distinct** j=4 rotational restriction `1+Reg(D4)=2A1+A2+B1+B2+2E`, character `[9,1,1,1,1]`. Equal dimension 9 is not a carrier identification.
- `DASHI/Biology/D4IrrepFiniteFrickeEquivariantExact.agda`: 5 irrep labels with orientation flip ↔ finite Fricke complement; does not establish Monster intertwiner.
- `DASHI/Wikimedia/IbrahimMonsterFiveOrbitD4IrrepDecompositionKernelExact.agda`: five-orbit quotient `[5,5,1,3,3]=3A1+B1+B2`. It differs from both nine-dimensional carriers.
- `DASHI/Moonshine/Monster3BNormalizerBridge.agda`, `Monster3BHeisenbergMultiplicityExact.agda`: 729×(12+78)=65610 and a named *symmetric-square-dual dimension role*, not a source selected full character identity.
- `DASHI/Wikimedia/IbrahimMonster3B729ExtensionFiniteFieldProducerSnowballExact.agda`: separate GF31/103/223 provenance; `IbrahimMonster3BSuzukiQuotientDescentCorrectionExact.agda`: full central kernel quotient remains an additional proof obligation.
- `DASHI/Wikimedia/IbrahimMonster3BSuzukiNinetyPermutationCharacterNoGoExact.agda`: the actual 90 multiplicity **cannot** be a pure Fin90 permutation representation; signed/linear action is the correct option.

## New exact finite D4 theorem

The *prior* signed repair on the 90-dimensional multiplicity space had D4 character
```
 class:          e   r²   r     axis diagonal
 S90:           90  18   2      18     18
 H729:          729 81   9      81     81
 H729 ⊗ S90:  65610 1458 18  1458   1458
```
Assume **for a D4-only structural experiment** `S90 = U12 ⊕ Sym²U12`. The symmetric-square character identity and D4 irreducible multiplicities admit exactly THREE possible characters for U12:
```
  (12,4,-2,-6, 4) =  A1 + 2A2 + 5B2 + 2E
  (12,4,-2, 4,-6) =  A1 + 2A2 + 5B1 + 2E
  (12,4, 0, 4, 4) = 4A1       + 2B1 + 2B2 + 2E.
```
The last is **the only** one containing the pre-existing nine-cell permutation representation `V9=3A1+B1+B2+2E`, and decomposes as
```
       U12 = V9 + A1 + B1 + B2,   chi_U12 = [12,4,0,4,4]
 Sym²(U12) = degree78,           chi_Sym² = [78,14,2,14,14]
   U12+Sym²(U12) = degree90,     chi_S90  = [90,18,2,18,18].
```
Constructive implementation: `scripts/monster_3b_jfine_ninecell_sym2_intertwiner.py` uses nine-position permutation generators, three signed 1D generators, the 78 basis elements `e_i e_j` (i≤j), and direct sum. Its exact projector/extraction basis is rational, and BOTH 90-column canonical integer matrices have rank90 modulo101. Define the exact rational D4 intertwiner with the previous signed model by
```
          T = C_(nine+3+Sym²12)  · C_(previous_signed_90)^(-1).
```
Both bases transform under literally equal canonical D4 blocks; this proves the intertwining law over Q, not just over F101. The finite checks were run locally without GAP.

## Decisive central-involution obstruction (NOT a full 6.Suz identification)

The covering group 6.Suz has central involution c. On a **faithful irreducible** 12, Schur and faithfulness force c to act as -I. Therefore `Sym²(12)(c)=+I`, so the degree78 symmetric square has c in its kernel and is not faithful to 6.Suz. The dual symmetric square has the same central C2 kernel.

Thus if the actual selected 78 in the Monster 3B factorisation is **faithful to 6.Suz**, identifying it as Sym² of a faithful 12 is impossible (not just unproved). Conversely a 78 descending to 3.Suz may be a symmetric-square candidate; **its literal character position and descent through the Barraclough–Wilson diagonal kernel must be checked**. This corrects the older script's unverified blanket assumption that both degree12 and degree78 candidate families are faithful.

On the central order-three scalar `lambda=ζ`, Sym²U has `lambda²=ζ²`; dual Sym²U has `lambda^(-2)=ζ`. The difference resolves the old "equal or inverse" phase ambiguity only after the SOURCE-SELECTED 78 character is identified. Arithmetic labels are not the same-object certificate.

## Source-character check implemented without matrices

`scripts/monster_3b_suzuki_sym2_character_screen.g` uses CTblLib `Irr(6.Suz)`, `PowerMap(tbl,2)`, full classwise symmetric-square formula and its cyclotomic conjugate, class positions/ATLAS labels, central C2/C3 characters and kernel classification. **Crucially it checks ALL degree78 candidates, not merely faithful 78s.**

The earlier source producer `scripts/monster_3b_suzuki_multiplicity_characters.g` and its renderer/checker were updated to name degree78 candidates neutrally and serialize faithfulness flags; no imaginary successful table results are asserted. GAP not installed locally, so the exact source 12↔78 matching result has **not executed**.

## Two meanings of '12G / GF' separated

- **12G** is an ACTUAL Monster conjugacy class (not the separate group `12.G`). ATLAS says it powers to the relevant 4B and 3B classes; its McKay–Thompson q¹ coefficient -2 means `χ196883(12G)=-3`. Together with `χ196883(4B)=51`, this yields the **conditional** chosen phase quarter-turn trace `(51+3)/3=18`, under a verified order-four/phase-preserving subgroup embedding.
- **GF(31), GF(103), GF(223)** are Barraclough's original finite-field *computational methods*, NOT class labels. Our **new model**, independently, has faithful D4 canonical-basis rank90 modulo each, with primitive cubic roots 5,46,39 respectively. No historical Barraclough generator data/matrices were used in these cross-field checks.
- **GF(3)** is the 3×3/Heisenberg geometry carrier; characteristic 3 is modular for E, and ordinary Stone–von Neumann semisimplicity there cannot be imported unmodified.


## External source confirmation: actual irreducible Sym²(12) in the Suzuki cover

Gabriele Nebe's open-access peer-reviewed paper *Symmetrizations of quadratic and Hermitian forms*, `Journal of Algebraic Combinatorics` 61, article 29 (20 March 2025), DOI `10.1007/s10801-025-01399-2`, §6, **explicitly constructs** the symmetrization of its unitary degree-12 character of `6.Suz`. Its partition (2) row names irreducible character `χ_80` of degree78, and §6 separately calls out the degree-78 representations as **faithful to 3.Suz**, not to the 6.Suz central involution. Direct source: https://link.springer.com/article/10.1007/s10801-025-01399-2

This resolves an uncertainty at *Suzuki character existence* level: `Sym²(12)=78` is not simply a proposed tensor dimension and does **exist as a sourced irreducible character**. It confirms the central-involution argument: on 12 the central involution is -I; on the 78 symmetric square it is +I, so the 78 descends to `3.Suz`.

It **does not** yet prove the selected `78ab` character in the actual Monster 3B quotient descent is precisely `χ_80` (or its conjugate). Barraclough-Wilson main-to-normalizer quotient has a diagonal kernel and a central phase convention that must be checked classwise. The source character is independent external corroboration of the structural idea, not a Monster intertwiner receipt.

Exact conditional cyclotomic predictions from `U_12 ⊕ Sym²(U_12)`:

- Centre `C2` trace is always `-12 + 78 = 66` in the 90-dimensional multiplicity module.
- For the nontrivial centre C3 scalar on the 12, `lambda=ζ`, the genuine Sym² acts with `ζ²`; so `χ_90(c3)=12ζ+78ζ²=-78-66ζ`. For the dual Sym², the 78 instead has scalar `ζ`, giving `90ζ`.
- Reversing `ζ↔ζ²` produces conjugate fingerprint choices `-12+66ζ` and `90ζ²`. None is a nonnegative integral pure 90-point permutation trace.
- The central C6 trace follows by multiplying the 12 block by `-1` but not the 78 block, producing the four exact cyclotomic fingerprints in `scripts/monster_3b_jfine_ninecell_sym2_intertwiner.py`. The local-only cross-check program `jfine_6suz_centre_sym2_fingerprint.py` and receipt were executed in Python.

These exact centre fingerprints give a **short source-level matching filter** for the selected actual 12/78 pair, likely cheaper than general character-table products. The newly source-written `monster_3b_suzuki_sym2_character_screen.g` still tests full classwise equality and then requires the already existing `IbrahimMonster3BSuzukiQuotientDescentCorrectionExact` same-object kernel/phase certificate. No GAP execution is claimed.

## Revised highest-alpha path

1. DONE and locally checked: the 9+3→12→Sym²78→90 D4-only construction, all three D4 12 roots, unique root containing the actual nine-cell D4 representation, rational D4 intertwiner into the preceding signed repair, and mod-31/103/223 same-model full-rank checks.
2. DONE as a mathematical conditional obstruction: faithful 6.Suz 78 cannot be Sym² of faithful 12 due to central C2. Do NOT promote `symmetricSquareDualDegree=78` from a field label into a 6.Suz module theorem.
3. NEXT MATERIAL SOURCE CHECK: run ONLY the compact existing CTblLib 6.Suz symmetric-square/dual + kernel producer; compare the actual selected 12 and 78 **full class functions and quotient-descent kernel**. A failing source character relation decisively refutes the 12→Sym²78 *Suzuki extension* while leaving the D4-only model intact.
4. AFTER that, and only if source evidence allows, match the actual 3B phase-preserving D4 class pattern 2A/6D and 4B/12G and the source `6.Suz` linear 12⊕78 action. Do not demand a Monster dense matrix as a prerequisite to class-level tests.
5. No Agda head/kernel verification, GAP execution, historical GF matrix reproduction, literal Monster D4 embedding, or full 6.Suz/Monster source-coordinate intertwiner is claimed.
