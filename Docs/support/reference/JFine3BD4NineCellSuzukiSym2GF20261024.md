# JFine–Monster 3B: reuse of D4, 12+78, 12G and finite-field owners
**Audit date:** 2026-10-24. **Status:** exact finite D4 computation completed locally; 6.Suz class-identity screen source-written; no GAP/Agda kernel receipt.

## Primary attribution
- Conway and Norton, *Monstrous Moonshine* (1979), DOI 10.1112/blms/11.3.308; Ford, McKay and Norton, *More on replicable functions* (1994), source for McKay–Thompson series.
- Barraclough and Wilson, *The Character Table of a Maximal Subgroup of the Monster* (2007), DOI 10.1112/S1461157000001352: extraspecial inertia and `6.Suz` irreducible-character constructions.
- R. W. Barraclough, *Some Calculations Related to the Monster Group* (PhD thesis, 2005), §5.3: historical GF31 eigenvalue reconstruction for degree729 and GF103/GF223 rational degree1458 checks. https://webspace.maths.qmul.ac.uk/r.a.wilson/RWBphd.pdf
- GAP/CTblLib 6.Suz character tables, source positions and class power maps: https://www.gap-system.org/Packages/ctbllib.html .
- Source-established symmetric-square identity `chi_Sym²U(g)=(chi_U(g)^2+chi_U(g²))/2`. For the covering Suzuki 12, see *Symmetrizations of quadratic and Hermitian forms* (2025), DOI 10.1007/s10801-025-01399-2. Its degree78 example need not be a **faithful** 6.Suz constituent.
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

## Revised highest-alpha path

1. DONE and locally checked: the 9+3→12→Sym²78→90 D4-only construction, all three D4 12 roots, unique root containing the actual nine-cell D4 representation, rational D4 intertwiner into the preceding signed repair, and mod-31/103/223 same-model full-rank checks.
2. DONE as a mathematical conditional obstruction: faithful 6.Suz 78 cannot be Sym² of faithful 12 due to central C2. Do NOT promote `symmetricSquareDualDegree=78` from a field label into a 6.Suz module theorem.
3. NEXT MATERIAL SOURCE CHECK: run ONLY the compact existing CTblLib 6.Suz symmetric-square/dual + kernel producer; compare the actual selected 12 and 78 **full class functions and quotient-descent kernel**. A failing source character relation decisively refutes the 12→Sym²78 *Suzuki extension* while leaving the D4-only model intact.
4. AFTER that, and only if source evidence allows, match the actual 3B phase-preserving D4 class pattern 2A/6D and 4B/12G and the source `6.Suz` linear 12⊕78 action. Do not demand a Monster dense matrix as a prerequisite to class-level tests.
5. No Agda head/kernel verification, GAP execution, historical GF matrix reproduction, literal Monster D4 embedding, or full 6.Suz/Monster source-coordinate intertwiner is claimed.
