> **26 OCT SOURCE-CLASS CORRECTION — ACTUAL ATLAS D4 IS NOT THE HYPOTHETICAL 4B/2A D4.** Norton & Wilson, *Anatomy of the Monster: II* (2002), DOI 10.1112/S0024611502013357, explicitly identify the central `−1_A` involution of `2.Suz` inside the Monster `3B` normalizer as Monster class **2B** (original scholarship; online reproduction is NOT a second source root). PR [#1098](https://github.com/chboishabba/dashi_agda/pull/1098) gives a manifest-SHA256-anchored actual original ATLAS `2.Suz:2` GF3 source-word `D4` with **`r²=−I12`**, hence that *specific source* half-turn has **2B**, NOT the **2A** required by the 24 Oct steelman. Barraclough & Wilson (2005), *Conjugacy Class Representatives* DOI 10.1112/S1461157000000966, original Table 2 gives **`4B²→2A`**, excluding source `r:4B`; original published **4D word `BCCCBB`** maps via BW07 §3.1 generator quotient to source `D*C³*D²`, which locally checks order4 and square `−I`, but DOES NOT determine our distinct source `r` conjugacy class. The **full 4B/2A necessary C4-character steelman and −19 pointed residual** below are valid only under their *hypothetical class pattern*, NOT a Monster class assignment for this source D4. The existing [conditional 2B/6B/6E signed parity checker](../../../../scripts/monster_3b_suzuki_c2_parity_6class_conditional_gate.py) already gives only **66 or 90** for the selected phase involution, with faithful78/parity−1 vs nonfaithful78/parity+1 conditional branches. No authentic 6.Suz selected78, Monster subgroup word, z-product 6B/6E determination, Agda/GAP kernel or physical experiment is claimed. [Full original-source / AtlasRep / Schur–Zassenhaus attribution ledger](https://github.com/chboishabba/dashi_agda/blob/agent/e6-f3-exterior-square-maxcut-20261006/Docs/support/reference/Monster3BAtlasD4FourESourceSubmoduleMaxCut20261026.md).

# Monster 3B × JFine max-cut decision — 24 October 2026

## Executive mathematical verdict

**The previously chosen purely geometric D4 extension of the JFine Heisenberg E-module is impossible as the selected Monster W_zeta phase-preserving D4 action.** This is an ordinary character obstruction, not a failure of Heisenberg isotypy.

Let W be the sourced 196883-dimensional Monster representation, z a selected 3B element and g an involution centralizing z. Then zg has order 6, (zg)^(-1)=z^2g, and the ordinary real Monster character satisfies

  tr(g|W_zeta) = [chi_W(g)-chi_W(zg)]/3.

The Monster source character at 2A and 2B is respectively 4371 and 275. Its order-six values are recovered from the q^1 coefficient of the **normalized** McKay–Thompson series as chi(g)=coefficient_q1-1. **Do not confuse coefficient q^0 or historic lowercase replicable labels with genuine Monster classes.**

| Monster order-six class | q^1 of T_g | degree-196883 chi_W | OEIS transcription |
|---|---:|---:|---|
| 6A | 79 | 78 | A007254 |
| 6B | 78 | 77 | A007255 |
| 6C | 15 | 14 | A007256 |
| 6D | -2 | -3 | A007257 |
| 6E | 6 | 5 | A007258 |
| 6F | 28 | 27 | A007259; constant q^0 shifted, coefficient q^1 unchanged |

The **ATLAS Monster 3B power-up list** contains only 6B,6D,6E among order-six classes. Their cube classes are 2B,2A,2B. Thus any order-two element g commuting with z has phase trace in the exact *necessary* set

  { (275-77)/3, (4371+3)/3, (275-5)/3 }
  = {66,1458,90}.

This means the existing geometric JFine D4 character

  [65610,810,90,2430,2430]  (D4 classes 1,r^2,r±1,reflection axes,diagonals)

is definitively NOT the selected Monster W_zeta D4 character: its half-turn 810 and reflection 2430 are both excluded. This holds without a candidate D4 embedding, without class algebra or any concrete Monster generator, because it quantifies over **all** possible Monster 2/6 classes. The sign twist of the old geometric D4 is also impossible (all D4 one-dimensional scalar twists fix r^2).

### A maximally economical, conditionally viable repair

Preserve the proved geometric H_zeta fibre action on X6 (dim729), whose D4 character is [729,81,9,81,81]. Replace only the D4 action on the **ninety-dimensional LINEAR** multiplicity space S.

For a source-compatible D4 under that fixed fibre action, every D4 involution phase trace must be divisible by 81. Among {66,90,1458}, **only 1458 is divisible by 81**. Therefore every involution in the proposed D4 must be Monster class 2A with zg in 6D, and the multiplicity trace is 1458/81=18 on r^2 and both reflection classes.

Since r^2 is class 2A, the ATLAS order-four power map forces r into class 4B. The only order-twelve class powering both to 4B (third power) and 3B (fourth power) is 12G. Its q^1 coefficient is -2, while class 4B has q^1=52. Hence chi_W(4B)=51, chi_W(12G)=-3 and the phase trace at r is (51+3)/3=18; the fibre trace is 9, so chi_S(r)=2.

Thus the prescribed D4 character on S is exactly

  chi_S = [90,18,2,18,18]

and by the D4 character-orthogonality formula, it has the **unique** decomposition

  S|D4 = 23 A1 + 5 A2 + 13 B1 + 13 B2 + 18 E,

where E is the two-dimensional standard real representation. This character is realized by explicit **signed-permutation** 90×90 generators, preserving the 90-dimensional basis *up to signs*, not by the original 90-point permutation action. The full H_zeta⊗S character is

  chi_(H_zeta⊗S) = [65610,1458,18,1458,1458].

This is a genuine exact finite-group construction and solves the **necessary local character alignment** under the fixed fibre hypothesis. It does **NOT** establish the actual subgroup D4⊂C_M(z), its Monster class pattern, the full 6.Suz inertia action, the actual Hom_E(H_zeta,W_zeta) module, its projective cocycle, or any literal basis intertwiner. It is an explicit **conditional steelman**, not an existence proof for a chosen Monster subgroup.

### What the source claims and what the repository computed

- **Original scholarship:** Conway–Norton (1979), Ford–McKay–Norton (1994), Barraclough–Wilson (2007), Breuer–Magaard–Wilson (2026). Their mathematical results/character tables retain original attribution.
- **ATLAS:** https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M ; source for 2A/2B, 3B, 4B, 6B/6D/6E and 12G conjugacy-class power-up relationships.
- **Series transcriptions:** https://oeis.org/A007254 through A007259, https://oeis.org/A007247 (4B), https://oeis.org/A058485 (12G). Values are SOURCE INPUTS to the repository arithmetic, not theorems newly discovered by the Python scripts.
- **New executable arithmetic:** `scripts/monster_3b_jfine_involution_character_nogo.py` establishes all 2/6 arithmetic and the exclusion without external software.
- **New local model:** `scripts/jfine_3b_linear_multiplicity_d4_repair.py` builds exact signed permutation generators, verifies the D4 presentation, computes class characters, checks the derived irreducible multiplicities, and constructs the 729×90 tensor traces.
- **New Agda source:** `DASHI/Moonshine/Monster3BJFineGeometricD4InvolutionNoGoExact.agda` gives 24 closed contradiction patterns for two involution classes × six order-six classes × two geometric trace types. `Monster3BJFineD4CandidateMultiplicityExact.agda` gives exact arithmetic proof terms for the replacement decomposed character. The Agda modules have **not** been typechecked at this head.
- **Previously owned:** all finite Heisenberg/Schrödinger/Stone–von Neumann/projector/C3-character/Hom-space/cocycle interfaces; Wilson's 12+78, the source-paid linear rather than pure Fin90 inertia action and the MonomialBasisSpecialisation route remain authoritative.
- **No mmgroup needed:** the geometric no-go and repaired D4 model are exact, backend-free. The old CTblLib/AtlasRep/mmgroup producers are optional cross-checks, NOT blockers or inputs to the new no-go.

## Revised phase and stopping rules

**Phase CLOSED — finite model and geometric no-go:** H6 and the original JFine chart, its selected nontrivial E-isotypic complex representation, the original geometric D4 action and character, plus the definitive order-2 Monster character obstruction.

**Phase CLOSED — candidate representation character:** a source-2/4/6/12-compatible signed-monomial D4 action on S90, with explicit group matrices in the Python producer and complete ordinary D4 irreducible multiplicities; its character is conditionally compatible with the requested Monster local class pattern.

**Phase OPEN — actual normalizer SAME OBJECT:** find/certify a D4 subgroup of the actual phase-preserving N(3B) with all five involutions in 2A and order-four rotations in 4B (and hence z-products in 6D and 12G). If no such D4 exists, this repaired signed model also fails. If one exists, compare FULL classwise character (the necessary local five-class trace is already paid) and then extend to the actual 6.Suz inertia representation with its 12+78 linear splitting and cocycle. The existing general linear Hom owners are appropriate; do NOT create another Weyl/Stone–von Neumann/Burnside theorem owner.

**No physics promotion** follows from any such group-module isomorphism. The full 12+78 normalizer-linear action is fundamentally different from an arbitrary signed D4 matrix; no material system, observable gauge field, or quantum-measurement implementation is identified.

## Source-level status

Local Python arithmetic and signed finite-group checks were executed and passed in this turn. Original character values/power maps were checked against OEIS/ATLAS sources. No actual GAP/AtlasRep/mmgroup run, Agda/Lean kernel receipt, Monster normalizer embedding, or concrete Monster intertwiner is claimed.


## 24 Oct original-D4 and 12+78 cross-pollination addendum

See the canonical new owner [JFine3BD4NineCellSuzukiSym2GF20261024.md](./JFine3BD4NineCellSuzukiSym2GF20261024.md). The repaired signed 90-space is not merely an arbitrary `D4` character: using the pre-existing raw nine-cell permutation `3A1+B1+B2+2E` (NOT the `SO3 j4=1+Reg(D4)` nine-space), an exact selected `D4` model is
```
  U12     = V9 ⊕ A1 ⊕ B1 ⊕ B2    = 4A1+2B1+2B2+2E
  Sym²U12 = dim78               character [78,14,2,14,14]
  S90     = U12 ⊕ Sym²U12       character [90,18,2,18,18].
```
There are exactly three possible 12-dimensional D4 characters yielding this 90 via Sym²; this is the unique root containing the original raw nine-cell permutation representation. Local Python constructs exact matrices, verifies a rational D4 intertwiner to the previous 90 repair and checks full canonical basis rank in characteristic 31,103,223.

**Critical faithful-central sign barrier:** Sym² of a faithful complex 6.Suz 12 kills the central involution and cannot be a faithful 6.Suz 78. The source 78 may instead factor through 3.Suz, but selected full class identity and Barraclough–Wilson quotient descent remain to be checked. The new CTblLib `monster_3b_suzuki_sym2_character_screen.g` does that full character comparison on ALL degree78 characters, and the earlier `monster_3b_suzuki_multiplicity_characters.g` + renderer/checker have been corrected to refrain from demanding degree78 faithfulness.

**Terminology:** Monster class 12G has character -3 inferred from the 12G q-series coefficient -2 and powers to Monster 4B and 3B. GF31,GF103,GF223 refer instead to Barraclough's historical finite-field program; crossfield tests of our D4 model are not reproductions of those matrices. No actual Suzuki or Monster same-object proof is claimed.
