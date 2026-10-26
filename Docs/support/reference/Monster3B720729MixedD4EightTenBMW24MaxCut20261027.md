# Monster 3B — published diagonal quotient and constructive mixed eight-site 720/729 max-cut

**Evidence date:** 27 October 2026. **Current PR:** [#1250](https://github.com/chboishabba/dashi_agda/pull/1250). **Donor:** [#1098](https://github.com/chboishabba/dashi_agda/pull/1098).

## A. External mathematical source correction: the diagonal quotient is PAID

**Original authors:** Richard W. Barraclough and Robert A. Wilson, *The Character Table of a Maximal Subgroup of the Monster*, LMS J. Comput. Math. 10 (2007), 161–175, DOI `10.1112/S1461157000001352`. Their original main/quotient source records `3^1+12:6.Suz.2` and the main→N(3B) class-20 kernel, as already tracked in the repository's `IbrahimMonster3BPrimarySupplementKernelClass20SnowballExact` and `IbrahimMonster3BDiagonalKernelPaidSignGaugeCorrectionExact`. Original author's [supplementary table archive](https://www.rwb.me.uk/table/index.html) remains the original computed-data root.

**Further verification (shared original coauthor, NOT independent testimony in the strong statistical sense):** Thomas Breuer, Kay Magaard and Robert A. Wilson, *Some steps in the verification of the ordinary character table of the Monster group* (12 December 2024), [source protocol, Section 6](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/htm/ctblm.htm). It explicitly constructs both quotients of the original main table `H` by the two candidate diagonal order-three subgroups:

- `H/[1,19]` (first candidate): 95 candidate irreducibles, class-restriction coefficient matrix rank88, **SolutionMat = fail**. Hence the degree196883 Monster restricted character cannot decompose through that source candidate.
- `H/[1,20]` (second candidate): same 95 candidates and rank88, **SolutionMat returns an integer character decomposition**. Its table is equivalent to standard GAP `MN3B` (the published `TransformingPermutationsCharacterTables` check yields `true`).
- These integer positions are legitimate only in the **specified original main table class ordering**. Under arbitrary class permutations they must be transported via the same permutation, not copied.

This is a *published source-level numerical proof receipt*, not a local GAP run. The existing code's `qKernel3` semantic selector now explicitly checks the original class position **20** and `mainToOuter[20]=6` as a regression against the original published table (script `scripts/monster_3b_suzuki_main_quotient_match.g`). The pre-existing shell test already checked 20/6; this cut moves the check into the source producer so a misleading certificate cannot be generated first.

**STOP:** never characterize the 19/20 source quotient choice as an outstanding mathematical obstacle. What remains a gauge is the symbolic `t1*t2` versus `t1*t2^-1` NAME after choosing a generator, not the invariant physical subgroup. The actual Monster-selected degree78 `6.Suz` irreducible, full source-character classwise identification, chosen 729 extension lift and intertwiner are distinct, still-unpaid evidence.

## B. Prior 720/729 owners, now sharpened constructively

Existing original DASHI owners (retain original authorship and dates):
- `DASHI.Foundations.Base369PointedAppraisalFibreExact` and `DASHI.Moonshine.Base369Pointed729NestedNinetyBidiExact`: pointed **`729=720+9=8*10*9+9`** address cardinality (not an ambient group isomorphism).
- `DASHI.Moonshine.Monster3BPointed720729AffineProjectorCutExact` and source [#1250 ledger](./Monster3BPointed720729AffineHeisenbergMaxCut20261026.md): original rank-nine `F3^2` support, 81 orthogonal nine-dimensional projectors, nine preserving translations and 720 moving them; full Heisenberg stabilizer `3^9` is **nonabelian**.
- [PR #1098 source witness](https://github.com/chboishabba/dashi_agda/blob/agent/e6-f3-exterior-square-maxcut-20261006/scripts/monster3b_atlas_d4_pointed720729_polarization_weld.py): original AtlasRep `2.Suz:2` `D4` words, a real D4-stable 6D Lagrangian and 2D isotropic plane in the 12D symplectic quotient. The four-dimensional quotient action is **`E⊕E`**, with 80 nonzero quotient vectors in eight size-four orbits plus six size-eight orbits. The original natural geometric cube-corner eight action has an axis-mirror without fixed points; source quotient has eight mirror-fixed points. Thus **no D4-equivariant map to NATURAL geometric cube corners exists**.

### New result: constructive eight-by-ten with a DIFFERENT eight-point target

In a chosen four-dimensional `F3` chart with `D4` acting as `E⊕E`, exact orbit/stabilizer enumeration distinguishes the eight length-four orbits as:

- **four** length-four orbits whose point stabilizer is an **axis-reflection** subgroup of order 2;
- **four** length-four orbits with a **diagonal-reflection** point stabilizer;
- **six** *free* length-eight orbits.

Choose an eight-point target `T` that is the DISJOINT union of one four-point **axis** orbit and one four-point **diagonal** orbit. This target is **not** the natural eight cube corners.

Now send the four source axis4 orbits to the axis target4, and the four source diagonal4 orbits to the diagonal target4, respecting point-stabilizer inclusion. Split the six free8 orbits into three sent to the axis4 orbit and three to the diagonal4 orbit; a free8 orbit projects two-to-one onto its four-point target. This is well-defined and D4-equivariant by orbit transport:

```
  source axis block: 4*4 + 3*8 = 40, hence each axis target point has 10 preimages
  source diagonal block: 4*4 + 3*8 = 40, hence each diagonal target point has 10 preimages
  total: 40+40=80, exactly 8 target points × 10 source labels.
```

For each nine-point plane coordinate `t∈F3²`, lift the quotient80→T8 through
```
   (F3^4 \ {0}) × F3²   →   T8 × Fin10 × F3²
               720                 8 × 10 × 9
```
plus the disjoint central `q=0` nine-point sheet, giving the original **720+9=729** bijection. The site projection is D4-equivariant; the ten-fibre action is **not trivial or independent of the target site**, because the source has free eight-point orbits whereas ten copies of `T8` have only four-point orbits. Transporting the genuine action across the bijection produces exactly the REQUIRED twisted sheet action, without a claim of canonical functoriality.

The D4 fixed-point characters are exactly:

| D4 class | identity | r² | r (quarter) | axis mirror | diagonal mirror |
| --- | ---: | ---: | ---: | ---: | ---: |
| Quotient 80 nonzero | 80 | 0 | 0 | 8 | 8 |
| New mixed target 8 | 8 | 0 | 0 | 2 | 2 |
| Pointed outer 720 | 720 | 0 | 0 | 24 | 24 |
| Central 9 | 9 | 1 | 1 | 3 | 3 |
| Total Schr 729 | 729 | 1 | 1 | 27 | 27 |

The actual verified finite consumer [`scripts/monster_3b_pointed720729_mixed_d4_eight_ten_quotient.py`](../../scripts/monster_3b_pointed720729_mixed_d4_eight_ten_quotient.py) computes the full map, tests all eight D4 elements on all 80 quotient points and all 729 chosen address states, tests eight exactly-ten fibres, checks whole character/fixed counts and confirms the necessary **nontrivial sheet twisting**. Independent Python reimplementation in this turn passed the 80-point orbit and 729-point classwise tests. **The exact GitHub script bytes were not locally executed.**

### Mathematical source/proof qualifications

1. This is a **new finite D4 SET-level existence result** in an `E⊕E` action that was already source-verified for the ATLAS four-dimensional quotient in #1098. It does NOT identify a literal chosen ATLAS coordinate basis with the standard `E⊕E` chart; an actual source intertwiner must be reused/imported from the owning PR to claim that.
2. D4-stability of the selected nine-plane permits a D4-equivariant complementary chart over `F3` by **Maschke's theorem** (|D4|=8 is prime to3), but this finite D4 splitting is NOT preservation by the **full Heisenberg group**; 720 translations move the rank-nine support.
3. The target `T8` is a mixed orbit set, **NOT the existing literal geometric `Corner8`**. The prior corner no-go remains valid and is NOT refuted.
4. The `720` support is not automatically the unrelated Mathieu stabilizer of order 720, and `729` is the dimension of a chosen Schrödinger basis, **not** the entire ambient Monster VOA or its selected `W_ζ`.
5. This construction does not choose the actual `6.Suz` degree78 constituent, a Monster-normalizer element word, source phase lift, linear Hom intertwiner or cocycle. It is not a physical device/quantum-operator claim.

## C. Pareto/snowball/Ibrahim next payments

- **Already paid by source and prior work:** diagonal quotient `H/[1,20]`, 720+9 address bijection, source D4-stable nine-plane and E⊕E quotient, natural geometric eight-corner obstruction, original Heisenberg full-action obstruction, exact Q(ζ) and general conductor character algebra.
- **Paid this cut:** additional published BMW24 corroboration of class20 vs class19 character incompatibility; explicitly enforced class20 in the original source GAP matcher; constructive D4-equivariant 80→mixed8 degree10 and lifted 720+9 chart with twisted ten fibres, independently locally reproduced in exact Python.
- **P0 next:** source-selected degree78 `6.Suz` character-main/MN3B-to-Monster FULL occurrence receipt and optional all-conductor same-label full-character JOIN already implemented in #1250. Never substitute a synthetic pass.
- **P1 after P0:** actual #1098 `Hom_E(H_ζ,W_ζ)`, center-preserving lifted action and cocycle using source-selected character; a source D4 mirror generally exchanges `ζ↔ζ²` and should not silently act inside a single `ζ)-eigenspace.
- **P2 optional geometric refinement:** identify a literal source-basis ATLAS intertwiner carrying the new mixed-eight quotient target back to the repository's existing chosen 9-plane, if needed. Do NOT treat the mixed orbit target as natural cube corners.

**Attribution:** Original mathematics Maschke and finite D4 orbit-action theory; original Monster/6.Suz source Barraclough–Wilson (2007), Breuer–Magaard–Wilson (2024) as an additional reproducible computation with shared coauthor, ATLAS/AtlasRep original matrices, Wilson (1988) character decomposition, Serre/Terras finite representation/Fourier foundations. This new mixed target/fibre mapping is a repository-derived constructive calculation; it is **not** a statement in any of the original publications. Historical original sources remain roots; republications/secondary commentary are not independent corroboration.

## Repository authorship and revision policy

- **Research direction and existing pointed 720+9/D4/Heisenberg programme:** Johl Brown and pre-existing dated DASHI repository authorship; retain the earliest dated repository owners. The positive mixed-eight orbit selection and the exact quotient/fibre enumeration in the October 27 cut are **repository-derived, ChatGPT-assisted calculations**, provisionally credited to Johl Brown's research programme with OpenAI ChatGPT implementation assistance, not falsely assigned as an original theorem of Barraclough, Wilson, Breuer, Magaard or ATLAS.
- **General principles (not novel claims):** finite G-set orbit/stabilizer equivariance, D4 character multiplicity formula and Maschke splitting belong to classical mathematical prior art. External 2007 and 2024 original-author sources pay the Monster class/quotient/character statements, not the invented eight-site model.
- **Proof status:** source-written GitHub scripts, independent local exact finite Python audit, static file-delimiter verification and actual source-ATLAS SHA-verified checks from prior PR #1098 are distinct evidentiary categories. The new GitHub-head mixed-orbit scripts and source-aware branch execution were not directly executed in this session. All same-object claims may be refined or withdrawn as source-groups, class fusions and kernel observations become available.
- **Source-root graph:** the 2024 Breuer–Magaard–Wilson reproducibility notes are a later independent **computation** using the same Monster table lineage and shared original author Wilson; they do not count as an independent underlying mathematical source of the 2007 group.
