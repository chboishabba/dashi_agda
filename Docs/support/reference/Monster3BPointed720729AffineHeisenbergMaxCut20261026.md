# 26 October 2026 — Pointed 720+9 → 729 Schrödinger cosets / Monster 3B max-cut

## Attribution and typed prior art

**Original mathematical sources**: Robert A. Wilson, *The odd-local subgroups of the Monster* (1988), DOI 10.1017/S1446788700031323, supplies the 3B normalizer restriction `143+65520+(729+729')(12+78)`. R. W. Barraclough and R. A. Wilson, *The Character Table of a Maximal Subgroup of the Monster* (2007), DOI 10.1112/S1461157000001352, supply the extension, quotient and character machinery. Serre's finite group representation theory and Terras (1999), *Fourier Analysis on Finite Groups and Applications* (DOI 10.1017/CBO9780511626265), are the appropriate mathematical roots for Weyl operators, finite Fourier characters, irreducibility and conjugation. Original ATLAS/AtlasRep source 2.Suz:2 GF3 12D matrices and explicit **true-source D4 subgroup** are owned separately by current [PR #1098](https://github.com/chboishabba/dashi_agda/pull/1098); it is not automatically a selected Monster word or a basis action on our arbitrary plane.

**Existing repository-specific address and proof owners**:
- `DASHI.Foundations.Base369PointedAppraisalFibreExact` constructs **720+9=729** pointed addresses with `720=8×10×9`. The same exact carrier is re-associated by `DASHI.Moonshine.Base369Pointed729NestedNinetyBidiExact` to `8×90+9`, with the 10×9 multiplicity explicitly source-distinct from the actual Monster action.
- `DASHI.Moonshine.Base369Pointed729CornerCubeBidiExact` carries the actual *geometric* eight corners, but **not** an equivariant Monster identification.
- `DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact`, `Monster3BFiniteHeisenbergCentralExtensionExact` and `Monster3BFiniteSchrodingerPointProjectorExact` own the true six-trit **model group** and its coordinate-projector/Heisenberg generators, not merely dimensions. PR #1098 owns source lifting and the subsequent actual-VOA Hom.
- `DASHI.Moonshine.Monster3BWilsonPublishedRestrictionReconciliationExact` already distinguishes `196883=143+65520+(729+729')×90` (Wilson source) from the **central C3 observer** `196883=53+3×65610`; a fabricated Suzuki-stable `143=53+90` direct-sum decomposition is explicitly disallowed.
- `DASHI.Foundations.TernaryGolay.MathieuStabilizerChain` uses a **different** 720 as the order of the ordered two-point stabilizer of M12; that does not identify this affine 720 support with the M12 group.
- Current [PR #1260](https://github.com/chboishabba/dashi_agda/pull/1260) uses the Eisenstein quotient `Z[ω]/(1-ω)^9`, of cardinal `3^9=19683` with abelian additive group `C81×C243`; the equal order below is **not** an isomorphism.

## Exact new chosen-basis bridge — not a canonical or Monster-equivariant map

Write `X6=F3^6=F3^2 × F3^4` and choose the latter quotient as 81 affine cosets of a nine-point plane `L=F3^2×{0}`. With little-endian base-three code `k=t+9q` where `0≤t<9`, `0≤q<81`:

```text
  central(t)              -> t,                    q=0
  noncentral(i,j,t)       -> 9*(1+10*i+j) + t      i∈0..7,j∈0..9
  inverse(k): q,t=divmod(k,9); q=0 -> central(t)
       else i,j=divmod(q-1,10); -> noncentral(i,j,t)
```

This is a **literal two-sided bijection of all 729 labels** reusing the existing 720+9 address owner and a CHOSEN six-trit coordinate chart. The 8×10 indexing of the 80 nonzero quotient vectors is a choice, **not** a canonical linear, D4 or ATLAS-equivariant decomposition. A corner index in the pre-existing 3×3×3 model is likewise not automatically a coset orbit.

Let `P_q` project onto the nine coordinate basis vectors with quotient `q∈F3^4`. The 81 projectors are pairwise orthogonal, rank nine each, and `∑_q P_q=I_729`. The subgroup of six-trit translations fixing `P_0` is precisely `L`, cardinal 9; the other **720 translations** move it, producing exactly **81 conjugate projectors**. A translation by a quotient-coordinate unit vector takes `δ_0` outside the selected plane:

```text
    P_0 T_a δ_0 = 0  but  T_a P_0 δ_0 = δ_a ≠ 0.
```

This is a concrete **negative** answer to whether the original shared nine-sheet is invariant under the *unchanged* full Schrödinger/Heisenberg action. All modulation operators commute with this diagonal support projector. The full Heisenberg stabilizer therefore has cardinal

```text
    |Stab_E(P_0)| = 3² × 3⁶ × 3 = 3⁹ = 19683,
    |E| = 3¹³ = 1594323,  [E:Stab(P_0)] = 3⁴ = 81.
```

Unlike the Eisenstein lambda^9 **abelian additive** group of the same order, this support stabilizer is **nonabelian**: its axis0 translation and axis0 modulation have central Weyl commutator ζ≠1. An **Agda source-written** term `rankNineSupportStabilizerNoncommutative` is expressed using the ORIGINAL Heisenberg extension's literal `compose`; a second theorem directly refutes `axis2` translation-invariance of the plane. **Agda has not been kernel-run this turn**.

There is also a source-aware useful filter for a proposed ATLAS `D4` element: certify whether its chosen `X6` representation normalizes the particular plane, i.e. `D(L)=L` under the *same* group lift and basis. [PR #1098](https://github.com/chboishabba/dashi_agda/pull/1098) now proves an **actual ATLAS 2.Suz:2 D4 word subgroup**, no longer just the older ambient GF729 D4, and invokes Schur–Zassenhaus for an abstract normalizer complement conditional on the source quotient. However neither that source D4's **actual Monster class fusion** nor its preservation of this **chosen** rank-nine plane has been established here. A centre-inverting mirror exchanges ζ and ζ² phase sectors, so a full-D4 action on a single fixed ζ phase cannot be inferred.

## Precise Wilson / 720 / 728 arithmetic and action nonclaims

Both useful decompositions of `729×90=65610` now share a **CHOSEN three-rank filtration**:

```text
  F3^6 coordinate labels    = {origin} ⊔ (L\{origin}) ⊔ (X6\L)
    support dimensions      = 1 + 8 + 720
    tensored with 90        = 90 + 720 + 64800 = 65610
    Wilson arithmetic       = 90 + 65520      = 65610.
```

The `728+1` partition underlying `65520=728×90` is the **complement of the ORIGIN**, whereas `720+9` is the **complement of a PLANE**. The 728 complement contains eight extra basis points in the chosen plane, and that accounts exactly for the numerical difference `65520−64800=720=8×90`. This is a precise **arithmetic and support-level** crosswalk, **not** a claim that Wilson's published 65520-dimensional monomial representation is `728×S90` as an honest N(3B) module. The 143-dimensional Wilson constituent is irreducible, so its numerical `143=90+53` must also not be promoted to an invariant splitting.

## Local exact verification and reproducible owner

A pure standard-library Python witness **actually executed locally** this turn:
- full 729-address forward/backward bijection (720 noncentral and 9 central);
- 81 rank-9 affine-coset supports, disjointness and completeness;
- exact stabilizing translation count **9**, moving translations **720**, conjugate projector orbit size **81**;
- exact Heisenberg cocycle and **noncommuting** Weyl stabilizer pair, group orders **19683**, **1594323**, index81;
- modulation-on-plane histogram: **81** phases constant on the plane and **648** nontrivial modulations each distributing the 3 phase exponents evenly (3,3,3);
- exact Wilson `65520+143=65610+53`, `720+8+1=729`, `720×90+8×90+90=65610`;
- no original Monster character, source D4 plane action, group word, experimental physics or Agda-kernel proof claimed.

Local executed source `/mnt/data/monster3b_maxcut_720729/check_720_729_heisenberg_coset_cut.py`, SHA-256 `4d1a7803aa0958174e737e66e0ba8870d7455735beb7791fb796c45648ae289c`; receipt `/mnt/data/monster3b_maxcut_720729/receipt.json`. The separately committed GitHub compact consumer `scripts/check_monster_3b_pointed_720_729_affine_projector.py` implements the same central finite claims but was **not** executed from its exact commit bytes in this turn. New source-written Agda `DASHI/Moonshine/Monster3BPointed720729AffineProjectorCutExact.agda` formalises the axis2 failure, noncommutation and numeric source reconciliation; not typechecked here.

## Pareto / Ibrahim next-target stop rule

**Closed (chosen finite model):** pointed 720+9 ↔ six-trit coordinate basis (chosen bijection), rank-nine projector orbit/stabilizer and Heisenberg-invariance no-go. No need to reimplement X6, 729 Fourier, nine-plane projectors, Mathieu towers, Suzuki characters, finite-field multiplication or D4 group structure.

**Highest-value source-specific open obligation:** choose the **actual ATLAS/MONSTER lift of source D4** (already explicit at 2.Suz:2 level in #1098); derive its action on the **same chosen** Heisenberg Lagrangian / nine-plane and classify `L -> D(L)`. If the source action fails to preserve L, the original pointed 720+9 cannot be a D4-invariant submodule under that action, though its coordinate chart remains valid. Separately, acquire/execute the original Barraclough–Wilson source-selected degree78 family and full character-table **same-object JOIN** already owned by #1250. A suitable basis change may alter which plane is stabilized and must be declared, not silently presumed.

No attribution laundering of Barraclough/Wilson, original ATLAS/AtlasRep, Serre/Terras, or other DASHI PR authors into a new Monster theorem. Equal numerals, phase analogies and existing source-written Agda code cannot substitute for actual Monster group words, linear intertwiners and kernel-verified proof.

## 26 October: **actual source D4-compatible polarization found in PR #1098**

New original-source donor **[scripts/monster3b_atlas_d4_pointed720729_polarization_weld.py](https://github.com/chboishabba/dashi_agda/blob/agent/e6-f3-exterior-square-maxcut-20261006/scripts/monster3b_atlas_d4_pointed720729_polarization_weld.py)** is in the **correct original ATLAS/2.Suz:2 owner #1098**, not re-vendored in this PR. An independent exact local GF3 replay used both literally identical original source generators, **verified their manifest SHA256**, and the true D4 generator words and rank12 alternating form from #1098.

The anti-symplectic D4 mirror's +1 eigenspace is a rank6 Lagrangian. The induced *symmetric* form `Q(u,v)=<u,r v>` on this rank6 space has rank6, determinant **2 modulo 3**, and **split Witt index 3**. Its concrete orthogonal isotropic generators in the deterministic m-positive basis are

```
(0,0,0,1,0,0), (0,1,2,0,0,1), (1,0,0,0,0,1).
```

The six source 12D vectors `v_i,r v_i` span a **true D4-invariant 6D Lagrangian**, and the first pair spans a **D4-invariant isotropic rank2 plane**. Thus there EXISTS a source-D4-compatible **nine-point coordinate plane** for one chosen Schrödinger polarization. This is a positive quotient-level source result. It does **NOT** say the full Heisenberg translation group preserves the plane: as proved earlier, 720 translations move it.

For the chosen 6D position Lagrangian, the D4 quotient by that rank2 plane is **two copies of the standard D4 2D module**, giving the following exact finite permutation action on 80 nonzero `F3^4` quotient points:

```text
identity fixes 80;
r,r²,r³ fix 0;
each of 4 reflection elements fixes 8;
eight 4-orbits + six 8-orbits = 14 orbits total.
```

Therefore the **specific** earlier `Corner8×Fin10` model with D4 acting on corners while acting trivially on the ten-sheet factor is **ruled out**: all reflection fixed counts of such a product must be divisible by ten, unlike the true 8 fixed nonzero points. A **nontrivial D4 action that mixes/permutes fine sheets** is not thereby obstructed, and constructing it would require a new equivariant coordinate/character comparison rather than a trivial-product assumption.

Local independent original matrix script:
`/mnt/data/monster3b_maxcut_720729/check_atlas_d4_pointed_source_weld.py`
and receipt:
`/mnt/data/monster3b_maxcut_720729/atlas_d4_source_weld_receipt.json`.
Source bytes have the exact original pinned SHA256:
`ddd4919ab560f78b065aa08e309bd047942cdb7bb52a1474da84d54d35a031c2`
and
`433ba0f0373995b159859df00dd5a5005355fdbf8b59a31d651aeaf43ffcd15f`.
The source-written GitHub consumer on #1098 has not been executed from its exact bytes here; **no GAP, Agda typecheck, actual Monster selected word, 6.Suz 78 selection or VOA intertwiner is claimed**.

**Pareto frontier revised:** replace the broad question “does source D4 preserve any nine-plane?” (now constructive YES at quotient/basis level) with the stricter question “can an equivariant 8×10 indexing be built using a **nontrivial ten-sheet D4 action**, or is there a character-theoretic obstruction to any product action?” Keep the original Suzuki character/Monster quotient JOIN in #1250 and the actual Hom/cocycle in #1098 as independent, more important same-object payments.

### 26 October stronger geometric-corner quotient obstruction (supersedes trivial-ten-only frontier)

The pre-existing `Base369Ternary27CornerEightExact` **literal eight cube corners** carry a chosen *natural planar square* D4 action `r(x,y,z)=(-y,x,z)`, `m(x,y,z)=(x,-y,z)`. The latter axis reflection fixes **zero** corners (the diagonal mirror class fixes four). On the actual ATLAS-source `E⊕E` action on 80 nonzero affine quotient labels, **every** D4 reflection fixes **eight** points. Any purported **D4-equivariant map** `quotient80→naturalCubeCorners8` would send each source reflection-fixed label to a target reflection-fixed corner. For the axis mirror, source has eight witnesses and target has none: **no such equivariant map exists**.

This is strictly stronger than the earlier obstruction to ten **trivial** fine sheets: it also excludes *any* ten-sheet action, even twisted, **whose projection to natural geometric corners remains D4-equivariant**. More general 8×10 bijections with D4 mixing corner and fine coordinates and thus **no equivariant corner projection** remain mathematically possible; numerical 80=8×10 cannot choose one. The chosen D4-stable rank-nine Schrödinger plane and the full Heisenberg 720-moving-translation no-go both remain valid. Original ATLAS matrix source SHA256 verified; local exact Python addendum passed, not an actual Monster class-fusion or source-selected-78 receipt.
