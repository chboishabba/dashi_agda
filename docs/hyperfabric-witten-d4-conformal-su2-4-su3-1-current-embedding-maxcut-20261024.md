# Latest-PR Witten/369 max-cut: SU(2)_4 ⊂ SU(3)_1 conformal embedding and D4 operator data

Date: 2026-10-24. Parent: [Agda hyperfabric #1249](https://github.com/chboishabba/dashi_agda/pull/1249);
Lean cross-prover: [#84](https://github.com/chboishabba/dashi_lean4/pull/84).
This **updates the existing canonical Witten owner**
`docs/hyperfabric-witten-cs-wzw-monster-ads3-source-maxcut-20261024.md`,
not another 369 ontology.

## Source authority, authorship and newly updated sibling PRs

**Primary original publication:** J. Lacki and Ph. Zaugg, *Braiding properties for the SU(2)₄ ⊂ SU(3)₁ embedding*, Phys. Lett. B 228 (1989) 223–227,
DOI [10.1016/0370-2693(89)90662-X](https://doi.org/10.1016/0370-2693(89)90662-X). They examine the D4 level-four SU(2) WZW model versus SU(3) level-one and their **actual conformal blocks/braiding**. Classification roots: Cappelli, Itzykson and Zuber (1987), ADE modular invariants; affine/Dynkin index and conformal-embedding literature. The present suite only reconstructs selected **finite** source consequences: Lie/current index, modular branching, fusion and character.

**Newest inspected source heads** (on Oct 24, accessed by GitHub connector; changed further in flight; do not infer unmerged modules are imports):
- Agda TOE [#1217](https://github.com/chboishabba/dashi_agda/pull/1217) at `57e0d8a`: selected 5D CS/E6/KK and source-selected common-action stress **obligations**. 5D `A∧F∧F` CS and 3D CS/WZW are different spacetime form-degree theories; a level-`k` 3D Witten conformal block does not automatically source 5D gravitational/QCD parity/CS. Source #1241 contains the actual physical 5D model negative controls.
- Agda Moonshine/braid [#1239](https://github.com/chboishabba/dashi_agda/pull/1239) at `ed920a8`: selected **Monster C27** weight-two power/character projectors, 729-call source evaluation and genuine 27-charge local-mode open leaves. Also records Griess1990 Albert Peirce product residual `883/8`. Neither `C27` with 27 charged spectral eigenspaces nor the 27 spatial hypervoxel is the new 3-charge `SU3_1` modular category.
- Lean Albert [#52](https://github.com/chboishabba/dashi_lean4/pull/52) at `52cbef8` and Agda #1106: actual 27D Albert product, trace/Peirce and E6 trinification, with full cross-slot triality 341/512 mismatches in chosen isometry. That separate `SU3³`/E6 gauge-theory programme cannot be identified with the 3D topological `SU3_1` from a name alone.
- Agda horned C3 [#1244](https://github.com/chboishabba/dashi_agda/pull/1244) at `1564d5f`/later `bd489b7`: correct characteristic-0 C3 Reynolds/Maschke split and characteristic-3 indecomposable unipotent action on selected 2D module. This is a C3 **group action** on a different carrier. An affine `SU3_1` 3-simple-object modular tensor category has nontrivial braiding and `Q(ζ3)` data; modular S with denominator sqrt3 cannot simply be reduced in characteristic3.
- Lean TOE [#80](https://github.com/chboishabba/dashi_lean4/pull/80) at `d625c09`: selected physical primitive TOE owner; Lean #85 fermionic Fock/charge superselection another independent same-gauge-state donor. **No physical source same-state weld** is claimed by this conformal extension.
- Agda master original `SU2Level4Spin1RepReceipt` k4 five WZW labels, `SU3FromAnyon3FoldReceipt` three Wilson-line labels with physical-promotion prohibition, `LevelRankDualityReceipt` strict level-rank separation, `BulkBoundarySU3Receipt` candidate boundary, and `MonsterGradedVOABridgeExact`. The present cuts **import** these owner terms in Agda, rather than creating a second SU3 theory.
- Existing Witten 1989 CS/WZW and Witten 2007 Monster gravity remain **distinct published theories**. Witten's AdS3 proposal and Maloney-Witten gravity saddle cautions remain as described in the canonical Witten ledger.

## W1+ NEW OPERATION-LEVEL POSITIVE: actual principal sl2 → sl3 index four

Use standard rational 3×3 elementary matrices `E_ij`, source complexification `sl3(Q)→sl3(C)`:

```text
e = E12+E23,
f = 2(E21+E32),
h = diag(2,0,-2).
[h,e]=2e, [h,f]=-2f, [e,f]=h.
tr3(e f)=4, while tr2(E12 E21)=1.
```

In the canonical fundamental-trace normalization, the **embedding Dynkin index is 4**. Hence a chosen affine `SU3` current at **level 1 restricts to SU2 at level 4**, the actual basis of the above 1989 conformal embedding. This is **not** the requested older `SU2_3⇄SU3_1` prime-lane “level-rank” candidate in original `LevelRankDualityReceipt`; that pair has different central charges `c(SU2_3)=9/5 ≠ c(SU3_1)=2` and is **not** the strict SU2_3/SU3_2 level-rank partner.

The adjoint `sl3` has dimension8; the principal `sl2` span `e,f,h` gives spin1 (dim3). From highest vector `v0=E13`, set `v_i=(ad_f)^i v0`, i=0..4. Exhaustive exact bracket checks prove
```text
ad_h(v_i)=(4-2i)v_i,
ad_e(v_i)=i(5-i)v_(i-1),
(ad_f)^5(v0)=0.
rank[e,f,h,v0,..,v4]=8.
```
So `sl3 = 3⊕5` as an actual source Lie representation; the **five spin-2 currents** are the additional dimension-one fields of the conformal extension. Matching Sugawara central charges:
`c(SU2_4)=3·4/(4+2)=2=c(SU3_1)=8·1/(1+3)`.

New `scripts/check_witten_principal_sl2_su3_index4_currents.py`: actual rational-matrix source code, locally equivalent exact SymPy run PASS Lie brackets, index4, all five spin2 ladder relations and rank8. Lean #84 `WittenPrincipalSU2SU3MatrixCut.lean` source-writes native rational principal matrix commutators and trace index; **Lean kernel not run**, imported original publication authority, no affine modes/OPE constructed.

## W2+ NEW full modular branching and Z3 extension: 5→3 by *fixed-point splitting*

The 1989 source conformal embedding has 3 distinct SU3_1 highest-weight modules (0, 3, 3bar) and 5 SU2_4 modules labelled a=0,1,2,3,4. Restricted `SU3_1` characters are

```text
χ^SU3_vac = χ^SU2_0 + χ^SU2_4,
χ^SU3_3 = χ^SU2_2,
χ^SU3_3bar = χ^SU2_2.
```

With 3×5 integral **branching B** whose rows are
`[1,0,0,0,1]`, `[0,0,1,0,0]`, `[0,0,1,0,0]`,
the source D4 modular-invariant coupling
`M=B^T B` has `M00=M04=M40=M44=1, M22=2` and all other entries0. Thus

```text
Z_D4 = |χ0+χ4|² + 2|χ2|².
```

For SU2_4 `S2_ab=sin(π(a+1)(b+1)/6)/√3`
and SU3_1 `S3_ab=ω^(a b)/√3`, `ω=e^(2πi/3)`,
the precise **same chiral-character** intertwining squares hold:

```text
B S2 = S3 B,
S2 M = M S2,
T3 B = B T2 (T phases equal on every nonzero B entry; h4-h0=1).
S2²=I5, S3²=charge conjugation.
```

This is a concrete BIDI/perfectly testable conformal-character transport, NOT an abstract cardinality match or identification of complete Hilbert spaces by invertible map (B is 3×5, rows 1/2 agree).

`SU2_4` initially has only **two invertible simple currents**, a=0 and a=4 (dimensions1); simple-current group Z2, with a=4 **bosonic** conformal weight h4=1. The local algebra extension `A=0⊕4` resolves fixed a=2 (SU2 j=1, qdim2) into TWO distinct `SU3_1` nonvacuum sectors (qdim1 each). Then the **EXTENDED fusion category** is pointed, with
`N_ab^c=1 iff a+b=c (mod3)`; exactly three invertible charges with C3 fusion.

**Critical attribution/no-go:** Z3 emerges from the published Q-system/extension; it is NOT already a subgroup of the original SU2_4 invertible objects and not evidence for a direct unextended C3 WZW symmetry. No physical embedding of selected horned-sphere C3, independent signed-zero C3, Monster C27 or 27-site real-path cube into this quantum current algebra is constructed. The actual local extension/braiding is original mathematical physics by Lacki/Zaugg and CIZ; the new tests verify precise finite consequences.

New `scripts/check_witten_su2_4_su3_1_d4_embedding_exact.py`: exact SymPy source:
`B S2=S3 B`, `[S2,M]=0`, `S2²=I5`, `S3²=C`, source `T` supports, all **27** pointed SU3 Verlinde coefficients and all **81** fusion-associativity checks PASS on independently executed source-equivalent local code. The committed branch file exists in GitHub, byte-exact execution not independently claimed.

New Agda owner `HyperfabricWittenD4SU3OriginalOwnerCutExact.agda` imports PREEXISTING `SU2Level4Spin1RepReceipt`, `SU3FromAnyon3FoldReceipt`, `LevelRankDualityReceipt`, defines literal source branching on their ORIGINAL constructors, gives D4 vacuum mixed and multiplicity-two fixed-point equalities, and refuses physical colour promotion. **Agda kernel UNVERIFIED**.

New Lean #84 `WittenSU2FourSU3OneD4EmbeddingCut.lean`: branch/D4 on actual `Fin5/Fin3`, `C3` pointed fusion/associativity via finite decidability, original `SU2_3/SU3_1` level distinction and `Fin27→Fin3` noninjectivity. **Lean/Lake kernel UNVERIFIED**. Companion `WittenPrincipalSU2SU3MatrixCut.lean` has native 3×3 rational Lie index witness (source, kernel UNVERIFIED).

## W3+ Source/physical acceptance and precise roadmaps

1. **SOURCE CONFORMAL CHIRAL EXTENSION: verified finite data** — actual Lie index and adjoint decompositions, D4 modular matrix, three-sector C3 fusion, no naive SU2_4 chiral isomorphism. The published original Q-system/conformal embedding remains original-theorem authority; this repo has not kernel constructed the full current-algebra extension or any 3D CS path integral.
2. **Worldsheet physical target** — existing selected 26D SU2_k WZW × 23 free/linear-dilaton boson background has nonflat string-frame g,H,Phi, global S3 gerbe, explicit C22 dual, O(3,3) chart Hamiltonian. Replacing just the *chiral* SU2_4 current algebra by SU3_1 via local extension requires its **full nonchiral modular invariant** and correct source target geometry/fields; this does NOT assert S3 ≅ SU3 group manifold (dimensions3 vs8), nor a new topological gravity bulk.
3. **Monster/AdS3** — original sibling Agda #1239 Monster C27 all-grade/twisted level matching, Witten 2007 AdS3 c24, Rademacher/partition saddles, and real Monster Griess modes remain independent. The C3 extended SU3_1 category is NOT directly equivalent to holomorphic Monster CFT (3 vs1 simples, c2 vs24); a physical interface would need a full Q-system/VOA embedding, selected state/Hamiltonian/observable, anomaly, modular sewing and bulk boundary gauge action.
4. **369/27 hyperfabric** — require a finite-to-continuum bounded operator/gerbe descent identifying selected P3³ Laplacian and the ACTUAL WZW current stress, not a `3` label. Latest Agda #1244 char3 indecomposable module warns against using semisimple complex S-matrix as a mod3 group representation. Latest Lean #52 Peirce cross-slot mismatch and existing F4 path-L mismatch remain true and separate.
5. **Current 5D KK/CS/E6** — the new source exact 3D CS–WZW boundary data do not supply a gauge-invariant **5D** `A∧F∧F` action, chiral E6 spectrum, radion vacuum, source stress or empirical LARES; use #1241 and #1217 original physical owners. “Witten CS” word reuse does not create a string/KK dual.
6. **Clay** — no analytic YM/NS/RH/Hodge/BSD/P≠NP source estimate or target is paid by finite Verlinde or branching arithmetic.

**Phase gate:** W1/W2 FINITE SUCCESS, and constructive conformal C3 extension in original external literature; W3 source target/VOA/current mode transport open; W4 physical bulk/quantum/experiment open. No exact-head Agda/Lake typecheck available. Keep current PRs draft and attribute the 1989 embedding to original authors.
