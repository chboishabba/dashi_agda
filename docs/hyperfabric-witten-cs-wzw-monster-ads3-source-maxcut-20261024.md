# Witten in DASHI: exact 1989 CS/WZW, 2007 Monster/AdS3 and non-promotion max-cut

Date 2026-10-24. In Agda hyperfabric PR #1249 and Lean TOE PR #84.
This is a primary-source-referenced theorem-owner audit and a NEW finite
SU2_4 chiral modular/fusion diagnostic. Witten's original discoveries,
the original Monster VOA (FLM) and Verlinde's formula are historical prior
art; source-owner algebra and local test receipts are distinctly attributed.

## 1. There are FIVE differently typed Witten subjects, not one theory

| Source/prior authors and repo location | Actual scope | Source status |
|---|---|---|
| Edward Witten (1989), *Quantum Field Theory and the Jones Polynomial*, CMP 121, 351–399, DOI 10.1007/BF01217730; CS boundary WZW conformal blocks | **3D SU(2)_k Chern–Simons topological theory** with (chiral) 2D WZW conformal blocks, modular S/T, Wilson lines, framing | Published mathematical QFT. Agda master `DASHI/Physics/QFT/{KacMoodyLevelReceipt,SU2Level4Spin1RepReceipt,SU2Level4CarrierReceipt,LevelRankDualityReceipt}.agda` contains source-dependent level and k4 integrable sectors; no full 3D CS path integral locally instantiated |
| Witten (2007), *Three-Dimensional Gravity Revisited*, arXiv:0706.3359 | **Pure/chiral AdS3 gravity ~ extremal holomorphic c24 Monster CFT** gravity/boundary proposal: (J=j-744) | Proposed physical dual; *not* proved pure 3D quantum gravity. Agda open PR **#1239** `docs/monster-ads3-gravity-witten-kk-braid-maxcut.md`, `docs/monster-c24-virasoro-primary-ads3-maxcut.md`, `docs/c3-braid-b3-modular-monster-ads3-gravity-maxcut.md`. The live PR explicitly pays a J finite-character and Virasoro-primary arithmetic, not a 3D bulk |
| Alexander Maloney & Edward Witten (2007/2010), *Quantum Gravity Partition Functions in Three Dimensional Gravity*, arXiv:0712.0155 | Calculated sums over known 3D AdS gravity saddles fail physical sensible partition-function criterion, needing more structures if pure gravity exists | **Adversarial** evidence against claiming J matching implies a bulk |
| E. Witten, *Constraints on Supersymmetry Breaking*, Nucl. Phys. B202 (1982), Witten index | Graded trace/index depending on parity, supercharge, discrete/Fredholm spectral input; not automatically observed SUSY or cosmological constant | Existing `DASHI/Physics/QFT/WittenIndexSUSYBoundarySurface.agda` explicitly records **open** source-target obligations |
| Witten/deformed-de Rham Laplacian semiclassical apparatus | Deformed differential / tunnelling / low spectral asymptotics, not automatically physical Yang–Mills mass gap | Existing `DASHI/Physics/YangMills/WittenLaplacianLane.agda` currently has **all core construction/limit status false**. Do not mix with Witten 1989 topological gauge theory or Monster 2007 |

**Witten-level convention distinction:** 1989 SU(2) Chern–Simons/WZW level `k_affine=4` corresponds to five integrable doubled-spin labels `0,1,2,3,4`, chiral (c=3k/(k+2)=2), and the familiar quantum Sugawara denominator (k+2). Witten 2007 extremal holomorphic gravity `k_grav=c/24=1` has **c=24** (different use of k). Neither is the bosonic string's `26` target coordinates, the Monster's C27 charges, or the actual spatial Cube27.

**Original Monster/AdS3 repo authority:** Agda #1239 at inspected head `c307e47ed2e53d3defa39ace6c531c9390ba5d5c` already owns the exact `J=q^-1+196884q+21493760q²+...` finite series, the Virasoro primary subtraction (196884=196883+1), Brown–Henneaux (c=3\ell/(2G_3)=24) target and non-promotion through bulk saddles; the selected `B3→SL2(Z)` with full-twist/central framing sign; and recent concrete Monster C27/Griess inverse-charge/27-site charge alignment **with uninhabited local 48-edge physical modes**. These are distinct from full Monster VOA, AdS3 quantum gravity and from SU2_4 CS.

## 2. New operational mathematical result: exact Witten 1989 SU2_4 torus Verlinde ring

Source's exact modular S matrix for integrable labels a,b=0..4:

```text
S_ab = sqrt(2/(4+2)) sin(pi (a+1)(b+1)/(4+2))
     = (1/sqrt(3)) sin(pi (a+1)(b+1)/6).
h_a = a(a+2) / (4(4+2)) = [0,1/8,1/3,5/8,1].
c = 2.
```

New script `scripts/check_witten_su2_4_cs_wzw_monster_chiral_cut.py` checks S symmetry and S²=I **exactly over Q(sqrt3)** and all **125 exact Verlinde numbers**

```text
N_ab^c = sum_x S_ax S_bx S_cx / S_0x
       = 1 iff a+b+c even and |a-b| <= c <= min(a+b,8-a-b);
         otherwise 0.
```

It independently checks **625 associativity equations**, the selected fusion `1×1=0+2`, `4×4=0`, and SU2_4 quantum dimensions `(1,sqrt3,2,sqrt3,1)` with global D²=12. All passed on the **local exact SymPy implementation**. The source formula and selected theorem are older Witten/Verlinde mathematics; this is its source-anchored finite *repository test* and selected type-discriminator, not newly discovered fusion.

**Witten framing anomaly from Gauss–Milgram** (exact):
```text
theta=(1, exp(pi i/4), exp(2pi i/3), exp(5pi i/4), 1).
(1/D) sum_a d_a² theta_a
  = exp(2pi i c/8) = i  for SU2_4 (c=2).
```

The holomorphic FLM Monster CFT has *one irreducible chiral module* and `c=24`, with framing phase `exp(2pi i 24/8)=1`. Therefore **SU2_4 chiral CS/WZW ≠ holomorphic Monster c24 chiral representation category**: 5 chiral sectors vs 1 and anomaly `i` vs `1` (two independent action-level diagnostics). It is not a no-go for embedding SU2_4 as a SUBSECTOR or for tensoring with other separately constructed sectors that restore total anomalies; the latter would need source-operational extension proof.

A physical 26D bosonic worldsheet based on `SU2_4` uses it as an interacting chiral/worldsheet *factor* alongside 23 noncompact bosons (one background-charged) and ghosts. The 3D CS bulk is a **distinct topological theory** whose conformal blocks are the same chiral WZW data. The Monster c24 AdS3 proposal is **another** bulk/boundary theory. Do not assert the worldsheet is the AdS3 boundary, or CS topological observables are pure-Einstein gravity observables, without a selected string/brane/boundary map.

## 3. Real source-owner reuse and new typed downstream files

- Original Agda master `DASHI/Physics/QFT/SU2Level4Spin1RepReceipt.agda`: genuine list of five integrable SU2_4 primaries and h_j, source level/k, prior conditional promotion boundaries. Existing `KacMoodyLevelReceipt` distinguishes CS level from affine/current algebra level and separates k1/k3 candidate SM interpretations.
- Original Agda master `DASHI/Moonshine/JCoefficientCharacterBridge.agda` and `MonsterGradedVOABridgeExact.agda`: already own first Monster `196884=1+196883` arithmetic and actual VOA/graded-trace boundary.
- Existing open Agda #1239 `docs/monster-ads3-gravity-witten-kk-braid-maxcut.md` and `monster-c24-virasoro-primary-ads3-maxcut.md`: **canonical Witten 2007** bulk/boundary and Virasoro prior art. No duplicate AdS3 machinery.
- New `DASHI/Unified/HyperfabricWittenCSWZWMonsterSourceOwnerCutExact.agda`: imports original SU2_4 and Monster J owner and records five-vs-one and c2-vs-c24 chiral nonpromotion. **SOURCE WRITTEN**, Agda kernel unverified. The 5 sectors and one holomorphic module are external-theory authority assumptions, not locally reconstructed from the record by this file.
- New Lean #84 `Integration/DASHITOE/WittenCSWZWMonsterChiralCut.lean`: finite truncated SU2_4 fusion ring, 125 source coefficient cases, 625 pairwise associativity conditions, counts and categorical differences. **SOURCE WRITTEN**, Lean/Lake kernel unverified; the actual Verlinde S-matrix equality is paid by executed exact Python, not this Lean ring source term.
- New exact Python script locally run PASS for exact S, Verlinde, quantum dimensions, framing and Monster chiral mismatch. **The committed GitHub script is a source-equivalent rewrite of the executed local file; it has not itself been byte-rerun**.

## 4. Pareto roadmap after Witten archaeology

| Gate | Actual deliverable | Status / acceptance |
|---|---|---|
| W0 Original Witten author/source lineage | Distinguish 1989 CS–WZW, 2007 Monster/AdS3, index, Witten Laplacian and open sibling PRs | **Done** source-audited; citations to original publishers and existing repo theorem owners |
| W1 Finite SU2_4 CS boundary/WZW data | 5 irreducible labels, exact S, Verlinde 125, fusion associativity 625, quant dims, framing `i` | **Done at exact SymPy source mathematics**; kernel native SU2_4 fusion ring remains source-written |
| W2 Negative same-chiral-category test | SU2_4 5 sectors, c2 mod8 anomaly `i` vs Monster holomorphic 1, c24 anomaly `1` | **Selected no-go**; a larger extension could include both, requiring an explicit functor/operational map |
| W3 Source WZW sigma worldsheet | Existing nonflat 26D `R^(1,22)×S3` flux/linear dilaton, patch gerbe, C22 and O(3,3) momentum B-shift | **Leading target math done** in Agda #1249; quantum k+2 frame correction and global string BRST remain open |
| W4 Original 3D Monster gravity | J exact Virasoro primary data, CS/SL2Z modular/braid, Brown–Henneaux source formula and C27 source projector | **Existing Agda #1239**; Maloney–Witten partition saddle and genuine 3D gravity stress/CFT same-object action still open |
| W5 Hyperfabric physical transport | Map original P3³ 27-site graph operator, Albert/F4 27/26 product, and chosen Monster/VOA operators onto selected WZW/CS/3D gravity actions with units and observables | **Not constructed**. Earlier structural no-go and physical source-accounting must be respected |
| W6 Clay and other QFT | Witten Laplacian YM lane and original YM, NS source estimates | **Independent**; no finite CS fusion rule resolves 4D mass gap or Navier–Stokes |

**Highest-ROI next mathematical producer**: formalize one genuine source-selected WZW affine-current/fusion category as a native proof and the corresponding CS conformal-block map. Do NOT spend another cut recreating c24 q-series, SU2_4 integrable labels or the braid B3 modular group homomorphism. **Highest-ROI physical producer**: full 26D WZW worldsheet BRST and same background/target α' scheme + flux gerbe, or separately 3D AdS gravity partition and twisted Monster boundary observables. A physical bridge from one to the other is optional and requires a selected bulk/string setup.


## 2026-10-24 highest-alpha ACTUAL conformal embedding found from latest PR scan

Canonical detailed source and proof ledger:
`docs/hyperfabric-witten-d4-conformal-su2-4-su3-1-current-embedding-maxcut-20261024.md`.
New original 1989 authority: J. Lacki/Ph. Zaugg,
doi:10.1016/0370-2693(89)90662-X, `SU(2)_4⊂SU(3)_1`
conformal embedding with D4 modular invariant.
This directly **uses** original default Agda `SU2Level4Spin1RepReceipt`,
`SU3FromAnyon3FoldReceipt`, `BulkBoundarySU3Receipt`,
`LevelRankDualityReceipt`. Source k4 SU2 and k1 SU3 have
equal `c=2` because the source principal
`sl2⊂sl3` fundamental-trace Dynkin index is **4**.
Actual rational Lie matrices give `[h,e]=2e,[h,f]=-2f,[e,f]=h`,
`tr3(e f)=4 tr2(E12 E21)`,
and `sl3 adjoint=spin1(3) ⊕ spin2(5)`.
Exact local SymPy bracket/ladder/rank run PASS.

Actual source branching of **three** SU3_1 simples (vacuum,3,3bar)
into the original **five** SU2_4 sectors:
`vac→0⊕4`, `3→2`, `3bar→2`.
Hence `D4=B^T B` gives
`|chi0+chi4|²+2|chi2|²`, and the
exact SOURCE modular equalities `B S_SU2=S_SU3 B`,
`[S_SU2,D4]=0`, T-compatible support,
`S_SU2²=I`, `S_SU3²=charge conjugation`.
Original bosonic label4 has h=1 and forms
an order-two simple current; the extension
`A=0⊕4` SPLITS original fixed doubled-spin2
into two distinct quantum-dimension-one sectors.
After extension, SU3_1 fusion is **C3**,
not before. Exact 27 SU3 Verlinde coefficients
and 81 extended associativity checks PASS
on exact local SymPy source (committed scripts
`check_witten_su2_4_su3_1_d4_embedding_exact.py`
and `check_witten_principal_sl2_su3_index4_currents.py`).

**NO IDENTIFICATION**: this does not turn original
signed-zero C3 or horned sphere C3 into a WZW modular tensor
category, nor same-object Monster C27, Albert 27,
physical SU3_colour, 5D E6 Higgs/CS or any 26D sigma
observable. The published extension/affine-OPE theorem
belongs to 1989 original authors, NOT locally proved
by the finite matrices. New Agda real original-sector
branch owner `HyperfabricWittenD4SU3OriginalOwnerCutExact.agda`;
Lean source `WittenSU2FourSU3OneD4EmbeddingCut.lean`,
`WittenPrincipalSU2SU3MatrixCut.lean`. Kernel unverified.

Latest PR audits: Agda #1217 5D parity/CS physical gates,
#1239 Monster C27 729-call source & actual Griess mode
producer (48 edges open), #1244 C3 rational/F3 Maschke,
#1106 Albert/E6 actual product/gauge action;
Lean #52 exact Peirce triality source cross-slot
341/512 residual; #80 physical TOE realization;
#85 Dirac actual charge superselection.
All are sibling source evidence only, no impossible
unmerged typed imports. See precise heads/source
and next phase gates in canonical new D4 ledger.


## Horned geometry/regularity (worker #1247/#1244) overrides Witten C3 overpromotion

The newest exact Witten D4 algebra connects two
chiral RCFTs with a genuine C3 pointed SU3_1
fusion category; **it does not give a group
homomorphism from the perfect Hatcher horn
group into that abelian C3 charge group**.
`G_ab=0` for the classical horned
exterior and `(G³⋊C3)_ab=C3` for
the independently specified three-copy
semidirect algebra; the latter external
C3 sees ROTATION only. The selected
sibling Wilson W belongs to an ambient
non-Abelian SU3 gauge representation,
is noncentral, and already gives an
ordinary S1 same-fringe counterexample.
Such SU3 holonomy cannot become an
SU3_1 anyon label, a Monster C27 charge
or an actual 3D CS Wilson operator from
sharing a group name. With the Hatcher
binary commutator tower, a NONTRIVIAL
selected root blocks jointly (i) uniformly
shrinking representative loops and (ii)
a uniformly bounded compatible unitary
connection. Geometry is the high-leverage
next formal producer, not further
Witten C3 count identities.

Canonical exact-genealogy, new cross
regression and phase frontier:
`docs/hyperfabric-horn-witten-su3-regularity-charge-maxcut-20261024.md`.
Original worker horn and neutrino
test receipts remain in their own PRs;
Lean source theorem and Agda script
in #1249/#84 explicitly unverified for
kernel/physical promotion.
