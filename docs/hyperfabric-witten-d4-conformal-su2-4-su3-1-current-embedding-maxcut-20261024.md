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


## 2026-10-24 attached-worker horn topology / Witten C3 INTEGRATION (highest-value additional no-go)

The canonical new #1249 integrated source report is
`docs/hyperfabric-horn-witten-su3-regularity-charge-maxcut-20261024.md`. It preserves the independently authored,
50/50-receipt-bearing PRs **horn #1244** and **neutrino/Wilson
#1247** instead of vendoring or retroactively claiming their
calculations; their original Hatcher/Gotô/Hosotani sources remain
attributed. The independently tested sibling
`W=TS1` has `||W-I||op≈1.43818847527`,
nontrivial exact Q(zeta3) Wilson trace, and is
**NONCENTRAL** (not one of 1, zeta3I, zeta3²I).
Selected source toy Wilson interference is not horn-specific:
ordinary S1 and free F2 are negative controls.

**Decisive new selected scope**: the source Hatcher
infinite binary commutator group is PERFECT, so every
group homomorphism from the horn subgroup G to the
SU3_1 pointed simple-object FUSION GROUP C3 is TRIVIAL.
After adjoining the external semidirect C3 rotation,
a C3 group charge could record ONLY that external
rotation, not original horn meridians. Therefore
the mathematically valid `SU2_4⊂SU3_1`
`D4` fixed-point extension and its C3 fusion
DO NOT directly solve the horn representation
problem, despite genuine common SU3 notation.
This is a group-homomorphism no-go only, not
a categorical nonabelian defect/functor impossibility.

**More consequential geometric gate**: from Hatcher
`m_w=[m_w0,m_w1]` and elementary unitary
`d([X,Y])≤2d(X)d(Y)`, fixed source
root delta>0 forces `max_{|w|=n} d(U_w)
≥ (2delta)^(1/2^n)/2→1/2`.
If physically corresponding local loops are
uniformly shrinking and the connection is
uniformly bounded in compatible frames, then
holonomies would converge to identity:
**contradiction**. The actual geometric
shrinking-length hypothesis for the intended
three-copy wild exterior is STILL OPEN.
At illustrative `ell_n=2^-n`, n12
requires `M≥2048.528334`; this is
conditional NOT measured or proven
metric behaviour. The existing
`FlatFormalDiskHolonomySurface` must own
real analysis, holonomy-to-identity and
Stokes proof consumers, not a new fake
SU3 gauge field.

New source regression
`check_horn_witten_su3_holonomy_regularity_discriminator.py`
checks exact selected trace noncentre,
horn root gap/depth quantification, 9
one-stage and 81 two-stage C3-commutator
triviality cases and Wilson-character
counterfactual. Lean #84
`HornWittenRegularityAndChargeCut.lean`
holds source-written generic commutator-to-
abelian proof and envelope/centre math.
NO completed physical/VOA/Horn/WZW
intertwiner or kernel typecheck. **Priority
H2 geometry shrinks vs nonsmooth escape
now outranks more cyclic representation
identities.**


## 2026-10-25 stronger NEW geometric max-cut: exact source Wilson norm and diameter countercontrol

Canonically grounded continuation:
`docs/hyperfabric-horn-finite-length-trace-regularity-maxcut-20261025.md`.
**Exact no-eigensolver selected SU3 certificate** from the original
sibling #1247 Q(zeta3) trace:
`ReTr(W)=221179426799/216225930001`;
`||W-I||_op²>= (6-2ReTrW)/3
=854996726408/648677790003 >1`.
This is source arithmetic plus the standard
unitary Frobenius/operator inequality. Thus the
fixed physical representative W would have
delta_op>1 without numerical eigenvalue software.

**Finite-depth no-go rather than only asymptotic**:
the universal commutator envelope
`E_(n+1)(eps)=2(E_n(eps))²` has
`E_n(1/2)=1/2` exactly for EVERY finite n.
If at any complete Hatcher depth all true
holonomy leaves have norm-gap <=1/2,
the selected root delta>1 is impossible.
A concrete analytic source-geometric witness
would be `sup_len_depth(n)=ell_n`,
`sup_compatible_connection_norm=M`,
and `M ell_n<=1/2` with genuinely
matched, whisker-conjugated source generators.
Neither `ell_n` nor M is already certified
for the 3-copy wild exterior; Euclidean
handle *diameters* alone do not supply
path-length bounds.

**Strong new counterexample proving need for LENGTH**:
on smooth Euclidean R², take SU3 gauge
`A=(i diag(1,-1,0)/2)(-y dx + x dy)`
with nonzero bounded constant curvature
and the radius 1/n circle traversed n² times.
Image diameter 2/n->0, pointwise norm
||A|| <=1/(2n)->0, but length=2pi*n,
and holonomy diag(-1,-1,1) at every n.
The original ordinary smooth SU3 gauge
theory is prior art; our concrete exact
high-winding negative control is the new
selected regression. It is NONFLAT
and HIGHLY REPEATED, NOT an actual simple
Hatcher meridian nor a flat-horn countermodel.
Do not infer physical singularity from it.

**New source discrepancy explicitly quarantined:**
Hatcher, *Algebraic Topology* Example 2B.2,
p.172 explicitly states the direct-limit
horn complement is nontrivial with TRIVIAL
abelianization and “highly nonfree”.
The 1968 N. W. Riebe institutional
abstract describes its `G^k` groups as
free countably infinite rank. They cannot
refer to one isomorphic nontrivial marked
group because a free group has nonzero
abelianization; Riebe's full thesis PDF is
access-restricted, so differing spaces/
constructions/abstract wording remain
UNRESOLVED, not an error proved.

**Executed receipt**: new
`scripts/check_horn_geometry_length_trace_maxcut.py`
local source PASS: exact rational trace and
operator-gap bound, 33 exact fixed-depth
envelope checks, numeric consistency for
seven selected depths, seven exact high-winding
negative controls. GitHub committed file exists
and math source is locally reproduced;
**byte-exact Git blob execution is not claimed**.
Lean #84 `HornWittenRegularityAndChargeCut.lean`
appends source-written rational selected
gap/cutoff and radius/winding source lemmas.
Lean/Lake KERNEL UNVERIFIED.

**True Pareto** is to construct/verify an
actual source MARKED meridian loop family
with unitary whisker/basepoint compatibility,
controlled tube clearance and rigorous
metric *length* bounds (or exhibit a
nonshrinking escape), before promoting
any horn-specific Witten/Neutrino/KK
physical claims. D4 SU2_4⊂SU3_1 and
Hatcher's perfect group no-abelian
charge map remain independent mathematical
constraints; no new CS, Monster, Clay or
experiment theorem is paid by this regression.


## 2026-10-25 final horn/Witten source correction and highest-alpha frontier

Canonical focused owner: https://github.com/chboishabba/dashi_agda/blob/chatgpt/hyperfabric-wave-spacetime-cut-20261024/docs/hyperfabric-horn-a5-flat-bundle-onebranch-maxcut-20261025.md

Historical owners: Hatcher's Alexander horn fundamental group; independent Agda horn #1244 owns the nontrivial A5 quotient and finite c=0 VOA; independent Agda neutrino/Wilson #1247 owns the selected noncentral W. Standard icosahedral A5 and flat-principal-bundle monodromy reconstruction are published prior mathematics.

A new finite-image theorem gives a strictly stronger geometric filter for the A5 quotient: every nonidentity element of the standard faithful icosahedral A5 < SO3 < SU3 has operator-gap at least sqrt((5-sqrt5)/2)>1. A nontrivial root commutator forces both children nontrivial recursively, hence ONE sequence of genuinely marked descendant meridians with lengths tending to zero contradicts a compatible uniformly bounded FLAT connection realizing that finite-image representation. This is NOT the unrestricted SU3 result, which required a stronger full-depth small-leaf condition.

A positive independent result is also necessary: the nontrivial representation of the classical Hatcher exterior's pi1 into SU3 automatically yields a smooth FLAT SU3 principal bundle with that holonomy on the OPEN exterior via the standard universal-cover construction. It need not have connection coefficients uniformly bounded near the excluded wild boundary. Thus abstract smooth-flat existence is positive, and the physical regularity requirement is the live issue. The SU3 principal bundle over this 3-manifold is topologically trivial by standard low-dimensional obstruction theory.

Three genuine exact source regressions have passed locally with byte-for-byte Git blob hash verification:
(A) A5 60 elements / 3600 commutator pairs / 8 synthetic collar stages / 127 topological parent-child WINDING mismatch controls; Git blob bce4f345d18912687bcf2d4a99d469376db39754.
(B) smooth FLAT punctured-plane order-five single winding loops, shrinking length and connection coefficient norm growing as 1/r; Git blob b15a80bc228f213f3918c2fd3509499034620f34.
(C) smooth bounded NONFLAT SU3 on simply connected R2 with different Wilson holonomies on homotopic contractible loops; Git blob 4876fffbcc823aebf929c6b0bd6ef29b42591ece.

The synthetic geometric collar is explicitly NOT Hatcher marked: each of 127 parent circles has child-core winding (1,0) versus (0,0) for the required commutator, proving a literal topological rejection instead of a decorative failure flag.

The selected separate #1247 W has nonzero imaginary trace because its exact zeta3 coefficient is nonzero. Every element, and every SU3 conjugate, of the chosen REAL icosahedral A5 < SO3 subgroup has real trace. Thus W cannot be identified with the A5-root holonomy in that representation. The original two selected math programmes must remain separately typed.

MOST IMPORTANT PHYSICAL PRECONDITION: Hatcher's pi1 relation between meridians implies a relation between holonomies automatically ONLY for FLAT monodromy representations. With nonflat connection, Wilson holonomy depends on the geometric representative; a controlled non-Abelian Stokes/homotopy/curvature-defect estimate is essential. Earlier loose wording about arbitrary bounded nonflat connections is superseded. The original FlatFormalDiskHolonomySurface mathematical interface owns the unresolved Stokes/analytic terms.

Lean #84 adds SOURCE-WRITTEN generic all-descendant-nontrivial, one-short-marked-descendant/finite-gap contradiction and selected Wilson nonreal trace certificate. Lean/Lake and Agda kernels not run; no actual source-coordinate three-copy Hatcher collars or uniform physical connection, no Witten/Monster/TOE identification and no Clay theorem.

Current Pareto: construct genuinely linked Hatcher Z-block collars with van Kampen parent-as-commutator marking, collar clearance, arclength and compatible whisker/gauge data for ONE descending branch; if that exists, the finite A5 uniformly bounded flat realization fails. For general curved gauge fields, separately quantify homotopy-surface curvature defects.