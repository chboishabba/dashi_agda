# 2026-10-25 — Actual ATLAS source words versus ambient GF(729) D4

## Original sources and inherited ownership

- **ATLAS / AtlasRep**: original `2.Suz:2` 12D GF(3) matrices. Existing source hashes, original role and public-mirror custody are recorded in `data/atlas/monster3b_suz12_source_manifest_20261012.json`, originally owned by PR #1098. Do NOT assign matrix authorship to this new audit or to the mirror.
- **Earlier repository mathematics PR #1098**: `outputs/monster3b_atlas_compression_field_selector_20261012.json` selected a degree-six GF(729) field chart, modulus `x^6+x^5+x^4+1`, chosen primitive generator coordinates `(0,1,0,1,1,0)` and order728. `outputs/monster3b_selected_heisenberg_lift_20261012.json` paid the exact quadratic central correction for a selected source word. These receipts and Agda code remain the mathematical donors, not replaced.
- **Barraclough–Wilson (2007)**, DOI `10.1112/S1461157000001352`, provides the original Monster N(3B) subgroup/character theory. [ATLAS Suzuki standard-generator data](https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Suz/) distinguishes a quotient `Suz:2` generator of order2 from its `2.Suz:2` preimage. The latter need not have order2. The source explicitly calls the double-cover generators *preimages*; lifting an involution does not automatically preserve its order.
- **PR #1250** is the actual Monster class/6.Suz family selection owner; **PR #1148** is the JFine H4 finite source owner; #1162/#1217 retain proof-relevant actual-Monster primitive-gate status. Never identify these separate mathematical objects by matching degree or labels.

## New exact source-word discriminators

`scripts/monster3b_atlas_source_word_order_d4_gate.py` consumes the **original already-vendored** `2Suzd2G1-f3r12aB0.m1`, `.m2` and the **previously computed** 12×12 selected-word receipt. It asserts over GF3:

1. Source outer `g1` has order4, **g1²=−I12**, and selected outer `g2` has order3. The source `g1` has symplectic-similitude multiplier `−1` from the older manifest. Consequently **g1 is NOT an involutive D4 mirror** despite its induced order2 action in a suitable quotient.
2. The earlier selected matrix word `g2 g1 g2^-1 g1 g2^-1` has order6 and **third power −I12**, so **it is NOT an order4 D4 rotation**. Its square is a nontrivial order-three unipotent; with `N=M²−I`, `rankN=6`, `rankN²=2`, `N³=0`. Hence the GF3 Jordan partition is exactly `3+3+2+2+1+1`. This is a *finite matrix-type certificate*, not a full Monster class name.
3. Neither negative says that a different **longer** ATLAS word cannot give a centre-inverting involution or suitable order4 rotation. A bounded short-word search alone would not establish global absence.

The order4/6 and rank data were checked independently in current-turn GF3 JavaScript directly against fetched original repository matrices and JSON; the exact committed source script has not been executed from its GitHub checkout in this session. No Agda/kernel, GAP/CTblLib or live source class-fusion receipt is claimed.

## New constructive AMBIENT D4 in the selected field chart

`scripts/monster3b_gf729_ambient_d4_similitude_source_boundary.py` reuses the same selected modulus and primitive `gamma`, without new geometry or new group multiplication.

Let `alpha=gamma^182`; because `gamma` has order728, `alpha` has order4 and `alpha²=−1`. Let `A` be the 6×6 matrix multiplication by alpha on the selected GF729 coordinates. Let `F` be the 27th-power Frobenius map (`x↦x^{3³}`), an involution on GF(3⁶). Since `27 ≡ −1 (mod4)`, `F A F = A^{-1}`.

Define matrices on the existing six-pair 12D Heisenberg quotient:

```
R = diag(A, A^{-T})
M = diag(F, −F^{-T}).
```

They satisfy `R⁴=I`, `R²=−I12`, `M²=I`, `MRM=R^{-1}`; if `J` is the inherited standard symplectic pairing, then `RᵀJR=J`, `MᵀJM=−J`. In the existing H6 asymmetric cocycle chart `c=b·a'`, use the exact central rechart `t=c+a·b`. Then the group lifts by `(v,t)↦(Rv,t)`, `(v,t)↦(Mv,−t)`, converted back to `c` via `c'=χ(c+a·b)−a'·b'`.

**Independent current-turn local Python execution passed** the primitive root/order tests, D4 group relations, both symplectic-similitude identities and **56,862** Heisenberg generator-product checks. It constructs a D4 subgroup of the **ambient `GSp12(F3)` group**, **NOT** an actual `2.Suz:2` or Monster normalizer subgroup. Its Frobenius mirror is not a verified word in the ATLAS generators.

## Connection to actual JFine and Monster frontier

- PR #1148 now has an independent **actual H4-module Fourier equivalence**, not just same dimension: `10×Reg(H4)_ζ = 810×Schr4`, `90×Res_H4 Schr6 = 90×9×Schr4`. It still needs the actual source H4 embedding and D4 equivariance. See `scripts/iit_jfine_h4_central_phase_fourier_intertwiner.py` on the IIT PR, which passed 6,561 DFT Gram checks and 59,049 exact source/target group-generator equations locally.
- The ambient D4's `R²=−I12` is an actual *finite-field operator statement*. It cannot identify the Monster involution as 2A rather than 2B without the original Monster class fusion/element word. The `M²=I` ambient mirror likewise does not prove any such involution in the original ATLAS `2.Suz:2`.
- PR #1250 has source-bounded **full D4 character and C3 product-summand obstructions**, plus a C3-compatible signed repair that fails unchanged regular H4 intertwining. Those negative results and this ambient positive group-theoretic result operate on different objects; none supersedes the others.

## Pareto / Ibrahim / snowball cut

1. **Source-selected full degree78 6.Suz character and quotient receipt** from existing #1250 CTblLib/Barraclough–Wilson exporter/matcher remains first; no invention of character classes.
2. **Actual field group membership** if the D4 hypothesis is pursued: find explicit ATLAS generator word `w` with `w²=I`, multiplier `−1` and the conjugacy relation `w r w=r^{-1}` for a *source* order4 `r`; then verify selected Monster class power/fusion. A mere ambient Frobenius matrix is insufficient. The known source g1 itself fails the order2 test.
3. **Whole-character/isotypic-first consumer** from `IbrahimMonster3BRecognitionRouteParetoExact`, then #1098 `Hom_E(Hζ,Wζ)` source action and multiplicity evaluation. Reuse the earlier classwise character / quotient Galois tests; no new 729dim Schreodinger theorem owner.
4. Reject new OEIS/42d, physical Ferrocell, base369 or related patterns as proof unless same mathematical object, original source, group action and relevant consumer are explicitly identified.

### Acceptance command (when working with this PR checkout)

```sh
bash scripts/check_monster3b_gf729_d4_source_ambient_cut.sh
```

**Statuses:** exact local field arithmetic and prior source matrices checked; code committed; exact GitHub branch-source execution, Agda formal kernel, source-group membership in `2.Suz:2`, actual Monster class fusion and physical realization all remain separate and **unverified**.


## Primary-source Section 9 auxiliary split versus actual diagonal quotient

**Additional 25 Oct source audit (original computational article, not a repository inference):** Thomas Breuer, Kay Magaard and Robert A. Wilson, *Some steps in the verification of the ordinary character table of the Monster group*, [full executable report](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/htm/ctblm.htm), Section 9 (original URL, 12 December 2024 document version). The source uses **H**, the split extension of N=3^(1+12) by 6.Suz.2, with `X × Z(N)` a C3² centre, and **distinguishes** `H/X = 3^(1+12):2.Suz.2` from the final **diagonal factors `H/D1`, `H/D2`**; the source selected Monster group is a factor, not an identification with H/X by notation alone. In Section 9.2 the authors say their **auxiliary `H/X`** factor's 12D action is symplectic and split, and explicitly construct it from original `M3max7G0-f3r38B0` matrices. They then combine it with a 6.Suz.2 source quotient and select the Monster diagonal factor by additional original power/fusion tests. Their original derivation (historically before this repo) retains independent authorship.

The existing #1098 source manifest instead records the **ATLAS `2Suzd2G1-f3r12aB0`** 12D generators and an outer similitude multiplier 2 on the **selected inner alternating form**. Both are real finite source descriptions, but **the present repository has not exhibited an intertwining word/basis and central-layer identification** proving that this specific source ATLAS 12a module equals the auxiliary BMW 14×14 block's representation with the same generator placement. No contradiction in the original literature is asserted: source group extension labels, action choices, and centre/diagonal coordinate may differ. Critically, **do not replace the actual diagonal quotient's selected central generator by the auxiliary (H/X) centre using mere dimension, group label or abstract semidirect-product isomorphism**. The correct test needs original explicit generator words, class fusion and the correct diagonal kernel choice. Source report section 9 and the earlier `IbrahimMonster3BDiagonalKernelPaidSignGaugeCorrectionExact` already own that custody boundary.

**New stop rule:** The ambient `GF729` D4 R,M gives actual matrices of `GSp12(F3)` and an H6 automorphism, not an actual (H/X) generator embedding nor a selected (H/D_i) action. Source `2Suzd2` g1 order4 is a *source matrix check*, not a general no-outer-involution theorem for either auxiliary or selected quotient. Upgrading either requires original class/quotient/word/intertwiner evidence, then reusing the existing #1250 selected-78 source matcher and #1098 Hom compiler.


## Newest PR #1250: all-conductor source-character checker supersedes the Q(zeta3)-only shortcut

During the latest cross-PR archaeology the **actual owner** #1250 advanced beyond the earlier portable `Q(zeta3)` approximation: `scripts/monster_3b_suzuki_all_conductors_export.g` acquires the original `Conductor(x)`, exact `CoeffsCyc(x,n)` with full conductor, original class orders/sizes/power map and all 12/78 source rows. `scripts/monster_3b_suzuki_all_conductors_character_audit.py` independently compares the full class functions in exact cyclotomic quotients `Q[x]/Phi_n`, with Galois conjugation, exact class-weighted orthogonality, Sym² and dual comparisons. New genuine mixed-conductor finite fixtures and negative controls are source-written and locally independently tested. They are **not** GAP/CTblLib authentication, selected Monster family evidence, or Agda kernel receipts.

This is significant because faithful 6.Suz character values were **not originally guaranteed to lie in Q(zeta3)**; hard-coding conductor 3 could fail before the selected same-object class test. The all-conductors owner fixes this **checker implementation limitation** without changing underlying Barraclough–Wilson, ATLAS, Nebe, Serre or GAP scholarly attribution. The actual source-selected main→MN3B→Monster quotient matcher remains #1250's authoritative pipeline. PR #1098 must consume its future full selected-character certificate, not fork either fast-path or full-conductor polynomial arithmetic.

Cross-reference latest #1239 source-authorized `C27` rational conductor projectors only for projector-reduction *prior art*; that 27A/B VOA object is **not** automatically the selected 3B normalizer or the current H4 Fourier basis.

The source-weld max-cut thus has two independent positive calculations (H4ζ Fourier 810-copy equivalence, ambient GF729 D4/GSp group equations), two source-word stop signs (Atlas g1 order4, selected word order6), and a distinct still-open high-value **actual selected Suzuki 78 quotient/Hom-space** object.


## 26 October: ATLAS standard-generator semi-presentation alignment

**Original source (not repository authorship):** ATLAS [sporadic Suz standard generators and semipresentation](https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Suz/), as provided by the ATLAS of Finite Group Representations contributors, states that the quotient `Suz:2` standard generators `c,d` have orders `2,3`, `cd` order `28`, and `cdcdcddcdd` order `7`. Its `2.Suz:2` generators `C,D` are **preimages**, not required to preserve orders.

**Current source-word exact matrix result:** using the PREEXISTING manifest-pinned 12D GF(3) ATLAS files `data/atlas/2Suzd2G1-f3r12aB0.m1` and `.m2` on #1098, independently computed in exact GF3:

- `C²=-I12`, `o(C)=4`, `o(D)=3`;
- `(CD)^28=-I12`, `(CD)^56=I12`, and no smaller proper projective order (divisors 1,2,4,7,14), hence **linear order 56 and projective order 28**;
- `W=CDCDC D D C D D` (unambiguously source literal `cdcdcddcdd`) has **linear order 7**.

Consequently the stored faithful matrix pair respects the named ATLAS quotient *semi-presentation* exactly at the projective level. This pays a concrete **generator-alignment and double-cover identity** which the previous source-order 4/3 and selected-word 6 evidence did not. It still does **not** prove the generated matrix group has all of `2.Suz:2` without relying on the original ATLAS source files, and it certainly does **not** supply a Monster selected diagonal quotient class word.

**Regression and authority:** extend existing `scripts/monster3b_atlas_source_word_order_d4_gate.py` (do not duplicate checker) to require the above projective order28 and order7; independent V8 GF3 matrix replay passed. ATLAS is the single primary source root; its copy and mirror are NOT independent corroborations. Existing manifest hash and #1098 original proof owners preserved. Distinct source `2.Suz:2` versus `Suz:2` lift status must survive the Ibrahim/consumer chain; no actual Monster 3B word, 6.Suz selected-78 family, C3/H6 phase action or kernel theorem follows.

**Related latest-PR Pareto inspiration:** #1260 constructs a ring with additive group `C81×C243`, which has cardinality `3^9` but **is not** the exponent-three additive `F3^9` or extraspecial `H4` source group. The new higher-power (nilpotent) λ-adic transfer is therefore a *different object*, useful for consumer-specific torsion diagnostics but not an alternate Monster 3B action. #1261's integer D4h sample source is also a *different* crystallographic representation, not an ATLAS group word. Original source roles and all coefficient-characteristic boundaries preserved.


## 26 October: exact ACTUAL ATLAS 2.Suz:2 D4 source subgroup witness

**Substantive supersession:** The previous statement that the ambient GF(729) D4 had no known source-group membership was true **for that PARTICULAR ambient pair**, but should not be misread as a universal absence of D4 inside the 2.Suz:2 source group. There now exists a separate, concrete **ACTUAL source-word D4 subgroup** of the previously vendored ATLAS (2.Suz:2) GF(3) matrix representation.

### Source names, exact straight-line words and group presentation

Let (C,D) be the ORIGINAL ATLAS 12×12 GF3 matrices at `data/atlas/2Suzd2G1-f3r12aB0.m1` and `.m2`. Use lower-case `c=C^-1`, `d=D^-1` (this is local word notation, not a different ATLAS group).

```
W = CDCDCDCDCDCdCd   (14 letters, linear order 10)
g = CdCdCDCd         (8 letters, invertible)
m = W^5             (outer/anti-symplectic linear order 2)
m' = g m g^-1        (another outer involution)
r = m m'            (strictly symplectic linear order 4)
```

Exact arithmetic over F3 gives:
`m²=I12`, `(m')²=I12`, `r²=-I12`, `r⁴=I12`, `m r m=r^-1`. The eight elements therefore form an injective representation of **D4**: (r) genuinely has order4, (m) has order2 and conjugates (r) to its inverse. Unlike the earlier ambient Frobenius model, **each matrix is an explicit word in the original ATLAS source generators**.

The source group's invariant alternating form is a unique one-dimensional line: independently solving the 288 linear equations on 66 alternating coefficients for `CᵀJC=-J` and `DᵀJD=J` over GF3 yielded constraint rank65, nullity1, and a form of matrix rank12. A complete 12×12 witness is now pinned in the executable source file. Consequently `mᵀ J m=-J` (centre-inverting similitude) and `rᵀ J r=J` (strict symplectic), by exact matrix equations, without character inference. `m` and `mr` each have a six-dimensional +1-eigenspace.

**Unexpected representation-theoretic negative:** since `r²=-I12`, the source 12-dimensional D4 quotient module has NO nonzero fixed vectors for the half-turn and contains **zero one-dimensional D4 irreducibles**. In characteristic 3 (Maschke applies because 3 does not divide 8), it is precisely `6 E`, six copies of the standard two-dimensional D4 representation. The earlier #1148 nongeometric eight-trit `A1+A2+2B1+2B2+E` action has **six** r²-fixed dimensions. A D4-equivariant linear injection of THAT eight-dimensional module into THIS actual source 12-dimensional D4 module is impossible: every one of its six r²-fixed vectors would map into the zero fixed space of `-I12`. This is a **same-action non-embedding theorem** for these specific two finite objects, not a no-go for all possible Suzuki D4 subgroups or Monster Heisenberg embeddings.

### Provenance and executable acceptance

`scripts/monster3b_atlas_actual_d4_word_witness.py` is committed on #1098 and imported into the existing backend-free `scripts/check_monster3b_gf729_d4_source_ambient_cut.sh` regression. It FAILS CLOSED unless both original ATLAS source-file SHA-256 hashes match the pre-existing #1098 manifest (m1 `ddd4919a...`, m2 `433ba0f...`). Independently reproduced original source bytes in local Python and checked their COMPLETE 64-character SHA256 digests, plus all source words, D4 relations, GSp multipliers and fixed-space ranks. Exact *committed branch* script re-execution, Agda kernel, authentic GAP/CTblLib actual Monster diagonal quotient and 6.Suz 78-family selection are NOT claimed.

**Original source authors retain credit:** ATLAS/AtlasRep contributors provide the faithful 2.Suz:2 matrices and quotient Suz:2 standard-generator test `o(c)=2,o(d)=3,o(cd)=28,o(cdcdcddcdd)=7`. Barraclough--Wilson (2007) and Breuer--Magaard--Wilson (2026, published original) provide actual Monster N(3B) quotient and character construction. Reused #1098 source bytes/proofs, #1148 8D finite model, and #1250 Monster fusion owner are separate. This current exact matrix-word witness is **DASHI derived arithmetic**, not an externally sourced claim of a particular Monster group embedding.

**Next maximal Pareto:** identify this explicit D4's selected class fusion and lift through the **correct diagonal H/D_i** (not just auxiliary H/X); test `r²=-I12` source class in the Monster normalizer and the actual selected `6.Suz` multiplicity character via existing #1250 all-conductor GAP exporter/main-to-N3B matcher. The existing #1098 true `Hom_E(Hζ,Wζ)` and its projective cocycle is the downstream consumer. Avoid reopening source H4 cardinality, generic Fourier, repeated OEIS/λ9 count coincidences or physical toroidal interpretations.
