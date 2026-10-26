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


## 26 October: classical Schur–Zassenhaus lifts the source D4 into actual N(3B)

This is a SOURCE-BASED ACTUAL-GROUP existence corollary, not merely a new model:

1. The original Barraclough--Wilson (2007) `N(3B)` is a finite maximal subgroup of the real Monster and has shape `3^(1+12).2.Suz.2`. The original Breuer--Magaard--Wilson character verification, Appendix 9, likewise states `N(3B)` has normal extraspecial 3-group `E` of order `3^13=1594323` and quotient `Q≅2.Suz.2`. Original group existence/class table is these authors' result, not DASHI's.
2. The preceding **source-word** GF3 matrix witness gives `S≅D4`, `|S|=8`, a genuine subgroup of the original ATLAS `2.Suz:2` (faithful representation) *abstractly identified* with `Q`. No choice of a diagonal `H/D_i` action is necessary for this abstract subgroup existence statement; the quotient ISOMORPHISM must still be distinct from a matrix intertwiner.
3. Let `P=pi^-1(S)≤N(3B)`. Then `E⊲P`, `P/E≅D4`, `|E|=3^13`, `[P:E]=8`, `gcd(3^13,8)=1`. Thus E is a normal Hall 3-subgroup of **P**.
4. By the classical **Schur–Zassenhaus theorem** (Schur and Zassenhaus; not re-proved here), E has a complement `K≤P` with `K≅D4`, and because E is a solvable p-group all such complements are conjugate by E.

Therefore the actual finite Monster (3B) normalizer contains **an abstract D4 subgroup** and the existence is a genuine mathematical implication of the original source structure + exact source-word subgroup + classical theorem. This is a stronger statement than the previous open *existence of some D4*; mark that leaf CLOSED at the **source-derived mathematical argument** level, but **NOT** at Agda kernel level. The literal Monster element words and explicit quotient section remain OPEN. This does not establish that *this* subgroup has the previously desired Monster class fusion `4B/2A/6D/12G`, preserves JFine's full pointed 196830 module, selects the faithful/nonfaithful `6.Suz` 78, or supplies `Hom_E(Hζ,Wζ)`. In fact this source D4 is `6E` on the F3^12 quotient with r²-fixed dimension0, and cannot contain the earlier 8D A2 JFine module (r²-fixed dimension6) as an equivariant injective submodule.

**Source inheritance and authority.** Original group/normalizer: R. W. Barraclough, R. A. Wilson, *The Character Table of a Maximal Subgroup of the Monster* (2007), DOI 10.1112/S1461157000001352; T. Breuer, K. Magaard, R. A. Wilson, *Verification of the conjugacy classes and ordinary character table of the Monster* (*J. Algebra*, volume703, 2026), DOI 10.1016/j.jalgebra.2025.09.034, with computational [CTblLib Appendix 9](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/htm/ctblm.htm). Original source group matrices and semipresentation: [ATLAS Suz page](https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Suz/). Schur–Zassenhaus is classical (not repo-derived); e.g. Kurzweil--Stellmacher, *The Theory of Finite Groups*, §6.2.1. Our contribution is a **particular short explicit GF3 source-word witness and the coprime-preimage application**, not the underlying group or theorem.

**Pareto change:** retire the unqualified task "does any real N3B D4 exist?" in favour of `specific source D4 class fusion / selected H/D_i quotient and ζ↔ζ² action`; keep #1250's original all-conductor selected-78 table and #1098's actual linear Hom/projective-cocycle as downstream owners. Consume the source receipt through a named type and exact source hash, not an unsourced abstract `D4` label. Agda kernel still unverified.


## 26 October: source D4 phase-sector parity bound and complement independence

**Schur–Zassenhaus additionally pays choice-independence up to conjugacy.** For the fixed inverse-image group `P=π⁻¹(S)`, all complements to the normal Hall 3-group `E` are conjugate by E (E is a solvable p-group). Hence any specific quotient element's **Monster conjugacy class** is constant among its lifts chosen through the different complements: the lifts are E-conjugate. This does **not** compute which Monster class it is, nor choose a word in the selected Monster generators. Retain original theorem authorship Schur/Zassenhaus.

**Selected phase parity discriminator (EXPLICITLY conditional on the actual E/Z(E) module weld).** Our source D4 satisfies `r²=-I12` on the original ATLAS 12D quotient. IF an equivariant identification transports this exact action to the actual `E/Z(E)≅F3^12` of the selected Monster 3B normalizer, then on the unique degree729 Schrödinger representation `H_ζ`, the symplectic half-turn is implemented by scalar times parity `P|x>=|-x>`, `x∈F3^6`. Exactly one basis coordinate is fixed (`x=0`), while 364 pairs transpose, so `Tr P=1` and the ± eigen-dimensions are 365 and364. On the full phase sector `W_ζ≅H_ζ⊗S_ζ`, `dim S_ζ=90`, the order2 lift's trace therefore has absolute value **at most90**, regardless of the still-unknown selected 78-family character. No independent full basis identification is inferred.

The already-owned #1250 original Monster power/fusion data give for a phase-preserving order2 element:
`2A/6D → Tr(Wζ)=1458`, `2B/6B →66`, `2B/6E →90` (from `(χ196883(t)-χ196883(zt))/3`). Consequently **IF** source `-I12` is indeed the same actual E/Z action, the source half-turn **cannot** fuse by the `2A/6D` route; the two `2B` possibilities are not excluded by this bound. This is a consumer-relative negative claim conditional on the missing module-intertwiner, not a new asserted Monster conjugacy class. The prior *geometric JFine* `r²` phase trace1458 likewise fails for this **particular** source D4. A different source D4 may satisfy a different bound.

`scripts/monster3b_atlas_actual_d4_word_witness.py` now exactly enumerates all 729 finite Schr6 parity basis vectors and verifies trace1/364 transpositions, as a mathematical fixture. Both source ATLAS matrices are SHA256 verified; source same-object E/Z recognition, actual GAP/CTblLib Monster fusion, and Agda kernel remain unverified. **Pareto:** a single selected quotient-module intertwiner and existing #1250 class-fusion data can turn this strict conditional exclusion into a source-specific Monster result; more H4 cardinality, abstract Fourier or λ-adic coincidence work cannot.


## 26 October: existing kernel-verified mathlib4 Schur–Zassenhaus donor

The classical normal-Hall complement theorem is **already formalized in the ORIGINAL mathlib4 community library** at [Mathlib.GroupTheory.SchurZassenhaus](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/SchurZassenhaus.html). The exact documented API is:

```lean
Subgroup.exists_right_complement'_of_coprime
  {G : Type u} [Group G] {N : Subgroup G} [N.Normal]
  (hN : (Nat.card ↥N).Coprime N.index) :
  ∃ (H : Subgroup G), N.IsComplement' H
```

For the PREIMAGE `P=π⁻¹(S)` of our SOURCE D4 `S`, use `N=E ≤ P` with `Nat.card E=3^13`, `E.index=8`. The one specific arithmetic premise is `(3^13).Coprime 8`. The resulting complement has group-isomorphism `K≃* S ≃* D4` by quotient restriction, conditional on actual subgroup/quotient receipts. This gives a high-alpha proof route with **no duplicate Schur–Zassenhaus formalisation**. Mathlib4's authors and previous subgroup/quotient and group-iso producers retain theorem ownership.

**Still missing in the currently connected Agda/Lean repository HEAD:** a *source-typed actual* `MonsterN3BGroup`, `E.normal`, `E.card=3^13`, an actual quotient isomorphism to `2.Suz:2`, and a certified embedding of the source 8-element D4 into that exact quotient carrier. A finite matrix witness in the ATLAS GF3 model plus a paper theorem **does not create a Lean inhabitant** of those object-specific assumptions. The abstract mathematical inference is valid with published sources, but a repository kernel receipt has not yet been assembled. Keep this distinction in any future cross-prover snowball.


## 26 October SOURCE-WORD 720+9 polarization max-cut

New consumer `scripts/monster3b_atlas_d4_pointed720729_polarization_weld.py`
**reuses** the same SHA256-verified original ATLAS/AtlasRep MeatAxe
`2Suzd2G1-f3r12aB0.m1/.m2`, the existing actual-source D4 generator words
`m=(CDCDCDCDCDCdCd)^5, g=CdCdCDCd, r=m(gmg^-1)`, and the original
`FORM_ROWS` nondegenerate anti/symplectic pairing. It does not vendor or
replace these original source bytes.

In original characteristic-three **12D symplectic quotient coordinates**,
`Fix(m,+1)` has rank six and is a Lagrangian because the mirror multiplier
is -1. On this 6D plus-eigenspace, the symmetric form
`Q(u,v)=<u,r v>` is nondegenerate and has determinant **2 in F3**, hence
**split Witt index three**. A concrete totally singular 3-space can be
chosen with coordinate vectors (relative to the deterministic
nullspace basis)
`(0,0,0,1,0,0)`, `(0,1,2,0,0,1)`, `(1,0,0,0,0,1)`.
The six original 12D vectors `v_i, r v_i` form a verified
`D4`-stable **rank-six Lagrangian**; its first pair `v_1,r v_1`
is a source `D4`-stable **rank-two isotropic plane**. The resulting
six-trit Schrödinger **basis LABEL model** has an invariant nine-point
plane. This is stronger than the earlier ambient-field-only D4.

On the quotient `F3^6 / F3^2 ≅ F3^4`, the actual source-word
D4 representation is `E⊕E`. Its 80 nonzero vectors have
**8 D4 orbits of length 4 and 6 orbits of length 8** (14 orbits).
Each of the four D4 reflections fixes **8** nonzero quotient points;
the half-turn and quarter-turns fix none outside the origin.
A direct `Corner8×Fin10` action with trivial fine sheet would force
all fixed counts to be multiples of 10; **8 is not**, providing an
exact D4-set obstruction to *that* product action. Nontrivial action
that mixes ten fine sectors remains possible and must be tested, not
dismissed. This refines and is consistent with #1250's pointed
720+9 full-Heisenberg-invariance no-go: source D4 *can* stabilize a
chosen nine-plane while translations outside F3² cannot.

Independent local Python replay on the **actual original source matrices**
verified exact SHA256:
`ddd4919ab560f78b065aa08e309bd047942cdb7bb52a1474da84d54d35a031c2`
and
`433ba0f0373995b159859df00dd5a5005355fdbf8b59a31d651aeaf43ffcd15f`,
full rank/isotropy/action/orbit counts and mirror signatures PASS.
**Exact new GitHub Python file itself, Agda kernel and GAP NOT executed**.
Local independent source:
`/mnt/data/monster3b_maxcut_720729/check_atlas_d4_pointed_source_weld.py`;
receipt:
`/mnt/data/monster3b_maxcut_720729/atlas_d4_source_weld_receipt.json`;
hash:
`2c74c56774b9ffe3e40f3a809d8b0029aec8f36a99762b7cdd033a377e11c0f2`.

**Proof frontier:** The source `2.Suz:2` matrix words are actual;
their proper `N(3B)` quotient lift, Monster conjugacy classes, and
selected 6.Suz 78/729 normalizer action/intertwiner remain separately
unpaid. A centre-inverting mirror maps ζ to ζ²; a D4 basis permutation
is not a linear D4 action in one fixed ζ-eigenspace. Original ATLAS/AtlasRep,
Wilson 1988, Barraclough–Wilson 2007, Serre/Terras authorship retained.
Pointed 720+9 original repository owner and caveats:
[#1250](https://github.com/chboishabba/dashi_agda/pull/1250).


### 26 October stronger geometric-corner quotient obstruction (supersedes trivial-ten-only frontier)

The pre-existing `Base369Ternary27CornerEightExact` **literal eight cube corners** carry a chosen *natural planar square* D4 action `r(x,y,z)=(-y,x,z)`, `m(x,y,z)=(x,-y,z)`. The latter axis reflection fixes **zero** corners (the diagonal mirror class fixes four). On the actual ATLAS-source `E⊕E` action on 80 nonzero affine quotient labels, **every** D4 reflection fixes **eight** points. Any purported **D4-equivariant map** `quotient80→naturalCubeCorners8` would send each source reflection-fixed label to a target reflection-fixed corner. For the axis mirror, source has eight witnesses and target has none: **no such equivariant map exists**.

This is strictly stronger than the earlier obstruction to ten **trivial** fine sheets: it also excludes *any* ten-sheet action, even twisted, **whose projection to natural geometric corners remains D4-equivariant**. More general 8×10 bijections with D4 mixing corner and fine coordinates and thus **no equivariant corner projection** remain mathematically possible; numerical 80=8×10 cannot choose one. The chosen D4-stable rank-nine Schrödinger plane and the full Heisenberg 720-moving-translation no-go both remain valid. Original ATLAS matrix source SHA256 verified; local exact Python addendum passed, not an actual Monster class-fusion or source-selected-78 receipt.

## 27 October — positive mixed-eight counterpart WITHOUT resurrecting natural corners

The actual original AtlasRep D4 source 12D matrix projectors and six-trit
Lagrangian were already owned here. The prior result says the natural
geometric cube-corner eight set has no D4-equivariant quotient map from
the nonzero affine quotient80 because the source reflection fixes eight
nonzero vectors whereas that target mirror fixes zero corners.

A new constructive quotient on this SAME source D4 E⊕E chart chooses a
DIFFERENT target8: one size-four orbit with axis-reflection stabilizer and
one size-four orbit with diagonal-reflection stabilizer. Source quotient80
has four size-four orbits of each type plus six free size-eight orbits.
Map four source axis4 orbits and three free8 orbits to the axis target4;
map four diagonal4 and the other three free8 to the diagonal target4.
The point-stabilizer inclusion criterion makes every map well-defined
and D4-equivariant; target fibres have (4·4+3·8)/4=10 elements.

The source-owning consumer
`scripts/monster3b_atlas_d4_pointed720729_polarization_weld.py`
now verifies this mixed eight-site map *inside its already SHA-pinned
original ATLAS-generator workflow*. The parallel downstream #1250
consumer `scripts/monster_3b_pointed720729_mixed_d4_eight_ten_quotient.py`
constructs the 720=8·10·9 outer sheet plus central nine points.
Independent local E⊕E finite computation passed: every one of the 80
quotient vectors is assigned, all eight group words intertwine, eight
fibres each have ten elements, 720 outer D4 orbit partition
24·4+78·8=720, with class character (720,0,0,24,24).

***Scope firewalls:*** this target is NOT the source's old
`Base369Ternary27CornerEightExact` natural corner carrier. D4
action on the ten-sheet index is necessarily twisted/position-dependent
because the source contains free eight-point orbits. Original full
Heisenberg invariance still fails: 720 Schr translations move the
selected rank9 projector. No selected Monster 3B normalizer class
fusion, 6.Suz degree78 character, ζ-phase action or actual VOA
intertwiner is certified by this D4 SET-level construction.

**Attribution:** finite orbit/stabilizer principle is standard group
action theory. Source group/matrices are original ATLAS/AtlasRep;
this construction is a new DASHI explicit chosen chart and its checks.
See #1250 new source/proof ledger
`Docs/support/reference/Monster3B720729MixedD4EightTenBMW24MaxCut20261027.md`.
