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
