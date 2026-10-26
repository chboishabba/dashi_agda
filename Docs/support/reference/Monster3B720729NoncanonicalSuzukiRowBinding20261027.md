# 27 Oct 2026 — 720/729 D4 noncanonicity and actual 6.Suz source-row join

## Attribution and status

**Original mathematical sources:** ordinary finite (D_4) orbit–stabilizer theory and (G)-set homomorphisms (classical); Barraclough–Wilson (2007), *The Character Table of a Maximal Subgroup of the Monster*, DOI 10.1112/S1461157000001352; Breuer–Magaard–Wilson (reproducible 2024 source protocol, later publication), [original 3B quotient calculation](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/htm/ctblm.htm); [CTblLib's published (6.mathrm{Suz}) table head](https://www.math.rwth-aachen.de/homes/Thomas.Breuer/ctbllib/ctbltoc/data/6.Suz.html), group order **2690072985600**, **210** conjugacy classes; Gabriele Nebe (2025), DOI 10.1007/s10801-025-01399-2 for symmetric square of the faithful Suzuki 12. These are **different primary source roles**, not independent discoveries by this repo.

**Existing DASHI source owners:** PR #1098 original AtlasRep (2.mathrm{Suz}:2) D4 words, source GF(3) stable Lagrangian and (E\oplus E) 80-point quotient, Heisenberg equivariance and Hom/cocycle proof interfaces; PR #1250 original mixed-eight `monster_3b_pointed720729_mixed_d4_eight_ten_quotient.py` and original main→MN3B→Monster (6.mathrm{Suz}) character matcher. The pre-existing pointed 720+9 cardinality identities and Ibrahim class-20 quotient/phase proof owners are reused, not newly claimed.

**Three distinct evidence levels:** the 80-point (D_4) combinatorics below are exact, independently executed with local Python. The source (6.mathrm{Suz}) main-character certificate *schema* was updated and code committed, but **not executed with genuine GAP/CTblLib source data**. The full Monster 3B selected constituent, 729 lift, Hom action and Agda proof are therefore not claimed.

## The finite positive theorem and a NEW noncanonicity barrier

The already source-audited (D_4) quotient action is `E⊕E` on (mathbb F_3^4). Its 80 nonzero vectors form:
- **four** axis-reflection stabilizer four-point orbits (A_4);
- **four** diagonal-reflection stabilizer four-point orbits (D_4^′);
- **six** free eight-point orbits (R_8).

The already constructed alternative eight-site target is **mixed**, (Y=A_4\sqcup D_4^′). It is not the natural geometric cube-corner action (the latter fails the already-owned reflection fixed-point test).

For an orbit (D_4/H), a (D_4)-equivariant map to (Y) is determined by a target point fixed by (H). An exact orbit-stabilizer enumeration gives:

| Source orbit | Hom to axis (A_4) | Hom to diagonal (D_4^′) |
| --- | ---: | ---: |
| axis four-orbit | 2 | 0 |
| diagonal four-orbit | 0 | 2 |
| free eight-orbit | 4 | 4 |

The number of **all** equivariant maps (X_{80}\to Y_8) is therefore (2^8\cdot8^6=67,108,864). For exactly **ten inverse images of every one of the eight target sites**, the four axis source four-orbits contribute 4 points per axis target site and each free eight-orbit assigned to axis contributes another 2. Hence exactly three of the six free orbits must map to each target type, and the number of balanced maps is

\[
\boxed{\binom63\,2^8\,4^6=20,971,520.}
\]

This was verified two ways: a direct independent `D_4` stabilizer census and a dynamic generating-function recursion over all 14 source orbits. A fixed choice of target labels yields this many different maps. Target (D_4)-equivariant automorphisms have order (2\times2=4), and they act freely on surjective maps, leaving **5,242,880** balanced maps modulo target-equivariant relabelling. No claim is made that these are inequivalent after *all source* automorphisms; this number only quotients target renamings.

**Mathematical significance:** a balanced eight-by-ten quotient **exists** but is **massively noncanonical**. The original source ATLAS (D_4) module plus the requirement (|f^{-1}(y)|=10) cannot select a unique map or a literal Monster source-coordinate intertwiner. Selection requires additional actual source words/phase/extension or another explicit invariant.

### Corrected twist argument

The ten-sheet twist is already forced on **(X_{80})**: the source has six free eight-point orbits while (Y_8\times\mathrm{Fin}_{10}) with trivially acted sheets has **only four-point** orbits. Therefore no equivariant bijection of the 80-point source to that untwisted product exists. The previous source-script comment based *only* on eight-orbits of the later 720-point product (X_{80}\times\mathbb F_3^2) was inadequate: a product of two four-point (D_4) orbits with distinct reflection stabilizers can itself have size-eight orbits. The assertion about the ten-sheet twist survives, but for the correct, stronger **quotient80** reason.

**Implementation:** extended original `scripts/monster_3b_pointed720729_mixed_d4_eight_ten_quotient.py` to independently count all/balanced maps, target automorphisms and the correct quotient80 twist obstruction, and added `scripts/test_monster_3b_mixed_eight_noncanonicity.py`. An independently executed local standard-library Python counter counts all maps and exhaustively checks **640** point–group equivariance incidences for one balanced map.

## Separate improvement: same-table identity for actual selected Suzuki 78

The existing `scripts/monster_3b_suzuki_main_quotient_match.g` reports selected degree12/78 **ATLAS string labels**. The source character-export script independently reports `source_irreducible_position_1_based` per row. Strings plus a table identifier and two central class positions are not enough to defend against accidentally joining stale/class-reordered character exports.

The original source-GAP producer now emits `six_suz_group_order=2690072985600`, `six_suz_class_count=210`, `six_suz_degree12_positions`, and `six_suz_degree78_positions`, guarded against the current published CTblLib table head. Its **existing** canonical Python validator, rendered Agda certificate and shell checker require them. The **existing** `scripts/monster_3b_suzuki_selected_character_join.py` now cross-checks these source positions against the exact `source_irreducible_position_1_based` values from the all-conductor export, additionally checking original group order/class count and unique, disjoint source character positions. No duplicate character computation or generic (6.mathrm{Suz}) representation machinery was introduced.

The synthetic join regression `scripts/test_monster_3b_suzuki_selected_character_join.py` now includes **18** fail-closed negative cases (six new cases explicitly target stale 12 or 78 positions, group-order/class-count changes, duplicated and missing character positions). These are synthetic API/contract tests, not claims that the 6.Suz source table was executed. Source code was committed, but the exact checked-out GitHub bytes were not executed in this container.

## Pareto/Ibrahim stop conditions

1. **Paid original:** 3B diagonal quotient class **20** not 19, from Barraclough–Wilson's table and Breuer–Magaard–Wilson's later computational protocol (shared Wilson lineage). Do **not** re-open it as unproved.
2. **Paid finite mathematical consumer:** constructive mixed-eight (80\to8\) quotient, 720+9 address, exact noncanonicity and no trivial-ten-sheet action at quotient80. Do not turn this into *canonical* 6.Suz/Monster coordinates.
3. **Still open source-character receipt:** the unique selected (6.mathrm{Suz}) degree78 full character, source main→MN3B→Monster quotient, actual ATLAS row positions and classwise `Sym²(12)`/dual identification. The updated selector/export/join will reject mismatched source row positions.
4. **Still open same-object action:** selected 729 inertia extension and Schur/Hom/normalizer cocycle in PR #1098, not a newly postulated 90-permutation module. The 720/729 quotient does not commute with the entire Heisenberg operator group.
5. **Source trust and physical claims:** a source page proves what its authors computed and published, not an observed run in this container. Similar dimensions, ζ notation, analytic zeta, quantum observer claims, or phase analogies are not Monster representation equalities.

**Local independent receipt:** `/mnt/data/monster3b_720729_balanced_map_count_receipt.json`. **Local independent executable source:** `/mnt/data/monster3b_720729_equivariant_map_count.py`. No GAP, Agda, literal actual Atlas generator run, or Monster intertwiner receipt in this turn.

## Stronger full-720 negative control: why size-eight orbits alone do not suffice

An independent finite computation constructs **the same mixed-eight target** and the same inner (\mathbb F_3^2) action, but an actually trivial D4 action on ten sheet labels. Its (720=8\cdot10\cdot9) points have:
```text
untwisted 720: 60 four-orbits + 60 eight-orbits = 240 + 480
source twisted: 24 four-orbits + 78 eight-orbits =  96 + 624
```
Both contain free size-eight D4 orbits, so the earlier implication "any outer720 free-eight orbit forces twisted sheets" is invalid. The **complete orbit character/census** distinguishes the actions, and the even cheaper quotient80 argument already proves the nontrivial-sheet requirement because source80 has six eight-orbits but target Mixed8 times ten *trivial* sheets has only four-orbits. The new census assertion is embedded in the EXISTING source owner `scripts/monster_3b_pointed720729_mixed_d4_eight_ten_quotient.py` and in its focused regression `scripts/test_monster_3b_mixed_eight_noncanonicity.py`; the negative model was also computed independently with local Python.

This is a clarification of the exact finite D4 representation, **not** a claim about true Heisenberg invariance, an actual Monster subgroup word, or the sourced degree78 selection.
