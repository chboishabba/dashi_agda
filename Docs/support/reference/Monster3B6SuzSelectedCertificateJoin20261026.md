# 26 October 2026 — Monster 3B / 6.Suz: exact selected-source certificate JOIN

## Why this cut dominates more geometric modelling

The prior code has two independently useful but unjoined certificate routes:

- The **actual-source Monster selector**, `scripts/monster_3b_suzuki_main_quotient_match.g` and `render_monster_3b_suzuki_main_quotient_match.py`, tests the original Barraclough–Wilson main, quotient, and Monster restriction tables and outputs a **specific pair of Atlas-labelled degree-78 constituents** after a unique full-character occurrence. This original GAP computation has not been observed executed locally.
- The **backend-free ordinary character checker**, `scripts/monster_3b_suzuki_all_conductors_character_audit.py` and exporter, recomputes **all-class** 6.Suz direct/dual Sym² character functions across the natural cyclotomic conductors and checks exact weighted irreducible orthogonality. It deliberately does **not** identify a Monster constituent.

A mere set of two favorable booleans can refer to different 78 characters, different centre-C3 generator orientation, or even a different export revision. Consequently neither receipt is a sufficient **same-object** input to the normalizer Hom compiler until their labels and central class metadata match.

## Implemented interface

`scripts/monster_3b_suzuki_selected_character_join.py` consumes BOTH **raw files**:
```sh
python scripts/monster_3b_suzuki_selected_character_join.py \
 build/monster_3b_suzuki_all_conductors_characters.json \
 build/monster_3b_suzuki_main_quotient_match.json \
 --out build/monster_3b_suzuki_selected_join.json
```

Its first operation is **RECOMPUTATION** of the full class-character audit and original full quotient-receipt schema check through the existing, imported source owners—not accepting externally supplied success booleans. It then requires:

1. Source table identifier `6.Suz` in BOTH original file objects; all original source class sizes/group order and exact character orthogonality supplied and tested.
2. The *same* one-based central C2/C3 class IDs emitted by the main selector as the zero-based IDs in the portable full-character export.
3. Exactly the same two degree12 ATLAS labels, and the selected two degree78 labels present among all exported source degree78 irreducibles. No sorting/relabelling is used to invent orientation.
4. Exact cyclotomic centre-C3 scalar rows for both degrees, using the already-owned `Cyc` arithmetic. Their selected two-by-two central-phase equality count must be the same number independently printed by the Monster selection receipt. A trivial centre-C3 eigenspace label `0` means unity phase, *not* scalar zero.
5. The actual selected source degree78 central involution scalar on each of the paired rows, consistent across both outer-conjugate halves; both faithful12 rows have C2 scalar −12; derived combined selected degree90 trace must equal the source receipt (−90 or +66).
6. Selected faithfulness true is impossible if either the central C2 scalar is +1 or the centre-C3 character is trivial.
7. FULL direct and dual Sym²(12) all-class comparison counts must match the original source-selected receipt, including whether the **complete** Nebe family is matched. C2 or C3 coincidence alone never promotes to this theorem.
8. SHA-256 fingerprints of the exact PROVIDED full-class and Monster-selected receipt bytes, without claiming that the files originated with their purported authors or a GAP run.

This reconciles the historical C2 faithful/nonfaithful and C3 ζ/ζ²/phase0 diagnostics **to one chosen source pair** before the selected-729 normalizer Hom work. The consumer sets `original_source_authenticated=false`, `GAP_executed_by_this_check=false` and `same_object_Monster_intertwiner_proved=false`; passing cannot erase this boundary.

## Independent local verification

`scripts/test_monster_3b_suzuki_selected_character_join.py` is an explicit **synthetic** interface test, with fake all-class audit/selected schemas. It cannot and does not recreate 6.Suz data or impersonate an observed GAP execution. A locally executed mathematically equivalent standalone test passed:

- both coherent *synthetic* degree78 central-C2 branches (−90 faithful, +66 nonfaithful);
- **12 negative controls**: wrong table; both central-class swaps; stale 12 or 78 labels; wrong common-C3 count; contradicted selected C2 trace/faithfulness; stale direct-Sym² count; false full-family equality; non-scalar 78 centre; inconsistent paired 78 signs;
- Python bytecode compilation.

**Receipt:** `/mnt/data/monster3b_maxcut/new/selected_join_synthetic_receipt.json`. Exact GitHub file bytes, the real imported upstream all-conductor audit, the original quotient validator, source 6.Suz data, GAP and Agda were **NOT** executed together in the present session. Local equivalent test does not claim any of those.

## Latest-PR snowball, avoid duplicate owners

| PR | Source-relevant gain | Explicit proof boundary |
|---|---|---|
| [#1098](https://github.com/chboishabba/dashi_agda/pull/1098) | Actual Schur/Heisenberg character transport, source Atlas 12D symplectic generators and `Hom_E(Hζ,Wζ)` cocycle owner. New Atlas word order checks rule out careless order-6 substitution for D4 mirror. Ambient order4/Frobenius mirror construction is useful but NOT certified as actual Suzuki or Monster subgroup. | Join receipt does not instantiate a literal selected lift/group word. |
| [#1105](https://github.com/chboishabba/dashi_agda/pull/1105) | Concrete selected GF729 primitive order728 operator and field conjugacy. | Underlying field chart not automatically the Monster-selected normalizer. |
| [#1239](https://github.com/chboishabba/dashi_agda/pull/1239) | Rational-conductor exact Fourier sector projector, optional root-free finite-field computation. | C27 VOA charge data are not 6.Suz character rows. |
| [#1250](https://github.com/chboishabba/dashi_agda/pull/1250) | Full D4/53 pointed-source obstruction with negative A1 multiplicity −19 and H4-incompatible signed repair. | Stop generating extra signed pointed models until actual E/Monster quotient action is paid. |
| [#1260](https://github.com/chboishabba/dashi_agda/pull/1260) | Eisenstein λ⁹ mod 3^9 finite torsion / C3 transfer, existing three-phase source owners. | This is characteristic-three / nilpotent transfer, NOT semisimple ordinary complex Suzuki character theory. Do not identify operators. |

## Original attribution and evidence hierarchy

- **Original mathematical authors:** R. W. Barraclough and R. A. Wilson (2007), *The Character Table of a Maximal Subgroup of the Monster*, DOI 10.1112/S1461157000001352, and [original source table archive](https://www.rwb.me.uk/table/index.html). Their §5.1 permits any Suzuki irreducible and distinguishes fused-pair inertia rows; it does not prescribe our earlier faithful78 filter.
- **Original symmetric-square result:** Gabriele Nebe (2025), *Symmetrizations of quadratic and Hermitian forms*, DOI 10.1007/s10801-025-01399-2. Irreducible degree78 Sym²(12) exists and descends to 3.Suz; that does not independently show occurrence in the Monster.
- **Original character theory:** Serre and standard symmetric-square/projector identities; GAP CTblLib/ATLAS own their character tables and actual class values; GAP documents `Conductor`/`CoeffsCyc` (Chapter 18). The current join's schema/tests are **repository-derived tools**, not original group-theory discoveries.
- Preserve original `IbrahimMonster3B*` attribution and source-vs-code-vs-proof status. Repeated copy of one original table is not independent corroboration.

## Pareto frontier

**P0 (complete this round):** build and local-test the source-relative character join; no new Heisenberg, GF729, C3 or (D_4) engine.

**P1 (external source receipt):** run the original Barraclough–Wilson/CTblLib main→MN3B→Monster source matcher and exact full 6.Suz character-row exporter, feed their **raw** outputs to this join, and establish a unique selected degree78 pair or an explicit fail-closed ambiguity. These source outputs were unavailable here. A valid receipt is the only safe gate for selected source-character identification.

**P2 (existing proof owner):** hand that specific pair, central class and full-character witness into [#1098](https://github.com/chboishabba/dashi_agda/pull/1098)'s actual group action and Hom_E cocycle; separately typecheck its Agda/Lean code. Neither a local Python agreement nor an Agda `Set` field is such a proof.

**No physical promotion:** finite complex character identities do not imply a Riemann-zeta zero, teleportation/observer intervention, or spacetime mechanism.
