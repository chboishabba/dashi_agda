# 27 October 2026 — Monster 3B / 6.Suz: fail-closed full-class coordinate join

## Scope and prior ownership

This is a narrow **source-relative certificate-integrity cut**, NOT a new Heisenberg, D4, GF729, Schur, finite-character, or Monster action construction.

Original sources, not repository discoveries:

- R. W. Barraclough and R. A. Wilson, *The Character Table of a Maximal Subgroup of the Monster*, LMS J. Comput. Math. **10** (2007), 161–175, DOI **10.1112/S1461157000001352**, plus [authors' actual table and fusion archive](https://www.rwb.me.uk/table/index.html).
- Thomas Breuer, Kay Magaard, and Robert A. Wilson, *Some steps in the verification of the ordinary character table of the Monster group*, [published reproducible computational protocol](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/htm/ctblm.htm); published Journal of Algebra **703** (2026), 452–463, DOI **10.1016/j.jalgebra.2025.09.034**. This has shared Wilson/table lineage: do not count a reused original source twice as independent evidence.
- Gabriele Nebe, *Symmetrizations of quadratic and hermitian forms*, 2025, DOI **10.1007/s10801-025-01399-2**, degree-78 Suzuki symmetric-square result. It does not by itself identify the Monster-selected constituent.
- CTblLib/GAP/ATLAS own original 6.Suz group, class, power-map and character data. The generic group-representation tools are classic, not original here.

Repository proof ownership remains in original `IbrahimMonster3B*` modules, PR [#1098](https://github.com/chboishabba/dashi_agda/pull/1098) for actual \(H_\zeta,W_\zeta,\operatorname{Hom}_E\), and this PR [#1250](https://github.com/chboishabba/dashi_agda/pull/1250) for source producer/export/validation/interface.

## Newly identified gap

Previously the selected-character join checked: table identifier, total group order, number of classes, central C2/C3 class indices, two source degree-12 and two selected degree-78 *Irr* positions and names, classwise exported Sym²/dual comparisons, and Monster/quotient evidence flags.

Those constraints **do not detect a stale permutation of other class coordinates** when the name/order/count/centres/Irr positions are unchanged. It is unsafe to promote a same-named row into a same-coordinate source character without comparing the full conjugacy-class indexing.

## Minimal repair in original owners, not a duplicate framework

1. **Original selected GAP producer** `scripts/monster_3b_suzuki_main_quotient_match.g` now also writes `six_suz_class_orders`, `six_suz_class_sizes`, `six_suz_power_map_2_zero_based` for the actual chosen `CharacterTable("6.Suz")`. Indices and data come directly from GAP, not a hardcoded guess.
2. **Original Python selected receipt validator** `scripts/render_monster_3b_suzuki_main_quotient_match.py` checks exact array lengths against the source 210 classes, integer types (rejecting Python booleans), identity positions, total class size = group order, square-map index range and order law \(\operatorname{ord}(g^2)=\operatorname{ord}(g)/\gcd(\operatorname{ord}(g),2)\), and central C2/C3 square/size constraints. The result now retains the three arrays.
3. **Original source-selected certificate join** `scripts/monster_3b_suzuki_selected_character_join.py` requires all three arrays to agree, element by element, with the already-exported `class_orders`, `class_sizes`, `power_map_2_zero_based` of the all-conductor source audit. The join reports `complete_source_class_signature_matched=true` and a SHA-256 of the **provided source-signature object** for reproducible comparison, not source authentication.
4. **Existing synthetic regression** `scripts/test_monster_3b_suzuki_selected_character_join.py` now has **26 specified negative inputs** instead of 18, adding both-sided perturbations of noncentral orders, sizes, square maps, missing metadata, and boolean-as-int poisoning. Its two coherent branches are also required to return the new hash and gate.

The class signature is a necessary *alignment discriminator*, **not a proof of unique class labels**: automorphisms or swaps of indistinguishable class-metadata rows can preserve order/size/power maps. Character values, exact source table identity, and the original quotient and Monster restriction computations must still be connected. The independent full-character export and selected-source receipt are **not authenticated by a self-reported field or a hash**.

## Source-versus-execution boundary

- **Committed code:** yes, to PR #1250, source-written at a new head.
- **Original GAP exporter and Monster quotient matcher executed against CTblLib here:** **NO**.
- **The updated exact checkout of both Python validators and synthetic regression executed locally here:** **NO** unless a separate exact-head runner receipt is attached.
- **Verified absolute phase orientation or concrete Monster normalizer lift/intertwiner:** **NO**.
- **Agda/Lean kernel-checked same-object theorem at this head:** **NO**.
- **Formal and computational value of the change:** any valid join must now pass the additional full class-metadata checks, closing a concrete stale-class-coordinate acceptance pathway.

The original [author archive](https://www.rwb.me.uk/table/index.html) explicitly records the main table, N(3B) quotient, and extra quotient/fusion maps; cite those rather than silently substituting class positions from an unrelated table revision.

## Pareto / snowball / Ibrahim roadmap

| Stage | State after this cut | Minimum next payment |
| --- | --- | --- |
| P0: existing 720/729 and mixed-eight D4 / GF729 finite work | Already exists; mixed quotient noncanonical | No new geometric 90-permutation story |
| P1: original 6.Suz character and Monster quotient receipts | Producer, exporter, strict validator and cross-receipt join written; **actual run absent** | Execute both original GAP inputs at one CTblLib revision, retain untouched raw JSON and provenance, execute actual all-conductor audit and source-selected join |
| P2: same-object selected 12/78 family | Selection algorithm and equality predicate written; actual selected full receipt absent | Exactly one selected family from main→MN3B→Monster, full class equality or explicit non-equality, phase and C2 labels |
| P3: actual 729 inertia lift and Hom normalizer cocycle | Generic theory exists in #1098; instance open | Attach same actual \(H_\zeta,W_\zeta\) carrier/actions and selected-phase character; prove cocycle/representation compatibility |
| P4: kernel / end-to-end | Pending | Run the correct exact-head Agda/Lean targets; keep provenance and source-written/code-executed/kernel-verified levels separate |

**Stop rule:** Do not infer a literal Monster action, unique eight-site chart, scalar `Fin90` basis acting as a representation, physical spin/optics, or quantum mechanism from the counts \(720+9=729\), \(12+78=90\), or a passing source-relative checksum. The remaining issue is actual selected-source *same-object* evidence, not shortage of generic construction machinery.
