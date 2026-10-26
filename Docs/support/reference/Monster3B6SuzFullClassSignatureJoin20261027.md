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

## Follow-on P0: JSON labels and reproducible source driver

A fresh review confirmed an existing source-format blocker: GAP's ATLAS `AtlasLabelsOfIrreducibles` can contain backslashes; a raw label such as `\\chi_{1,0}` is invalid in a hand-written JSON string (`\\c` is not a JSON escape). This was already identified in a prior PR review; do not claim to have discovered the ATLAS phenomenon.

- Added `scripts/monster_3b_source_json_escape.g`, a shared printable-ASCII, fail-closed JSON-string quoting helper using existing GAP string replacement, with **no extra GAP package dependency**. It refuses unsupported control/non-ASCII bytes instead of corrupting labels.
- Reused it in the **three existing original source producers**: the original main quotient matcher, arbitrary-conductor exporter, and older Q(zeta3) portable exporter. Character labels remain the original ATLAS strings after decoding JSON.
- Added **thin orchestration only** in `scripts/check_monster_3b_suzuki_actual_source_join.sh`. It invokes the pre-existing original quotient shell checker, source all-conductor exporter and auditor, and strict selected-source join, preserving the raw files under `build/`.
- An independent local Python synthetic reconstruction verified all eight additional class-signature negative controls plus five JSON quote/backslash round trips. This does **NOT** mean the committed GAP script, the committed updated Python integration, or real CTblLib exports ran locally.
- The distinguishing branch is decisive: if the source-restricted selected 78 is **not** the Nebe Sym² family, a passing join should be reported as a rigorous *negative* against that selected-constituent hypothesis, not promoted to the conjectured 12+78 intertwiner.

## 27 October second-order strengthening: bind the **full selected characters**, not just the table head

The previous improvement still left a genuine source-coordinate hole: different conjugacy classes can have identical element order, class size and square-map behaviour. Therefore even equality of *all* 210 metadata triples between two table exports cannot mathematically prove equality of their character-column orders.

An **independently executed exact finite counterexample** uses the actual abelian group `C2 × C2 × C3`. Fix the identity, a chosen involution `(1,0,0)`, and a chosen central order-three element `(0,0,1)`. Swapping `(0,1,0)` and `(1,1,0)` preserves the *entire* group class-order, class-size and square-power-map arrays, plus these central class positions. A genuine 1-dimensional character
`χ(a,b,c)=(-1)^(a+b) ζ^c` nevertheless changes its character values on the swapped classes. Thus the metadata-only join is not a complete class-coordinate integrity gate.

The existing source consumer path now adds a strictly stronger obligation without inventing a new character algorithm:

1. `scripts/monster_3b_source_json_escape.g` exports individual original GAP cyclotomic values **exactly** using `Conductor`, `CoeffsCyc` and algebraic reconstruction; no approximation to `Q(ζ₃)`.
2. The original GAP `monster_3b_suzuki_main_quotient_match.g` emits **the full 210-class values** of both actual selected degree-12 and both actual selected degree-78 `Irr(six)` rows alongside the earlier group metadata, ATLAS labels and original main→MN3B→Monster receipt.
3. `render_monster_3b_suzuki_main_quotient_match.py` validates two complete selected rows of each degree and their exact value-record structure.
4. `monster_3b_suzuki_selected_character_join.py` compares **all 4 × 210 values exactly**, via its already-owning `Cyc.wire`, against the independent all-conductor export *after* matching source `Irr` indices and central C2/C3.
5. The original synthetic regression gains six additional fail-closed cases covering source/exported noncentral character drift, omitted degree12 rows, and a truncated selected degree78 row; total **32** specified negatives before the version gate. The thin execution driver asserts `selected_source_characters_all_classes_matched=true`.

The **independent** small-group model was executed locally and produced `/mnt/data/monster3b_exact_class_metadata_collision_receipt_20261027.json`. The newly committed exact `6.Suz` GAP source and 32-case GitHub test were **not executed here**: do not relabel a local equivalent mathematics test as an actual CTblLib/Monster receipt. A future successful source join still needs original author/source-provenance attestation and the #1098 actual normalizer Hom action, not merely successful arithmetic.

**Mathematical limit:** four selected rows need not distinguish every conjugacy class of `6.Suz`. The new check establishes equality of those selected rows *as exported by the two producers* on a common class ordering. A globally simultaneous reindexing of the original source tables is still outside this local join's detection without independently fixed source coordinates. Actual GAP table version and source input identities must be retained.

## Explicit GAP/CTblLib runtime-version binding

The two original GAP producers now each record `GAPInfo.Version` and `GAPInfo.PackagesLoaded.ctbllib[2]` in their raw JSON receipts. The existing main-receipt validator accepts only nonempty string versions; the existing source-relative join rejects mismatched GAP or CTblLib revisions across the independently produced records, and includes the matched versions in its output. The synthetic adversarial suite adds **four** revision-drift controls, bringing the specified negative cases to **36**.

This is version *consistency*, not software-binary authentication: locally altered tables or two different builds with the same version string are not ruled out, and the exact CTblLib/GAP computation was not executed in this environment. The version field location is documented by GAP's own `GAPInfo.PackagesLoaded.ctbllib[2]` usage. The external original source protocol and its dated computational lineage are retained.

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
