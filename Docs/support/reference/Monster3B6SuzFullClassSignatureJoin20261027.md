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


## 23 November 2026 — source-owning OOM guard reconciliation

The original source-owning #1250 branch now mirrors the safe candidate filter already present in TOE #1217: all three AtlasRep/CTblLib candidate acceptance paths check `IsPermGroup(candidate)` **before** calling `Size(candidate)`; the downstream `SylowSubgroup(G,2)` is only entered with such an accepted group. The two dihedral-group checks use `not IsAbelian(...)` in GAP. Source commit: [d0c2e722](https://github.com/chboishabba/dashi_agda/commit/d0c2e7224a856674c8fb6de8e85dc160fd2c8975).

This prevents the previously identified unassisted 78-dimensional matrix-group Schreier–Sims route, but is **not** a blanket memory-safety theorem: constructing `AtlasGroup(info)` itself is still permitted before the representation guard, and no GAP execution of this exact commit was observed here. Failure to realize a suitable permutation model remains the documented `atlas-group-realization-residual`, not a successful actual D8 realization.

**Current P0 ordering:** (1) exact-head source GAP replay of both 6.Suz and the guarded five-orbit screen, with untouched raw receipt/version/hash; (2) all-conductor 210-class audit and source-selected 12/78 full-class join, including explicit C2/C3 phase and direct/dual Sym2 checks; (3) quotient-first subgroup construction in the **central double cover** 2.Suz.2, then Schur–Zassenhaus odd-kernel lift into N_M(3B) and intersection with the 17 serialized character-compatible worlds; (4) only then actual Hom/VOA selected same-object intertwiner and inverse-projective cocycle on the original carrier. The degree-1782 Suz.2 permutation representation alone does not specify the double-cover lift: an involution downstairs can lift to order four upstairs.

**Authority:** original ATLAS/AtlasRep and CTblLib inputs remain source owners; prior mathematics of Schur–Zassenhaus is classical; this branch patch is an engineering guard, not a newly discovered group-theoretic result. Earlier user-local 57/57 and 17-world PASS reports remain *reported* rather than independently executed in this update. GAP, Agda kernel and authentic 6.Suz source receipts are **not** claimed.


## 23 November 2026 — user-local source execution, four-class discriminator and kernel receipt

**Execution attribution:** The user's local GAP/CTblLib and Agda session reports the following completed evidence, independently from this GitHub source-reconciliation session. These outputs have not been re-executed from the newly committed GitHub branch here. Keep source-run evidence and exact-head verified repository receipts distinct.

| Existing pipeline | User-local reported outcome | Exact authority boundary |
| --- | --- | --- |
| `check_monster_3b_suzuki_main_quotient_match.sh` | PASS: class-20 quotient kernel; source 12 pair main positions [327,328] descends to MN3B χ146; selected 78 pair [253,254] descends to χ109, positive Monster restriction multiplicity | Character-table and quotient occurrence, not a Monster Hom action |
| `check_monster_3b_suzuki_actual_source_join.sh` | `SOURCE_RELATIVE_CHARACTER_JOIN_PASS`, all 210 classes via exact `CoeffsCyc` with full source signature and selected 12/78 rows | The join intentionally returns `original_source_authenticated=false` and `same_object_Monster_intertwiner_proved=false`; raw build JSON not attached to this commit |
| `monster3b_atlas_suz2b_monster_4class_source_fusion.g` | `UNIQUE_SOURCE_FUSION`; candidate central-double-cover `2.Suz.2` class 5 maps to Monster `4D` | Source-class constraint selection; the source JSON sets `literal_source_word_2Suz_class_individually_identified=false` |
| `monster3b_atlas_suz2b_monster_4class_receipt_validator.py` | PASS: conditional chain `4D -> 12F -> 6B`, predicted selected trace 66, nonfaithful 78 C2-positive branch | Conditional on same actual source word, chosen central generator, and phase / inversion lift; do not promote a selected same-object action |
| `run_agda29_parallel_check.sh` on generated `Monster3BSuzukiMainQuotientMatchCertificate.agda` | User-reported exit 0, (10/10) Checking, 0 holes / 0 postulates | Generated character/quotient certificate only; not a same-object Hom/VOA kernel proof |
| Monster Python regressions | 24/24 focused and 96/96 full Monster user-local PASS | Reported local working-tree state; exact pushed-head replay not independently observed |

**Live-source consumer repairs in #1250:** phase-parity checker assertion now iterates `all_sieved`, because `atlas_class_sieve()` returns class coordinates without `predicted_selected_phase_trace`; the separate 4-class receipt validator now calls `check_phase_parity(k)["atlas_source_rotation_to_z_rotation_12_to_z_halfturn_6"]` instead of `select_rotation_class(k)`. Both reuse the existing semantic calculation rather than duplicate it. Source commits [065445ad](https://github.com/chboishabba/dashi_agda/commit/065445ad0ee514c8e8222e717aac10cd7201eed3) and [67531140](https://github.com/chboishabba/dashi_agda/commit/6753114056e31e142ec9955e27bbfe7b97f31dee).

**Updated maximum-cut:** Original-source table/class-family discrimination is reported paid to the extent of the GAP receipts, including elimination of 4A/4C for the selected constraint family. Still **UNPAID**: proof that the particular 12D ATLAS D4 word maps to the unique class-5 double-cover row; explicit concrete `D8 <= N_M(3B)` subgroup word/relations and faithful central-cover lift; absolute `ζ3` versus `ζ3²` phase orientation on that original carrier; selected `Hom_E(H_ζ,W_ζ)` normalizer action and inverse-projective cocycle; and the physical TOE claim. The 17 character-compatible D4 fusions remain a *possibility screen*, not 17 realized subgroups.

**Next high-alpha cut:** bind source 12D AtlasRep `r,m` to exact 2.Suz.2 class-5 using an explicit subgroup/representation witness, carry its centre and class fusion through MN3B, intersect the 17 serialized worlds, then attach the selected actual Hom carrier. Retain the published original sources and distinct #1098/#1250 owners; no finite 720/729 chart coincidence counts as an action witness.


## 23 November 2026 — maximum-cut source D4 word / Suzuki centralizer / Monster 4D fusion weld

**Original donor #1098, not a newly invented D4:** `scripts/monster3b_atlas_actual_d4_word_witness.py` builds original ATLAS GF3 matrices C,D and word `r = m (g m g^-1)`, `m = (CDCDCDCDCDCdCd)^5`, `g = CdCdCDCd`. Its finite group equations establish `r² = -I12`, `m² = I12`, `mrm = r^-1`. Original donor `scripts/monster3b_atlas_source_d4_rotation_suz_2b_seven_centralizer.py` supplies **two actual generator words** `DcDCDcdC` and `CDCdCdCd` yielding order-seven matrices commuting with r. From published Suzuki 2A/2B centralizer orders 3317760 and 161280, respectively, this identifies r's Suzuki quotient involution as **2B**.

**New independent local arithmetic check:** using the original 12×12 ATLAS matrix entries already fetched from #1098, I recomputed the D4 relations, each order-seven witness and both commutators with exact integer arithmetic modulo 3. Both witnesses PASS. I also reconstructed the original MeatAxe plaintext files byte-for-byte from the fetched #1098 contents and verified both full SHA256 digests against the #1098 manifest (`ddd4919a…d35a031c2`, `433ba0f0…fcd15f`). This is a local exact GF3 and SHA256 replay, **not** a new GAP run, a group-generator intertwiner, or an Agda kernel proof. The earlier user-local full source join, 4D fusion and 96 Monster tests remain separately reported.

**Existing original #1250 source fusion:** `monster3b_atlas_suz2b_monster_4class_source_fusion.g` enumerates the relevant 2.Suz.2 order-four classes satisfying `r² = -I` and projection to Suzuki class 2B. In the reported authentic local CTblLib receipt there is exactly one such candidate: **2.Suz.2 class 5**, mapping through 6.Suz.2 -> main -> MN3B -> Monster **4D**. The corresponding conditional ATLAS class route is **4D / 12F / 6B**, predicted trace **66**, selected nonfaithful-78/C2-plus branch. This is materially stronger than merely saying a 4D possibility exists; it is a uniqueness-of-class consequence **under the original source quotient identifications**.

**New minimal source-owner consumer (committed to PR #1250):**
- `scripts/monster3b_atlas_d4_word_to_4class_source_weld.py` joins the PREEXISTING #1098 Suzuki-2B source-word JSON and the PREEXISTING #1250 exact GAP fusion JSON. It refuses missing D4/7-centralizer evidence, altered centralizer premises, multiple candidate classes, wrong class index/Monster class, and false Hom/phase promotion. It retains literal 2.Suz.2, 6.Suz.2, main, MN3B, Monster class positions and both supplied receipt hashes.
- `tests/test_monster3b_atlas_d4_word_to_4class_source_weld.py` contains 11 synthetic positive/negative contract cases.
- `scripts/check_monster3b_atlas_d4_word_4class_weld.sh <#1098-witness.json>` executes original #1250 GAP fusion/validator plus the thin consumer, never the 78-dimensional matrix group.
- The consumer's own status is **SOURCE_RELATIVE**, not authenticated original-source provenance or an Agda theorem. These new committed scripts/tests have not been run from this exact GitHub head here.

**Necessary source-identity qualification:** original #1098 generator matrices are labeled `2.Suz:2`; the CTblLib source chain contains `2.Suz.2` and the actual Monster normalizer's quotient/diagonal factors. No *explicit generator-by-generator isomorphism + selected-diagonal action* has yet been attached proving that these two named realizations share precisely the selected quotient coordinates. Therefore the conjunction `source-word Suzuki 2B + unique CTblLib class5` establishes a **conditional class recognition weld** under that alignment, not a fully demonstrated same-object Monster generator lift. Do NOT replace the published original exact quotient map by name-matching groups.

**Next P0 proof weld (no more generic character numerology):** source-generate the explicit 2.Suz:2 -> CTblLib 2.Suz.2 class/standard-generator alignment (or find a concrete faithful section in the original BW diagonal quotient), transport the exact ATLAS word r and reflection m, prove the resulting D8 fusion on one selected original N(3B) complement, and only then attach #1098 selected Hζ/Wζ/Hom action, central ζ vs ζ² orientation and cocycle. Class-based uniqueness and Schur–Zassenhaus ensure abstract existence/conjugacy, not original Monster element words.
