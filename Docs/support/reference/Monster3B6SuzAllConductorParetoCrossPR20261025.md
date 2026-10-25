# Monster 3B / 6.Suz: all-conductor exact character audit and latest-PR Pareto
**Date:** 2026-10-25. **Implementation:** [PR #1250](https://github.com/chboishabba/dashi_agda/pull/1250).

## Attribution / precise evidence ladder

**Original mathematical scholarship (not authored by DASHI):** R. W. Barraclough and R. A. Wilson, *The Character Table of a Maximal Subgroup of the Monster*, LMS J. Comput. Math. 10 (2007), 161–175, DOI 10.1112/S1461157000001352: historical 3B inertia, 6.Suz.2 main character table, diagonal quotient/class fusions, and §5.1 fused nontrivial degree729 source. Gabriele Nebe, *Symmetrizations of quadratic and Hermitian forms* (2025), DOI 10.1007/s10801-025-01399-2 §6: actual irreducible degree78 symmetric square of 6.Suz degree12, descending to 3.Suz. Ordinary finite character/symmetric-square identities are classical, e.g. Serre. **Authoritative source computational repository** is Barraclough–Wilson's original [N3B tables and fusion archive](https://www.rwb.me.uk/table/index.html). GAP CTblLib / ATLAS character values are table data. Publishing copies, cited OEIS series, and web summaries do not create additional independent source roots.

**Current repositories, distinct original DASHI authorship:** [#1098](https://github.com/chboishabba/dashi_agda/pull/1098) owns `Hom_E(H_zeta,W_zeta)`, actual source-selected linear FDRep and normalizer/cocycle; [#1105](https://github.com/chboishabba/dashi_agda/pull/1105) owns an exact **chosen** GF(729) primitive field model from Atlas 12D symplectic compression; [#1148](https://github.com/chboishabba/dashi_agda/pull/1148) owns standalone finite D4 eight-trit (not a Monster action); [#1239](https://github.com/chboishabba/dashi_agda/pull/1239) owns rational-conductor C27 projector constructions; [#1250](https://github.com/chboishabba/dashi_agda/pull/1250) owns source/quotient 6.Suz selected78 comparisons, D4 no-go and signed geometry negative controls. The earlier #1250 full D4/53 residual no-go has negative invariant multiplicity **-19** under its strong factorization premises; its signed fix does **not** commute with unchanged H4 regular action. Do NOT resurrect the pointed summand based only on a phase/dimension match.

## New high-value portability fix

The first portable checker on #1250 used only `Q(zeta3)` coordinates and the associated GAP source-exporter called `CoeffsCyc(x,3)`. That route is a valid **restricted fast path**, but requiring *all* ordinary 6.Suz 12 and 78 class values to lie in Q(zeta3) is an **unsupported field assumption**. The actual CTblLib row contains original cyclotomic values `x` whose conductors must be tested, not guessed. GAP documents `Conductor(x)` and `CoeffsCyc(x,n)`; using a too-small nonmultiple conductor returns `fail`. (GAP Reference Manual, Chapter 18.)

**Implemented additive portable route (retains the first checker):**

1. `scripts/monster_3b_suzuki_all_conductors_export.g` requests `n=Conductor(x)` **per class value**, and `CoeffsCyc(x,n)`. It verifies that the source value equals `sum_j coeff_j E(n)^j` exactly and emits each value as `{"conductor":n,"coefficients":[... exact rational strings ...]}`. No floating point or speculative field selection. The original source class order, sizes, full 2-power map, centre C2/C3 positions, character family labels and degrees are retained. **Not GAP-executed here.**
2. `scripts/monster_3b_suzuki_all_conductors_character_audit.py` implements an exact **standard-library** polynomial quotient `Q[x]/(Phi_n(x))`, building `Phi_n` by exact monic division of `x^n-1` by earlier cyclotomic factors. It embeds two different source-value conductors into their common LCM before multiplication, conjugation, Sym² `[chi(g)^2+chi(g²)]/2` and dual comparisons. All equality is rational/exact.
3. The Python consumer independently checks group class-order and second-power consistency, centre class orders and singleton sizes, source character identity/degree, **exact class-size-weighted irreducible orthogonality** whenever source class sizes are supplied, and every degree12/78 *full class function* comparison. It supplies exact **first divergent class witness** for negative comparisons.
4. Explicit fail-closed `MAX_CONDUCTOR=4096` guard: if a source value **or the conductor of a required common embedding** exceeds 4096, the comparison rejects rather than approximating. This is a **computational bound**, not a mathematical no-go; increase with resource budgeting or use the existing GAP in-source full-character comparator when source field complexity exceeds the bound.
5. Character-table data passed with `table_id="6.Suz"` must include full group order/class sizes and pass exact orthogonality. The program explicitly reports `source_provenance_authenticated=false`, `Monster_78_selected=false`, `GAP_or_Agda_executed=false`. A filename or editable table header is never an original-source proof.

### Genuine local mathematical tests

In `/mnt/data`, the independently executed equivalent local Python reference was type/syntax compiled and tested with:
- `Phi_n` exact degrees for **all 120 conductors 1..120**, using Euler totient counts.
- Exact root-conductor embedding/conjugation in conductors 3,5,7,11,15,21, and multiple other powers.
- **All 30 elements of the genuine finite group C2 × C3 × C5**, with class values of *mixed conductors* (1/3/5/15/30), direct Sym² degree78 and dual comparisons, and a specific modified-character class rejected.
- **465 exact pairwise orthogonality checks** of the genuine group's 30 distinct irreducible degree-one characters.
- **7 fail-closed malformed input cases** (the committed regression adds an eighth disjoint negative control). The toy degree12/78 rows used for positive Sym² comparison are direct sums of characters, not irreducible characters of C2×C3×C5; the source orthogonality gate is accordingly not applied to those *synthetic* high-degree rows.
- The **exact committed GitHub byte versions** and actual GAP/CTblLib/Agda/kernel **were NOT executed** by this local test. The local reference is mathematically equivalent in test scope but is separately hashed. Do not launder a local receipt as a repository-head or source table execution result.

Local receipt: `/mnt/data/monster3b_maxcut/general_cyclotomic_local_receipt.json`; independent local hash manifest: `/mnt/data/monster3b_maxcut/general_cyclotomic_manifest.json`. This is exact finite-character arithmetic, not a measurement or original Monster table computation.

### Commands for a runnable checkout with the published source table

```bash
python scripts/test_monster_3b_suzuki_all_conductors_character_audit.py

# Not executed in this environment:
mkdir -p build
gap -q scripts/monster_3b_suzuki_all_conductors_export.g
python scripts/monster_3b_suzuki_all_conductors_character_audit.py \
 build/monster_3b_suzuki_all_conductors_characters.json \
 --out build/monster_3b_suzuki_all_conductors_audit.json

# Actual Monster source-selected 78 family still requires:
gap -q scripts/monster_3b_suzuki_main_quotient_match.g
```

The first two commands audit the full **6.Suz** character identity only. The original matching script must independently establish the *Monster-selected 78 family* through the Barraclough–Wilson 1458/156 main constituents, exact (N(3B)) quotient descent and positive restricted Monster character occurrence. Even agreement of exact 6.Suz full characters does **not** provide an actual Monster basis (T) or its full normalizer cocycle. These last proof interfaces already exist in PR #1098; preserve source ownership, don't add a duplicate Heisenberg compiler.

## Pareto / snowball / Ibrahim decisions

1. **P0 source-current:** Run the source-selected original main→MN3B→Monster class matcher. Fail on zero/multiple selected degree78 pairs, missing quotient maps, or unverified source table. Record class labels and orientation as OUTPUT, not assumptions. No amount of synthetic pure Python can replace original missing 6.Suz class values.
2. **P1 reusable backend-free verification:** Once source class rows exist, independently verify exact classwise Sym²/dual, irreducibility via class-size weighted orthogonality, central C2/C3 and original matched degree78 labels. Use all-conductors consumer for values beyond Q(zeta3); if conductor bound exceeded, stop or do an exact explicitly justified higher-field run.
3. **P2 same-object:** Route source-selected group words, character equalities and actual (729×(12+78)) quotient to original Ibrahim / PR #1098 FDRep–Hom/Schur and cocycle theorem owners; distinguish proof-relevant terms from `Set`-valued pseudo-proof fields.
4. **P3 explicit GF729 coordinate weld:** If selected actual 729 lift fixes the required F3^6 symplectic source, import PR #1105's concrete primitive field selector and symplectic intertwiner. Do not assume the field structure follows from a 729-cardinality equality.
5. **Stop** exploring new D4/53 signed-pointed repairs unless their source H4 action, whole Monster character and same-object quotient weld are paid; #1250 already gives one mathematically specific no-go.
6. **No physics promotion:** arbitrary cyclotomic representation identities are neither Riemann-zeta zeros nor quantum observer effects, signal mechanisms or physical experiments.

**Proof status:** finite local arithmetic PASS; new source code COMMITTED; no authentic GAP/CTblLib source export, Agda kernel typecheck, Monster selected 78 family or full normalizer intertwiner observed.
