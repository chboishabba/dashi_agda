# Monster 3B / 6.Suz: portable exact full-class character audit (25 October 2026)

## Purpose and Pareto cut

The **actual selected Monster 3B 78** and its `6.Suz` source character remain the highest-value outstanding SAME-OBJECT question. The existing authors' tables and DASHI GAP scripts are already available. This cut **does not** construct a new Suzuki group, Monster action, Heisenberg representation, D4 geometry or Fourier field. It separates three independent operations:

1. **Source acquisition**: CTblLib plus the ORIGINAL Barraclough–Wilson `N3BetcTables.tar.gz` archive and the published `main -> MN3B` quotient map.
2. **Source-selected occurrence**: pre-existing `scripts/monster_3b_suzuki_main_quotient_match.g` enumerates all degree156 outer fused pairs restricting to two degree78 irreducibles, then checks the degree1458 product, degree113724 constituents, quotient descent, and positive restricted-Monster character occurrence. Source choice is NOT equated to faithfulness.
3. **Independent character-identity audit**: the new pure-Python consumer checks the entire selected full class function against `Sym²(12)` and its contragredient. Matching dimension, central involution, central C3 scalar, or cyclotomic norm alone is explicitly insufficient. This independent comparison is possible without GAP *once exact source class-value rows have been supplied*.

This is a reproducibility and evidence-boundary improvement: **not** an execution of the source Monster character data or the missing normalizer intertwiner.

## Original scholarship and source custody

- **R. W. Barraclough and R. A. Wilson**, *The Character Table of a Maximal Subgroup of the Monster*, LMS J. Comput. Math. **10** (2007), 161–175, DOI [10.1112/S1461157000001352](https://doi.org/10.1112/S1461157000001352), especially **§5.1**. The source mathematically distinguishes splitting and fused outer pairs and allows **any irreducible `6.Suz` character** in the 729-inertia tensor. It must NOT be rewritten as a source claim that only faithful 78s occur.
- [**Barraclough and Wilson's original computational archive**](https://www.rwb.me.uk/table/index.html), `N3BetcTables.tar.gz`: original `3^1+12:6.Suz.2` (main), `3^1+12.2.Suz.2` (Monster (N(3B))) and `3^12.6.Suz.2` table/fusion contents. The archive contains mappings that might not be present in all current CTblLib installations; it has not been downloaded or locally executed in this turn.
- **Gabriele Nebe**, *Symmetrizations of quadratic and Hermitian forms*, J. Algebraic Combinatorics **61** (2025), article 29, DOI [10.1007/s10801-025-01399-2](https://doi.org/10.1007/s10801-025-01399-2), **§6**: source irreducible degree78 symmetric square of a faithful degree12 `6.Suz` module, descending to `3.Suz`. Source proof of this representation's existence does NOT select its occurrence in the Monster.
- **GAP Reference Manual §18.1-10**, [`CoeffsCyc`](https://gap-system.github.io/gap/doc/ref/chap18.html). The documented external cyclotomic coefficient representation is converted to the `(1,ζ)` field basis with **exact** formula `(a,b)=(c1-c3,c2-c3)` because `ζ²=-1-ζ`. No floating point, no `str(E(...))` evaluation, no modified source data. If a required class value lies outside Q(ζ3), the exporter aborts, not an assertion that the value is zero.

Prior DASHI proof ownership stays with `IbrahimMonster3B*` exact quotient/phase and main-family receipts, Moonshine original Heisenberg/Schur/Weyl/Stone–von Neumann owners, [PR #1098](https://github.com/chboishabba/dashi_agda/pull/1098) for proof-relevant Hom/normalizer/cocycle, and [PR #1148](https://github.com/chboishabba/dashi_agda/pull/1148) for the separate geometric JFine/D4 finite model.

## New implementation: exact portable independent check

Producer **`scripts/monster_3b_suzuki_portable_character_export.g`** writes full `6.Suz` degree12 faithful and ALL degree78 rows in the form

```json
{
  "table_id": "6.Suz",
  "group_order": 1,
  "class_sizes": [1],
  "class_orders": [1],
  "power_map_2_zero_based": [0],
  "central_c2_zero_based": 0,
  "central_c3_zero_based": 0,
  "degree12": [
    {"label":"12a", "values":[["12","0"]]}
  ],
  "degree78": [
    {"label":"78a", "values":[["78","0"]]}
  ]
}
```

**The block above describes the schema only; its short lists and integers are placeholders, NOT an actual source table, and are not a valid input** (the actual table has many classes, must include genuine C2 and C3 class positions, and must satisfy the total source group order). Do not copy it as a witness.

Consumer **`scripts/monster_3b_suzuki_portable_character_checker.py`** independently:

- reconstructs every Q(ζ3) value as a pair of exact `Fraction` coefficients;
- checks the entire **zero-based** class-square map, including the exact squared-element order rule;
- for `table_id="6.Suz"`, **requires** the full conjugacy-class sizes and group order, their exact sum, and central classes of size one;
- checks that the supplied 12/78 rows are pairwise **irreducible and orthogonal**, using exact source class-size weighted inner products;
- computes on **every conjugacy class** `(chi12(g)^2+chi12(g^2))/2`, and the Galois-conjugated dual;
- reports complete matches and the **first differing class and exact source/predicted values** for every nonmatch;
- **never** authenticates provenance just because an input claims `table_id="6.Suz"`, never infers a Monster quotient or explicit normalizer intertwiner, and never reports a GAP execution.

Both files deliberately fail closed when full classes, central positions, source irreducibility, or field membership are unavailable. They are additional consumers, not replacements for the original Monster same-object matcher.

### Commands

```sh
# Local, GAP-free regression:
python scripts/test_monster_3b_suzuki_portable_character_checker.py

# When the original CTblLib source and Barraclough/Wilson quotient
# installation are available (not executed here):
mkdir -p build
gap -q scripts/monster_3b_suzuki_portable_character_export.g
python scripts/monster_3b_suzuki_portable_character_checker.py \
  build/monster_3b_suzuki_portable_source_characters.json \
  --out build/monster_3b_suzuki_portable_character_check.json

# Actual selected Monster family remains a separate original GAP computation:
gap -q scripts/monster_3b_suzuki_main_quotient_match.g
```

The exporter and both-source group sections are source-written **without an observed GAP run**. A successful full `6.Suz` character equality still does not independently pay the **Monster occurrence** or the **full normalizer cocycle**.

## Independently observed local Python results

On a genuine `C2×C3` character-family example (six conjugacy classes), the `12\rightarrow\operatorname{Sym}^2(12)=78` row and its **dual** were accepted by the exact character checker; the modified noncharacter row failed on an explicit witness class. The test also rejected **eight** malformed/export-forgery cases (including missing/invalid source class sizes and order) and independently passed character inner-product arithmetic on genuine one-dimensional representations.

Execution in this session:

```text
python -m py_compile portable_suzuki_character_checker.py portable_character_selftest.py : PASS
python portable_character_selftest.py : PASS
    6 actual group classes
    2 correct matching character rows (direct and dual)
    8 negative controls
    first differing class reported for incorrect row
python portable_suzuki_character_checker.py portable_character_fixture.json ... : PASS
```

The validated current-turn local artifacts are:
- `/mnt/data/monster3b_maxcut/portable_character_selftest_receipt.json`
- `/mnt/data/monster3b_maxcut/portable_character_local_receipt.json`
- `/mnt/data/monster3b_maxcut/portable_character_verified_manifest.json`

The manifest hashes the **locally executed standalone scripts**. Those local script hashes must NOT be claimed to hash identical GitHub byte content: the repository versions contain more provenance documentation. Source-generated output fields `table_provenance_authenticated=false` and `no_GAP_execution_claim=true` intentionally prevent this evidence laundering.

## Remaining irreversible evidence cut / Pareto frontier

1. **Source 78 selection**, not mathematical existence: obtain source original-table matching output selecting *one* actual faithful/nonfaithful degree78 family by full product, quotient and Monster occurrence.
2. **Independent full-character check**: use portable exported `6.Suz` rows and verify exact `Sym²`/dual row identity. This can eliminate the 12→78 hypothesis even when centre signatures agree. If the source rows use a larger cyclotomic field, report that and use the original GAP full-character comparator; do not approximate.
3. **Same-object normalizer action**: source 729 extension phase/parity, central `C3` diagonal quotient, full `6.Suz` linear action, cocycle and source-coordinate Hom. **Existing PR #1098** owns this formal interface. Do not promote matching characters into a verified intertwiner before the actual source-selected action is fixed.
4. **Physical/other claims**: no Riemann zeta zeros, quantum-observer mechanism or device inference follows from cyclotomic and Monster finite representation calculations.

**Status:** pure Python full-character algorithm and finite controls verified; source archive, GAP/CTblLib source export, Agda kernel, selected Monster 78 and actual normalizer intertwiner **not observed**.
