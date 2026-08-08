# Monster 3B normalizer restriction and structural dashboards

This lane replaces decorative dimension plots with reproducible character-table and finite-Heisenberg computations.

## Exact external computation

With GAP and CTblLib installed:

```bash
mkdir -p build
gap -q scripts/monster_3b_normalizer_restriction.g
```

The script loads:

```gap
CharacterTable("M")
CharacterTable("MN3B")
```

selects the unique Monster irreducible of degree `196883`, restricts it through the stored MN3B-to-M class fusion, decomposes the result by scalar products with `Irr(mn3b)`, and rejects any result whose constituent contributions do not reconstruct `196883`.

The numeric certificate is written to:

```text
build/monster_3b_normalizer_restriction.json
```

No constituent is assigned a `12`, `78`, `90`, `3^6`, or other semantic label merely from its degree.  Such names require ownership from CTblLib/ATLAS metadata or an independently checked representation construction.

## Structural visualization suite

Run:

```bash
python scripts/monster_3b_structural_dashboard.py
```

When the GAP JSON exists, the suite also generates a one-cell-per-dimension restriction sheet coloured by the actual MN3B irreducible position.  Without the JSON, that figure is omitted.

The always-available figures are mathematical function plots rather than magnitude bars:

1. **Extraspecial quadratic-refinement sheet** — compares two quadratic refinements through phase kernels derived from their polarizations.
2. **Generator-to-invariant dashboard** — maps each standard generator of `F_3^6` to its symplectic pairing, character phase and quadratic increment over all 729 states.
3. **Heisenberg–Weyl phase portrait** — plots all `729 × 729` phases `arg(zeta^{<b,x>})`.
4. **Heisenberg times `12 + 78` sheet** — displays the full `729 × 90 = 65610` carrier with the additive multiplicity boundary retained.
5. **Orbit-length sheet** — reindexes `F_3^6` as `F_3^3 × F_3^3` and plots orbit lengths under an explicit affine symplectic-model generator.

The first, second, third and fifth plots are canonical finite-field or explicit-model computations.  The fourth uses the documented dimensional split `90 = 12 + 78` but its displayed coupling function remains a model until an actual MN3B matrix representation is supplied.

## Checked Agda boundary

`DASHI/Moonshine/Monster3BNormalizerBridge.agda` proves the exact arithmetic:

```text
729 × 12 = 8748
729 × 78 = 56862
729 × (12 + 78) = 65610
65663 + 65610 + 65610 = 196883
65610 + 53 = 65663
```

It separately records that:

- the actual restriction is an external GAP/CTblLib computation until certified;
- no explicit characteristic-zero Monster basis is currently imported;
- the candidate tensor interpretation is not silently promoted to an MN3B-module equivalence.

## Interpretation discipline

The central `3B` element is scalar on each nonlinear central-character sector, so it selects `zeta` versus `zeta^2` but does not generate internal interference geometry.  Rich patterns must come from translations, modulations, Weil-type transformations, Suzuki-side operators, orbit structure, or genuine matrix coefficients of other normalizer generators.
