# Monster 3B projector/core continuation

## Status

This continuation is stacked on the exact CTblLib/Heisenberg work in PR #464. It replaces several separate numerical probes by one division-free theorem, distinguishes the canonical regular `C3` core from the dyadic refinement, places the conformal line in the invariant sector, and constructs a finite `729 x 90` projector-index model without dense `65610 x 65610` matrices.

It does **not** claim that the finite model has already been identified with the actual Monster `ζ` eigenspace. The extraspecial-kernel embedding, actual `χζ` projector, inertia character, and `12 + 78` branching remain explicit certificate inputs.

## Centred probes

For weights `w=(w0,w1,w2)` and multiplicities `m=(b+δ,b,b)`, the new theorem proves over exact rationals

```text
3 (w · m)
  = (w0+w1+w2) aug(m)
    + δ (3 w0 - (w0+w1+w2)).
```

The displayed `123`, `321`, and `369` identities are instances. Every real positional probe therefore detects the same one-dimensional invariant-sector defect.

## Canonical versus dyadic core

The multiplicity vector has the canonical decomposition

```text
(65663,65610,65610)
  = 65610 (1,1,1) + (53,0,0).
```

The dyadic refinement is separately recorded:

```text
(65663,65610,65610)
  = 65536 (1,1,1) + (127,74,74).
```

Thus `65610` is the maximal regular `C3` core, while `65536` is a selected power-of-two refinement. The branch explicitly keeps

```text
dyadicCoreCanonicallySelectedByMonsterAction = false
```

until a genuine intertwining or geometric selection theorem is supplied.

The equal nontrivial eigenspaces retain the exchange symmetry `ζ ↔ ζ²`; the distinguished invariant defect reduces the coordinate-permutation pattern from a uniform three-way symmetry to the stabilizer of the two equal nontrivial sectors.

## Conformal line

The exact sector arithmetic is

```text
(65664,65610,65610)
  = (1,0,0) + (65663,65610,65610).
```

The standard VOA fact that automorphisms fix the conformal vector is recorded as imported provenance from Frenkel--Lepowsky--Meurman, not as a newly proved Monster theorem. This makes the `54 -> 53` transition representation-shaped while preserving the source boundary.

## Finite projector model

The model basis is

```text
X × Fin 90,
X = F3^6,
|X| = 729.
```

Translation acts on `X` and leaves the multiplicity coordinate fixed. The evaluation map between translated multiplicity labels and model basis vectors has constructive left and right inverses and is translation-equivariant. Exact arithmetic proves

```text
729 * 90 = 65610.
```

This realizes the desired finite index mechanism without constructing a dense matrix. The actual Monster-sector identification remains false/open.

## Projector trace interface

For an actual certified abelian class embedding, the multiplicity character is to be computed by the finite weighted trace formula

```text
χ_S(g)
  = normalization * Σ_a χζ(a)^(-1) χ_W(ga).
```

The implementation proves the finite sum/append algebra and records the exact certificate fields needed for:

```text
certifiedAClassEmbedding
inertiaStabilizesChiZeta
multiplicityCharacterTable
multiplicityInnerProductsIntegral
multiplicityCharacterEqualsTwelvePlusSeventyEight
```

No guessed normalizer matrices are introduced.

## Remaining highest-alpha theorem

The next irreducible step is to connect the certified `MN3B` restriction to the actual extraspecial kernel `E ≅ 3^(1+12)` and certify either:

```text
χ_{Wζ|E}(g) = 0 for g outside Z(E),
χ_{Wζ|E}(z^k) = 65610 ζ^k,
```

or the equivalent translated-projector resolution. Only after that identification may the finite `729 x 90` model be promoted to

```text
Wζ|E ≅ Hζ ⊗ Sζ,
dim Sζ = 90.
```

The later `Sζ ≅ 12 ⊕ 78` claim remains a character-inner-product computation, not a dimension factorization.

## Validation

```bash
bash scripts/check_monster_3b_projector_core_round2.sh
```

The checker cascades through the PR #464 checker, rejects holes and trust escapes in the new sources, checks all exact constants and authority boundaries, and invokes the cumulative Agda root when Agda is available.
