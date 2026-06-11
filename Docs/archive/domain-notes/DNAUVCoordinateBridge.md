# DNA U/V Coordinate Bridge

## Scope

This note lands one bounded companion to the initial DNA supervoxel lane:
an explicit `U/V` coordinate surface that makes the chemistry-facing map easier
to reuse in Agda.

Files added in this pass:

- [`Ontology/DNA/ChemistryUVCoordinates.agda`](../Ontology/DNA/ChemistryUVCoordinates.agda)

## Why this exists

The existing DNA lane already had:

- a raw DNA `4 -> 16 -> 64 -> 256` carrier,
- a chemistry quotient interface on `DNA256`,
- and one concrete admissibility screen.

What was still implicit is the role of the `U/V` chemistry features themselves.
The chat material treated them as chemistry-visible coordinates:

- `U`: weak/strong,
- `V`: pyrimidine/purine.

That can sound like a lossy quotient. In the current DNA alphabet it is not.
The pair `(U, V)` determines the base exactly:

- `(weak, purine) = A`
- `(weak, pyrimidine) = T`
- `(strong, purine) = G`
- `(strong, pyrimidine) = C`

So this new module makes a useful distinction explicit:

- chemistry may still *use* `U/V` as a quotient-style coordinate system,
- but the coordinate pair itself is a complete base code for `A/C/G/T`.

## What the new module formalizes

`ChemistryUVCoordinates.agda` adds:

- a length-indexed `UVCoordinates` record,
- `encodeUV` from base sequences into `U/V` coordinates,
- `decodeUV` back into bases,
- proofs that `decodeUV (encodeUV xs) ≡ xs`,
- a `feature256` bridge into the existing `ChemistryFeature` record,
- a `featureSection256` theorem showing that decoding and re-encoding a
  coordinate packet preserves the chemistry feature exactly,
- and `pullbackAdmissible`, which lifts any sequence-level Boolean screen onto
  `U/V` coordinates by decoding first.

## Why the pullback matters

The concrete chemistry module currently keeps admissibility at the raw-sequence
level:

- immediate-repeat exclusion,
- immediate complement exclusion,
- span-2 complement exclusion,
- short reverse-complement and hairpin screens,
- short GC-balance screens.

The new coordinate bridge gives an honest way to reuse those screens without
claiming a new theorem:

1. keep the admissibility law stated on bases,
2. pull it back to `U/V` coordinates with `pullbackAdmissible`,
3. use `pullbackAdmissible-section` to show that the pulled-back predicate
   agrees with the original one on encoded sequences.

This keeps the current architecture clean:

- `Supervoxel4Adic.agda` owns the raw carrier,
- `ChemistryQuotient.agda` owns the quotient interface,
- `ChemistryConcrete.agda` owns the first concrete chemistry screen,
- `ChemistryUVCoordinates.agda` now owns the coordinate bridge between those
  layers.

## Boundary

This still does **not** add:

- a richer thermodynamic model,
- longer-window admissibility theorems,
- a codec to external DNA text formats,
- or any physics-closure integration.

It is intentionally a small bridge module so the DNA lane has a clean local
place for the chemistry-coordinate story before further admissibility work is
added.
