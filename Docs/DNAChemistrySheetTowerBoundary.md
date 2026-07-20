# DNA chemistry sheet and tower boundary

## Why this correction exists

The existing DNA lane already contains useful and coherent objects:

- `Ontology.DNA.Supervoxel4Adic` owns the concrete `4 -> 16 -> 64 -> 256` nested DNA carrier;
- `Ontology.DNA.ChemistryUVCoordinates` owns the exact U/V coordinate bridge;
- `Ontology.DNA.ChemistryQuotient` owns the chemistry-visible quotient interface;
- `Ontology.DNA.ChemistrySheetHamiltonian` owns a signed U/V transition-and-coupling energy;
- the streaming, admissibility, eigenclass, and channel modules consume those surfaces.

The word **sheet** was nevertheless doing too much work. In the current implementation,
`SheetCoordinates n` is simply a pair of length-`n` signed U/V vectors. It has no scale
index, no projection operator, no expansion operator, no detail residual, and no exact
multiscale reconstruction law. It is therefore a base-coordinate field used by a chemistry
energy, not yet the general DASHI activation-sheet object.

## Four objects that must stay distinct

1. **Base coordinate pair**
   - one U value and one V value per base;
   - this is what `SheetCoordinates` currently implements.

2. **Coefficient sheet**
   - one coefficient per cell/block/node at a declared level;
   - its shape depends on the chosen tower semantics.

3. **Expanded detail field**
   - a coefficient sheet transported back into a common carrier for rendering,
     summation, or interaction.

4. **Scalar energy summary**
   - a norm, transition count, correlation score, or Hamiltonian contribution;
   - this is a functional of a sheet, not itself a sheet.

A heatmap can render any of the first three, but the image alone does not determine which
mathematical object was rendered.

## The 4-adic carrier is not automatically the sheet tower

`Supervoxel4Adic` constructs a fixed-height four-way nested product:

```text
DNA4 -> DNA16 -> DNA64 -> DNA256
```

This is a valid carrier hierarchy. It does not, by itself, declare the general sheet-growth
law, and it is not definitionally a tetration tower. In particular, the ragged lengths
`256, 64, 16, 4, 1` arise from ordinary block coarsening on a fixed 256-base carrier.
They cannot be used as evidence that the underlying DASHI sheet semantics are tetrational.

Conversely, this correction does **not** rule out a tetrational or recursively compositional
sheet formalism. It says that such a claim needs its own explicit level operator and
composition semantics instead of being inferred from the existing DNA block shapes.

## New typed boundary

`Ontology.DNA.ChemistrySheetTowerBoundary` adds:

- `CarrierGrowthLaw`, separating fixed four-way nesting, repeated exponentiation, and
  tetrational composition;
- `SheetRepresentation`, separating base coordinates, coefficient sheets, expanded detail
  fields, and scalar energy summaries;
- `MultiscaleSheetTower`, which requires:
  - a level carrier;
  - a declared growth law;
  - coefficient and expanded carriers at each level;
  - analysis, expansion, and detail maps;
  - a coarsest carrier;
  - an exact reconstruction theorem;
- `SheetHamiltonianSurface`, which types per-level, cross-level, and total energies without
  assuming that every chemistry contribution is quadratic;
- `ExistingChemistryCoordinateSurface`, which honestly packages the currently implemented
  U/V Hamiltonian while marking multiscale reconstruction and tetrational tower authority
  as absent;
- `SheetTowerPromotion`, which prevents a heatmap or ragged row lengths from self-promoting
  into tower semantics.

## Corrected reading of the present chemistry Hamiltonian

The existing `ChemistrySheetHamiltonian` remains useful. Its current theorem-bearing content
is:

- exact base-to-signed-U/V conversion;
- signed transition counts within U and V;
- signed cross-channel coupling counts;
- combination with strong-base, complement-span, reverse-complement-palindrome, and short
  hairpin counts.

The correct name for its input object is presently **base-indexed chemistry coordinates**.
A later module may lift these coordinates into genuine DASHI sheets and prove reconstruction,
Hamiltonian transport, and any tetrational/compositional relationship.

## Next theorem-bearing step

The next implementation should instantiate `MultiscaleSheetTower` using the repository's
actual DASHI lift semantics. That instance should specify:

1. what a level is;
2. how the next sheet is constructed;
3. whether the construction is block-nested, exponentiated, tetrational, or another recursive
   composition;
4. how coefficients expand to a common carrier;
5. how all details plus the terminal object reconstruct the original signal;
6. how the existing chemistry energy transports to that tower.

Until those witnesses exist, claims such as “the heatmap is the activation sheets,” “the
rows follow tetration,” or “chemistry acts exactly on these bands” remain candidate
interpretations rather than promoted theorem statements.
