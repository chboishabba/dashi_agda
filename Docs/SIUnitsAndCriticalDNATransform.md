# SI units and critically sampled DNA transform

## Scope

This tranche closes two boundaries left after the chemistry-sheet codec work:

1. the former sheet tower reconstructed by retaining the complete leaf sequence;
2. the thermodynamic tables carried conventional units in field names but not in their Agda types.

## Critically sampled four-way transform

`Ontology.DNA.CriticallySampledDNA4Transform` gives the four DNA bases an exact cyclic four-state relative-coordinate structure.

Each four-base block

```text
(a, b, c, d)
```

is represented as

```text
(anchor = a,
 delta(a,b), delta(a,c), delta(a,d)).
```

The synthesis map applies each delta back to the anchor. The four-block round-trip is machine-stated and exhaustive over the four-state carrier.

The construction is recursively packaged for the existing `DNA16`, `DNA64`, and `DNA256` nested carriers. Its coefficient inventory is

```text
1 + 3 + 12 + 48 + 192 = 256
```

four-state symbols. Unlike the prior redundant tower, the coefficient record contains no retained `FlatDNA256` leaf copy.

This establishes critical sampling and local exact reconstruction. The focused compiler gate is intended to expose any remaining proof-normalisation work needed for the explicit `DNA16`/`DNA64`/`DNA256` round-trip theorems.

The transform is invertible and block-local. It is not promoted as Euclidean-orthogonal: the natural algebra here is the finite four-state difference group. An orthogonality theorem would require a declared scalar embedding and inner product.

## Type-indexed SI system

`DASHI.Physics.Units.SI` defines dimensions by the seven SI base exponents:

```text
length, mass, time, current, temperature, amount, luminous intensity.
```

It includes:

- all seven SI base units;
- the named coherent derived units from hertz through katal;
- molar energy, molar entropy, and molar concentration;
- decimal fixed-point scales;
- quantities indexed by both dimension and scale;
- measurements carrying uncertainty, source, version, and unit.

A quantity of molar entropy therefore cannot be used where a molar-energy quantity is required merely because their numeric representations coincide.

`DASHI.Physics.Units.SIMetrologyBridge` connects this concrete representation to the repository's existing metrology authority boundary and keeps dimensional validity distinct from measurement precision and model authority.

## SantaLucia conversion

`Ontology.DNA.SantaLucia1998SI` transports the sourced conventional table exactly:

```text
0.1 kcal mol^-1       = 4184 decijoule mol^-1
0.1 cal mol^-1 K^-1  = 4184 × 10^-4 joule mol^-1 K^-1
0.01 kcal mol^-1      = 4184 centijoule mol^-1
```

The conversion uses integer fixed-point arithmetic. No floating-point rounding is introduced.

## Boundaries

- SI dimensional typing does not establish empirical accuracy; source, version, uncertainty, and calibration remain separate.
- The DNA transform is critically sampled and reversible as a finite group transform, but is not yet an orthogonal chemistry-energy decomposition.
- Celsius interval/absolute-temperature semantics, affine temperature conversion, logarithmic units, and uncertainty propagation remain specialized follow-on modules rather than being hidden inside the core quantity carrier.
