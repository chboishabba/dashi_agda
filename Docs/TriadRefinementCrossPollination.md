# Triad refinement cross-pollination

This note records the additional bridges attached to the current saturated Hecke
refinement lane.

## 1. MDL-governed promotion

`Ontology/Hecke/DirectedCorrelationMDLPromotion.agda` turns the invariant ladder
into a promotion problem rather than an unrestricted feature-expansion problem:

1. flat histogram,
2. ordered triad histogram,
3. symmetric sector correlation,
4. directed 3×3 sector interaction.

A richer level is admissible only when:

- the preceding level is exhausted on the relevant current scope,
- the target carries a pair-specific separation obligation,
- the target's total model-plus-residual description length is no worse.

The fixed structural costs are bookkeeping defaults for the current finite
carrier. They are not claimed to be an optimal universal code. This imports the
existing MDL/ZKP discipline into the Hecke lane: heuristics may propose richer
summaries, but promotion must be receipt-bearing and pay for complexity.

## 2. Triad × five-class SSP carrier

`Ontology/Hecke/TriadFiveSSPCoordinateBridge.agda` makes the candidate

```text
15 = 3 × 5
```

surface fully explicit. It defines:

- three existing triadic sectors,
- five local symmetry-class slots,
- fifteen row-major coordinates,
- an explicit reversible labeling by the existing fifteen-element `SSP` carrier.

The two round-trip proofs establish a finite carrier equivalence for that chosen
labeling. They do **not** establish:

- a canonical Monster action,
- a Monster representation,
- moonshine compatibility,
- a physical interpretation of the ordering,
- or that the five classes are the actual orbit quotient discovered by the
  long-compute histogram lane.

Those stronger claims are collected in `MonsterInterpretationObligation`; the
record deliberately has no inhabitant in this module.

## 3. Indexing on the existing FRACTRAN carrier

`DASHI/Combinatorics/TriadFiveFractranIndex.agda` connects the new finite carrier
to the repo's existing concrete FRACTRAN state instead of inventing a parallel
15-register machine.

The existing `FractranCOL.EV5` is a five-lane prime-exponent vector. Therefore the
structure-preserving index is:

```text
TriadFractranState = EV5(sector0) × EV5(sector1) × EV5(sector2)
```

and one `TriadFiveCoordinate` is read as:

```text
sector     -> choose the EV5 bank
localClass -> choose lane 0..4 inside that existing EV5
```

This preserves the proposed `3 × 5` structure explicitly. It also provides an
`SSP`-labelled view through the reversible coordinate map, with the theorem
`coordinateExponent-via-ssp` showing that reading by SSP label is exactly reading
by the underlying triad-five coordinate.

The module additionally states two stronger boundaries:

- `TriadFiveFractranCatalogueIndex` requires an outcome-sound classifier and
  representative under the existing `FractranCOL.run` semantics;
- `TriadFiveFractranDynamicBridge` requires an actual lifted transition law,
  preservation of the promoted Hecke invariant, and an MDL promotion receipt.

Neither is inhabited automatically. A coordinate label is not yet a proof that two
FRACTRAN computations are equivalent, and three EV5 banks are not yet a derived
15-coordinate FRACTRAN dynamics.

## 4. Why these bridges belong together

The directed correlation surface supplies a candidate separator. MDL determines
whether that separator earns promotion. The `TriadFiveCoordinate` carrier gives a
finite coordinate system in which a later representation-theoretic action could
be stated. The FRACTRAN adapter then indexes those coordinates on existing
prime-exponent state machinery. The flow is therefore:

```text
computed sector data
  -> directed invariant candidate
  -> MDL/promotion receipt
  -> finite 3×5 coordinate carrier
  -> three-bank EV5 FRACTRAN index
  -> outcome-sound catalogue / dynamic bridge obligations
  -> optional group-action obligations
```

This keeps the Monster-facing layer downstream of the measured and promoted
Hecke invariant rather than using Monster numerology to choose the invariant in
advance. It also keeps FRACTRAN semantics downstream of explicit encoding and
simulation obligations rather than treating a shared prime label as computational
identity.

## 5. Immediate discharge order

1. Focus-check the MDL-promotion, triad-five, and FRACTRAN-index modules.
2. Compute the three predicted current pairs sector-by-sector.
3. If local histograms collapse, compute the symmetric and then directed
   correlations.
4. Construct a `PromotionReceipt` only for a level that separates and pays its
   MDL cost.
5. Populate `TriadFractranState` from the promoted invariant and state the actual
   lifted transition law.
6. Construct a `TriadFiveFractranCatalogueIndex` only when representative
   soundness and key completeness are proved under `FractranCOL.run`.
7. Test whether the resulting separated fibres admit a natural five-class
   quotient. Only then attempt to inhabit `MonsterInterpretationObligation`.
