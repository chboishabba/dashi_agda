# Triad refinement cross-pollination

This note records the two additional bridges attached to the current saturated
Hecke refinement lane.

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

## 3. Why these bridges belong together

The directed correlation surface supplies a candidate separator. MDL determines
whether that separator earns promotion. The `TriadFiveCoordinate` carrier gives a
finite coordinate system in which a later representation-theoretic action could
be stated. The flow is therefore:

```text
computed sector data
  -> directed invariant candidate
  -> MDL/promotion receipt
  -> finite 3×5 coordinate carrier
  -> optional group-action obligations
```

This keeps the Monster-facing layer downstream of the measured and promoted
Hecke invariant rather than using Monster numerology to choose the invariant in
advance.

## 4. Immediate discharge order

1. Focus-check the directed-correlation and predicted-sector modules.
2. Compute the three predicted current pairs sector-by-sector.
3. If local histograms collapse, compute the symmetric and then directed
   correlations.
4. Construct a `PromotionReceipt` only for a level that separates and pays its
   MDL cost.
5. Test whether the resulting separated fibres admit a natural five-class
   quotient. Only then attempt to inhabit `MonsterInterpretationObligation`.
