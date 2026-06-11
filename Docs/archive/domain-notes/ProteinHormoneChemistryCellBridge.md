# Protein Hormone Chemistry Cell Bridge

`DASHI.Biology.ProteinHormoneChemistryCellBridge` is a theorem-thin bridge
between the current chemistry right-limits gate and the bounded cell
differentiation / communication physiology bridge.

The Agda module stages the lane as:

1. chemistry right-limits receipt surface;
2. protein candidate observation;
3. hormone candidate observation;
4. receptor / cell-communication context;
5. bounded cell physiology receipt.

## Non-promotion guards

The only admissible route is
`boundedProteinHormoneCellObservationRoute`.  The following routes reduce to
the empty `Never` type:

- disease causation;
- full protein folding;
- cell-fate prediction;
- hormone-to-behaviour closure;
- chemistry-to-biology closure.

The canonical inhabitant is a toy receipt surface only.  It connects existing
canonical chemistry and cell-physiology witnesses, but does not add empirical
protein structure, hormone kinetics, disease mechanism, cell fate, behaviour,
or biology-closure evidence.

## Integration note

The lane is named in `DASHI.Interop.ObservationTransportSpine` as
`proteinHormoneChemistryCellDomain`, imported by `DASHI.Everything`, and
included in `DASHI.Interop.PhysicsChemistryBiologyDNAUnificationDischarge` as a
receipt-gated cross-scale observation surface.
