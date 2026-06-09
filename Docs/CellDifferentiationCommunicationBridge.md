# Cell Differentiation Communication Bridge

`DASHI.Biology.CellDifferentiationCommunicationBridge` is a bounded
physiology observation surface for cell differentiation, cell communication,
metabolism, circulation, endocrine signalling, and immune signalling.

The Agda module stages the route as:

1. observation of an organism, tissue, and cell population;
2. candidate lineage, communication, metabolic, circulatory, endocrine, and
   immune state extraction;
3. integration into a candidate physiology state;
4. observation and provenance gates backed by a receipt;
5. promoted bounded physiology meaning.

## Non-promotion guards

The module explicitly names these guards as typed constructors:

- `NoDiseaseCausationClaim`
- `NoFullDevelopmentRecovery`
- `NoCellFatePredictionClaim`
- `NoBiologyClosureClaim`

The only admissible route is `boundedObservationReceiptRoute`. Disease
causation, full development recovery, cell fate prediction, and biology closure
routes reduce to the empty `Never` type.

The module now also carries canonical toy inhabitants for the observation,
candidate, receipt, bounded meaning, and guard-certificate surfaces.  These
inhabitants demonstrate type-level coverage only; they are not empirical
biology receipts.

## Integration note

This file is imported by `DASHI.Biology.BioAnimalexicStackDischarge` and the
aggregate `DASHI.Everything` surface.
