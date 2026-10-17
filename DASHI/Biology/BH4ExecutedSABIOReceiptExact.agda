module DASHI.Biology.BH4ExecutedSABIOReceiptExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Executed SABIO-RK export-API acquisition + schema-aware parameter recount,
-- 2026-10-17.
--
-- Live schema-v3 run:
--   16 proteins requested/completed
--   11 proteins with >=1 export row
--   190 kinetic-law entries
--   932 explicit parameter objects under the current export schema
--   0 acquisition errors
--
-- Per-protein entry counts:
--   TPH2 75; PAH 44; TPH1 33; MTOR 13; PTS 6; SPR 6; GCH1 4;
--   QDPR 4; TH 2; AGMO 2; TSC2 1.
--   GCHFR, PCBD1, NOS1, NOS2, NOS3: zero rows in this exact export query.
--
-- The earlier kinetic_parameter_count = 0 was a parser-schema miss. The
-- schema-aware rerun paid 932 parameter objects; that count is acquisition
-- metadata, not a claim that all 932 are scientifically usable flux bounds.
------------------------------------------------------------------------

record ExecutedSABIOReceipt : Set where
  constructor executed-sabio-receipt
  field
    proteinsRequested : Nat
    proteinsCompleted : Nat
    proteinsWithEntries : Nat
    kineticEntryCount : Nat
    kineticParameterCount : Nat
    acquisitionErrorCount : Nat
    proteinsWithEntryCounts : List String
    proteinsWithoutEntries : List String
    exportAcquisitionExecuted : Bool
    parameterSchemaRecountRequired : Bool

open ExecutedSABIOReceipt public

canonicalExecutedSABIOReceipt : ExecutedSABIOReceipt
canonicalExecutedSABIOReceipt =
  executed-sabio-receipt
    16
    16
    11
    190
    932
    0
    ( "TPH2:Q8IWU9:75"
    ∷ "PAH:P00439:44"
    ∷ "TPH1:P17752:33"
    ∷ "MTOR:P42345:13"
    ∷ "PTS:Q03393:6"
    ∷ "SPR:P35270:6"
    ∷ "GCH1:P30793:4"
    ∷ "QDPR:P09417:4"
    ∷ "TH:P07101:2"
    ∷ "AGMO:Q6ZNB7:2"
    ∷ "TSC2:P49815:1"
    ∷ [] )
    ( "GCHFR:P30047"
    ∷ "PCBD1:P61457"
    ∷ "NOS1:P29475"
    ∷ "NOS2:P35228"
    ∷ "NOS3:P29474"
    ∷ [] )
    true
    false

executedSABIOProteinsRequested : Nat
executedSABIOProteinsRequested = proteinsRequested canonicalExecutedSABIOReceipt

executedSABIOProteinsCompleted : Nat
executedSABIOProteinsCompleted = proteinsCompleted canonicalExecutedSABIOReceipt

executedSABIOProteinsWithEntries : Nat
executedSABIOProteinsWithEntries = proteinsWithEntries canonicalExecutedSABIOReceipt

executedSABIOKineticEntryCount : Nat
executedSABIOKineticEntryCount = kineticEntryCount canonicalExecutedSABIOReceipt

executedSABIOKineticParameterCount : Nat
executedSABIOKineticParameterCount = kineticParameterCount canonicalExecutedSABIOReceipt

executedSABIOAcquisitionErrorCount : Nat
executedSABIOAcquisitionErrorCount = acquisitionErrorCount canonicalExecutedSABIOReceipt

executedSABIOEntriesExact : executedSABIOKineticEntryCount ≡ 190
executedSABIOEntriesExact = refl

executedSABIOParametersExact : executedSABIOKineticParameterCount ≡ 932
executedSABIOParametersExact = refl

executedSABIOCoverageExact : executedSABIOProteinsWithEntries ≡ 11
executedSABIOCoverageExact = refl

record ExecutedSABIOBoundary : Set where
  constructor executed-sabio-boundary
  field
    exportRowCreatesInVivoFluxBound : Bool
    exportRowCreatesInVivoFluxBoundIsFalse : exportRowCreatesInVivoFluxBound ≡ false
    parameterObjectCreatesInVivoFluxBound : Bool
    parameterObjectCreatesInVivoFluxBoundIsFalse : parameterObjectCreatesInVivoFluxBound ≡ false
    exportRowCreatesSameCompartmentState : Bool
    exportRowCreatesSameCompartmentStateIsFalse : exportRowCreatesSameCompartmentState ≡ false
    zeroPreRepairParameterCountMeansNoKineticParameters : Bool
    zeroPreRepairParameterCountMeansNoKineticParametersIsFalse :
      zeroPreRepairParameterCountMeansNoKineticParameters ≡ false
    zeroProteinRowsMeansProteinHasNoKinetics : Bool
    zeroProteinRowsMeansProteinHasNoKineticsIsFalse : zeroProteinRowsMeansProteinHasNoKinetics ≡ false
    sabioCoverageCreatesDiseaseMechanism : Bool
    sabioCoverageCreatesDiseaseMechanismIsFalse : sabioCoverageCreatesDiseaseMechanism ≡ false

open ExecutedSABIOBoundary public

canonicalExecutedSABIOBoundary : ExecutedSABIOBoundary
canonicalExecutedSABIOBoundary =
  executed-sabio-boundary false refl false refl false refl false refl false refl false refl

canonicalExecutedSABIOGenericReceipt : Receipt.GenericReceipt
canonicalExecutedSABIOGenericReceipt =
  Receipt.mkNonPromotingReceipt
    "executed BH4 SABIO-RK export receipt"
    "DASHI.Biology.BH4ExecutedSABIOReceiptExact"
    "16 exact panel proteins -> SABIO export API -> 190 kinetic-law rows across 11 proteins -> 932 schema-aware parameter objects with zero acquisition errors"
    "closes SABIO transport/acquisition and parameter-object extraction; moves the live frontier to assay/condition adjudication and justified reaction-flux interval translation"
    "export rows and parameter objects are not in-vivo flux bounds or same-compartment state; zero rows for an exact UniProt query do not prove a protein has no kinetics; SABIO coverage does not establish disease mechanism"
    "python3 scripts/run_bh4_phase4_maxcut.py"
