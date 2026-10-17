module DASHI.Biology.BH4ExecutedSABIOReceiptExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Executed SABIO-RK export-API acquisition receipt, 2026-10-17.
--
-- Live schema-v3 run:
--   16 proteins requested/completed
--   11 proteins with >=1 export row
--   190 kinetic-law entries
--   0 acquisition errors
--
-- Per-protein entry counts:
--   TPH2 75; PAH 44; TPH1 33; MTOR 13; PTS 6; SPR 6; GCH1 4;
--   QDPR 4; TH 2; AGMO 2; TSC2 1.
--   GCHFR, PCBD1, NOS1, NOS2, NOS3: zero rows in this exact export query.
--
-- The run's kinetic_parameter_count = 0 is NOT promoted as a scientific zero:
-- the parser used pre-migration key spellings and missed SABIO export fields such
-- as n_start_value/n_end_value/end_value. Parameter normalization is therefore
-- a separate rerun/adjudication obligation.
------------------------------------------------------------------------

record ExecutedSABIOReceipt : Set where
  constructor executed-sabio-receipt
  field
    proteinsRequested : Nat
    proteinsCompleted : Nat
    proteinsWithEntries : Nat
    kineticEntryCount : Nat
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
    true

executedSABIOProteinsRequested : Nat
executedSABIOProteinsRequested = proteinsRequested canonicalExecutedSABIOReceipt

executedSABIOProteinsCompleted : Nat
executedSABIOProteinsCompleted = proteinsCompleted canonicalExecutedSABIOReceipt

executedSABIOProteinsWithEntries : Nat
executedSABIOProteinsWithEntries = proteinsWithEntries canonicalExecutedSABIOReceipt

executedSABIOKineticEntryCount : Nat
executedSABIOKineticEntryCount = kineticEntryCount canonicalExecutedSABIOReceipt

executedSABIOAcquisitionErrorCount : Nat
executedSABIOAcquisitionErrorCount = acquisitionErrorCount canonicalExecutedSABIOReceipt

executedSABIOEntriesExact : executedSABIOKineticEntryCount ≡ 190
executedSABIOEntriesExact = refl

executedSABIOCoverageExact : executedSABIOProteinsWithEntries ≡ 11
executedSABIOCoverageExact = refl

record ExecutedSABIOBoundary : Set where
  constructor executed-sabio-boundary
  field
    exportRowCreatesInVivoFluxBound : Bool
    exportRowCreatesInVivoFluxBoundIsFalse : exportRowCreatesInVivoFluxBound ≡ false
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
  executed-sabio-boundary false refl false refl false refl false refl false refl

canonicalExecutedSABIOGenericReceipt : Receipt.GenericReceipt
canonicalExecutedSABIOGenericReceipt =
  Receipt.mkNonPromotingReceipt
    "executed BH4 SABIO-RK export receipt"
    "DASHI.Biology.BH4ExecutedSABIOReceiptExact"
    "16 exact panel proteins -> SABIO export API -> 190 kinetic-law rows across 11 proteins with zero acquisition errors"
    "closes SABIO transport/acquisition and moves the live frontier to schema-aware parameter normalization, assay/condition adjudication and justified reaction-flux interval translation"
    "export rows are not in-vivo flux bounds or same-compartment state; the historical zero parameter count was a parser-schema miss, not evidence of absent kinetic parameters; zero rows for an exact query do not prove the protein has no kinetics; SABIO coverage does not establish disease mechanism"
    "python3 scripts/run_bh4_phase4_maxcut.py"
