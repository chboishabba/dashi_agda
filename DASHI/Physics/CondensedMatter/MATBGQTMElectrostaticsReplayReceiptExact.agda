module DASHI.Physics.CondensedMatter.MATBGQTMElectrostaticsReplayReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record QTMElectrostaticsReplayReceipt : Set where
  constructor qtm-electrostatics-replay-receipt
  field
    scriptPath : String
    evidencePath : String
    scriptSHA256 : String
    sourceDOI : String
    tipBiasV : String
    backGateV : String
    nTCm2 : String
    nTotalCm2 : String
    nBCm2 : String
    assertionsPassed : Bool

open QTMElectrostaticsReplayReceipt public

canonicalQTMElectrostaticsReplayReceipt : QTMElectrostaticsReplayReceipt
canonicalQTMElectrostaticsReplayReceipt =
  qtm-electrostatics-replay-receipt
    "scripts/matbg_qtm_electrostatics_reference.py"
    "Docs/evidence/matbg_qtm_electrostatics_reference_2026-10-16.json"
    "8aad7c408e0ae91ff5d1a934eab1442ca9f7248e87841ea1066da09e73a62de3"
    "10.1038/s41586-026-10378-x"
    "0.01" "10.0"
    "143554708712.59756"
    "3888460153389.055"
    "3744905444676.4575"
    true

record QTMElectrostaticsReplayBoundary : Set where
  constructor qtm-electrostatics-replay-boundary
  field
    xiaoCapacitancesSourcePaid : Bool
    sourceElectrostaticEquationsPaid : Bool
    zeroChemicalPotentialCapacitorReferencePaid : Bool
    densityPerVoltConversionPaid : Bool
    measuredSkewMapReplayPaid : Bool
    chemicalPotentialInversionPaid : Bool
    qtmDataFitPaid : Bool
    sameSampleEntropyPaid : Bool
    agdaKernelReceiptPaid : Bool

open QTMElectrostaticsReplayBoundary public

canonicalQTMElectrostaticsReplayBoundary : QTMElectrostaticsReplayBoundary
canonicalQTMElectrostaticsReplayBoundary =
  qtm-electrostatics-replay-boundary
    true true true true false false false false false

record QTMElectrostaticsReplayAttributionBoundary : Set where
  constructor qtm-electrostatics-replay-attribution-boundary
  field
    xiaoEtAlOwnCalibratedCapacitancesAndEquations : Bool
    dashiOwnsZeroChemicalPotentialNumericalFixture : Bool
    capacitorFixtureDoesNotCreateMeasuredSkewReplay : Bool

open QTMElectrostaticsReplayAttributionBoundary public

canonicalQTMElectrostaticsReplayAttributionBoundary : QTMElectrostaticsReplayAttributionBoundary
canonicalQTMElectrostaticsReplayAttributionBoundary =
  qtm-electrostatics-replay-attribution-boundary true true true
