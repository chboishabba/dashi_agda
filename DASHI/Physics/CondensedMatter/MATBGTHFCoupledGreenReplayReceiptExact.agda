module DASHI.Physics.CondensedMatter.MATBGTHFCoupledGreenReplayReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record THFCoupledGreenReplayReceipt : Set where
  constructor thf-coupled-green-replay-receipt
  field
    scriptPath : String
    evidencePath : String
    scriptSHA256 : String
    sourceDOI : String
    matrixDimension : String
    dominantFPeakMeV : String
    positiveCPeakMeV : String
    lowEnergyCPeakMeV : String
    maxInverseResidual : String
    assertionsPassed : Bool

open THFCoupledGreenReplayReceipt public

canonicalTHFCoupledGreenReplayReceipt : THFCoupledGreenReplayReceipt
canonicalTHFCoupledGreenReplayReceipt =
  thf-coupled-green-replay-receipt
    "scripts/matbg_thf_coupled_green_reference.py"
    "Docs/evidence/matbg_thf_coupled_green_reference_2026-10-16.json"
    "bf0a98a086d4fa2dc3667eba5182f9f522c18b3ceac7fce24f8aba672cb59823"
    "10.1038/s41586-026-10378-x"
    "6" "-76.15" "76.15" "-3.7"
    "1.0307899139003352e-14"
    true

record THFCoupledGreenReplayBoundary : Set where
  constructor thf-coupled-green-replay-boundary
  field
    sourceBlockFormulaPaid : Bool
    sourceNeutralityParametersUsed : Bool
    sixBySixBlockInversionPaid : Bool
    coupledGreenBlockExecutionPaid : Bool
    sourceHybridizationNumericallyActive : Bool
    densityIntegralPaid : Bool
    selfConsistentDensitySolvePaid : Bool
    calibratedBZCutoffPaid : Bool
    qtmDataFitPaid : Bool
    sameSampleEntropyPaid : Bool
    agdaKernelReceiptPaid : Bool

open THFCoupledGreenReplayBoundary public

canonicalTHFCoupledGreenReplayBoundary : THFCoupledGreenReplayBoundary
canonicalTHFCoupledGreenReplayBoundary =
  thf-coupled-green-replay-boundary
    true true true true true
    false false false false false false

record THFCoupledGreenReplayAttributionBoundary : Set where
  constructor thf-coupled-green-replay-attribution-boundary
  field
    xiaoEtAlOwnCoupledHubbardIBlockAndParameters : Bool
    dashiOwnsNeutralityFixtureExecutionAndReceipt : Bool
    neutralityFixtureDoesNotCreateDensitySelfConsistency : Bool
    spectralFixtureDoesNotCreateQTMFit : Bool

open THFCoupledGreenReplayAttributionBoundary public

canonicalTHFCoupledGreenReplayAttributionBoundary : THFCoupledGreenReplayAttributionBoundary
canonicalTHFCoupledGreenReplayAttributionBoundary =
  thf-coupled-green-replay-attribution-boundary true true true true
