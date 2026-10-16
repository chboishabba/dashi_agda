module DASHI.Physics.CondensedMatter.MATBGTHFHubbardIAtomicReplayReceiptExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record THFHubbardIAtomicReplayReceipt : Set where
  constructor thf-hubbard-i-atomic-replay-receipt
  field
    scriptPath : String
    evidencePath : String
    scriptSHA256 : String
    sourceDOI : String
    uMeV : String
    flavourStateCount : String
    inverseLifetimeMeV : String
    poleCentreMinusMeV : String
    poleCentrePlusMeV : String
    neutralityLowerWeight : String
    neutralityUpperWeight : String
    extremeHoleUpperWeight : String
    extremeElectronLowerWeight : String
    assertionsPassed : Bool

open THFHubbardIAtomicReplayReceipt public

canonicalTHFHubbardIAtomicReplayReceipt : THFHubbardIAtomicReplayReceipt
canonicalTHFHubbardIAtomicReplayReceipt =
  thf-hubbard-i-atomic-replay-receipt
    "scripts/matbg_thf_hubbard_i_atomic_reference.py"
    "Docs/evidence/matbg_thf_hubbard_i_atomic_reference_2026-10-16.json"
    "7633547ed9f4dd10af2088dd482cba0880220e3ea5294b0620f3398d63f54ce5"
    "10.1038/s41586-026-10378-x"
    "60" "8" "1" "-30" "30"
    "0.5" "0.5" "1.0" "1.0"
    true

record THFHubbardIAtomicReplayBoundary : Set where
  constructor thf-hubbard-i-atomic-replay-boundary
  field
    xiaoUAndLifetimeSourcePaid : Bool
    atomicPropagatorFormulaSourcePaid : Bool
    hubbardPoleLocationsPaid : Bool
    fillingDependentSpectralWeightsPaid : Bool
    spectralWeightNormalizationPaid : Bool
    atomicReferenceExecutionPaid : Bool
    literalHcHcfMatricesPaid : Bool
    selfConsistentCFHybridizationPaid : Bool
    qtmExperimentalDataFitPaid : Bool
    sameSampleEntropyPaid : Bool
    agdaKernelReceiptPaid : Bool

open THFHubbardIAtomicReplayBoundary public

canonicalTHFHubbardIAtomicReplayBoundary : THFHubbardIAtomicReplayBoundary
canonicalTHFHubbardIAtomicReplayBoundary =
  thf-hubbard-i-atomic-replay-boundary
    true true true true true true true
    false false false false

record THFHubbardIAtomicReplayAttributionBoundary : Set where
  constructor thf-hubbard-i-atomic-replay-attribution-boundary
  field
    xiaoEtAlOwnHubbardIFormulaAndParameters : Bool
    dashiOwnsSymmetricReferenceExecutionAndReceipt : Bool
    deltaMuZeroIsReferenceFixtureNotMeasuredSampleFit : Bool
    atomicReplayDoesNotCreateSelfConsistentInteractingSolution : Bool

open THFHubbardIAtomicReplayAttributionBoundary public

canonicalTHFHubbardIAtomicReplayAttributionBoundary : THFHubbardIAtomicReplayAttributionBoundary
canonicalTHFHubbardIAtomicReplayAttributionBoundary =
  thf-hubbard-i-atomic-replay-attribution-boundary true true true true
