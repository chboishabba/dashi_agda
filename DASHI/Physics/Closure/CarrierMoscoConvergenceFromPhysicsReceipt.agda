module DASHI.Physics.Closure.CarrierMoscoConvergenceFromPhysicsReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NoSpectralPollutionReceipt as NSP
import DASHI.Physics.Closure.SpectralConvergenceGate3Receipt as Gate3

------------------------------------------------------------------------
-- Carrier Mosco convergence from physics receipt.
--
-- This module records the physical wave-pool/caisson reading of the Mosco
-- convergence story.  Increasing pattern space supplies the recovery
-- sequence / upper-bound intuition.  Energy lower semicontinuity and
-- no-spectral-pollution remain separate formal obligations.  Caisson
-- independence motivates carrier density, but does not prove it.
--
-- Safe correction: Mosco convergence of closed semibounded forms gives
-- strong resolvent convergence, not norm resolvent convergence, unless
-- stronger external hypotheses are supplied.

data CarrierMoscoPhysicsStatus : Set where
  physicalArgumentRecorded_formalProofRequired_gate3Open_noClayPromotion :
    CarrierMoscoPhysicsStatus

data CarrierMoscoPhysicsReading : Set where
  wavePoolPatternSpaceIncreasing :
    CarrierMoscoPhysicsReading

  caissonBoundaryIndependenceMotivatesDensity :
    CarrierMoscoPhysicsReading

  recoveryUpperBoundObligationIdentified :
    CarrierMoscoPhysicsReading

  energyLowerSemicontinuitySeparateObligation :
    CarrierMoscoPhysicsReading

  noSpectralPollutionSeparateObligation :
    CarrierMoscoPhysicsReading

  carrierDensityNotProvedByCaissonIndependence :
    CarrierMoscoPhysicsReading

canonicalCarrierMoscoPhysicsReadings :
  List CarrierMoscoPhysicsReading
canonicalCarrierMoscoPhysicsReadings =
  wavePoolPatternSpaceIncreasing
  ∷ caissonBoundaryIndependenceMotivatesDensity
  ∷ recoveryUpperBoundObligationIdentified
  ∷ energyLowerSemicontinuitySeparateObligation
  ∷ noSpectralPollutionSeparateObligation
  ∷ carrierDensityNotProvedByCaissonIndependence
  ∷ []

data CarrierMoscoFormalObligation : Set where
  proveRecoverySequencesForIncreasingPatternSpace :
    CarrierMoscoFormalObligation

  proveEnergyLowerSemicontinuity :
    CarrierMoscoFormalObligation

  proveCarrierCoreDensity :
    CarrierMoscoFormalObligation

  proveDomainCompatibility :
    CarrierMoscoFormalObligation

  proveCompactnessOrTightnessAgainstEscapingModes :
    CarrierMoscoFormalObligation

  proveIsolatedSectorNoSpectralPollution :
    CarrierMoscoFormalObligation

canonicalCarrierMoscoFormalObligations :
  List CarrierMoscoFormalObligation
canonicalCarrierMoscoFormalObligations =
  proveRecoverySequencesForIncreasingPatternSpace
  ∷ proveEnergyLowerSemicontinuity
  ∷ proveCarrierCoreDensity
  ∷ proveDomainCompatibility
  ∷ proveCompactnessOrTightnessAgainstEscapingModes
  ∷ proveIsolatedSectorNoSpectralPollution
  ∷ []

data CarrierMoscoConclusion : Set where
  physicalReadingRecorded :
    CarrierMoscoConclusion

  recoveryUpperBoundMotivatedNotProved :
    CarrierMoscoConclusion

  lowerSemicontinuityNotDischarged :
    CarrierMoscoConclusion

  noSpectralPollutionNotDischarged :
    CarrierMoscoConclusion

  carrierDensityMotivatedNotProved :
    CarrierMoscoConclusion

  gate3RemainsOpen :
    CarrierMoscoConclusion

  moscoOnlyStrongResolvent :
    CarrierMoscoConclusion

  noNormResolventPromotion :
    CarrierMoscoConclusion

  noClayPromotion :
    CarrierMoscoConclusion

canonicalCarrierMoscoConclusions :
  List CarrierMoscoConclusion
canonicalCarrierMoscoConclusions =
  physicalReadingRecorded
  ∷ recoveryUpperBoundMotivatedNotProved
  ∷ lowerSemicontinuityNotDischarged
  ∷ noSpectralPollutionNotDischarged
  ∷ carrierDensityMotivatedNotProved
  ∷ gate3RemainsOpen
  ∷ moscoOnlyStrongResolvent
  ∷ noNormResolventPromotion
  ∷ noClayPromotion
  ∷ []

data CarrierMoscoPromotion : Set where

carrierMoscoPromotionImpossibleHere :
  CarrierMoscoPromotion →
  ⊥
carrierMoscoPromotionImpossibleHere ()

carrierMoscoPhysicsStatement :
  String
carrierMoscoPhysicsStatement =
  "Wave-pool and caisson physics are recorded as intuition for the carrier Mosco story: increasing pattern space motivates recovery/upper-bound data, and caisson independence motivates carrier density."

carrierMoscoObligationStatement :
  String
carrierMoscoObligationStatement =
  "Energy lower semicontinuity, carrier density, domain compatibility, and no-spectral-pollution remain separate formal obligations; the physical argument does not discharge them."

carrierMoscoResolventCorrectionStatement :
  String
carrierMoscoResolventCorrectionStatement =
  "Mosco convergence gives strong resolvent convergence, not norm resolvent convergence, unless stronger external hypotheses are supplied."

carrierMoscoGate3Statement :
  String
carrierMoscoGate3Statement =
  "Gate 3 remains open: the receipt records the physical argument but fails closed and exports no norm-resolvent, continuum Yang-Mills, or Clay promotion."

record CarrierMoscoConvergenceFromPhysicsReceipt : Setω where
  field
    status :
      CarrierMoscoPhysicsStatus

    statusIsCanonical :
      status
      ≡
      physicalArgumentRecorded_formalProofRequired_gate3Open_noClayPromotion

    noSpectralPollutionReceipt :
      NSP.NoSpectralPollutionReceipt

    gate3Receipt :
      Gate3.SpectralConvergenceGate3Receipt

    moscoStrongResolventAvailable :
      NSP.moscoGivesStrongResolvent noSpectralPollutionReceipt ≡ true

    moscoNormResolventStillFalse :
      NSP.moscoGivesNormResolvent noSpectralPollutionReceipt ≡ false

    gate3NoSpectralPollutionRequired :
      Gate3.gate3NoSpectralPollutionRequired gate3Receipt ≡ true

    gate3NormResolventStillFalse :
      Gate3.gate3NormResolventProved gate3Receipt ≡ false

    gate3ClayStillFalse :
      Gate3.clayYangMillsPromoted gate3Receipt ≡ false

    physicalReadings :
      List CarrierMoscoPhysicsReading

    physicalReadingsAreCanonical :
      physicalReadings ≡ canonicalCarrierMoscoPhysicsReadings

    formalObligations :
      List CarrierMoscoFormalObligation

    formalObligationsAreCanonical :
      formalObligations ≡ canonicalCarrierMoscoFormalObligations

    conclusions :
      List CarrierMoscoConclusion

    conclusionsAreCanonical :
      conclusions ≡ canonicalCarrierMoscoConclusions

    physicalArgumentRecorded :
      Bool

    physicalArgumentRecordedIsTrue :
      physicalArgumentRecorded ≡ true

    recoveryUpperBoundMotivated :
      Bool

    recoveryUpperBoundMotivatedIsTrue :
      recoveryUpperBoundMotivated ≡ true

    recoveryUpperBoundProvedHere :
      Bool

    recoveryUpperBoundProvedHereIsFalse :
      recoveryUpperBoundProvedHere ≡ false

    energyLowerSemicontinuityProvedHere :
      Bool

    energyLowerSemicontinuityProvedHereIsFalse :
      energyLowerSemicontinuityProvedHere ≡ false

    noSpectralPollutionProvedHere :
      Bool

    noSpectralPollutionProvedHereIsFalse :
      noSpectralPollutionProvedHere ≡ false

    caissonIndependenceMotivatesCarrierDensity :
      Bool

    caissonIndependenceMotivatesCarrierDensityIsTrue :
      caissonIndependenceMotivatesCarrierDensity ≡ true

    carrierDensityProvedHere :
      Bool

    carrierDensityProvedHereIsFalse :
      carrierDensityProvedHere ≡ false

    formalProofRequired :
      Bool

    formalProofRequiredIsTrue :
      formalProofRequired ≡ true

    gate3Closed :
      Bool

    gate3ClosedIsFalse :
      gate3Closed ≡ false

    moscoGivesStrongResolvent :
      Bool

    moscoGivesStrongResolventIsTrue :
      moscoGivesStrongResolvent ≡ true

    moscoGivesNormResolvent :
      Bool

    moscoGivesNormResolventIsFalse :
      moscoGivesNormResolvent ≡ false

    normResolventPromotion :
      Bool

    normResolventPromotionIsFalse :
      normResolventPromotion ≡ false

    continuumYangMillsGapPromoted :
      Bool

    continuumYangMillsGapPromotedIsFalse :
      continuumYangMillsGapPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    physicsBoundary :
      String

    physicsBoundaryIsCanonical :
      physicsBoundary ≡ carrierMoscoPhysicsStatement

    obligationBoundary :
      String

    obligationBoundaryIsCanonical :
      obligationBoundary ≡ carrierMoscoObligationStatement

    resolventCorrectionBoundary :
      String

    resolventCorrectionBoundaryIsCanonical :
      resolventCorrectionBoundary ≡ carrierMoscoResolventCorrectionStatement

    gate3Boundary :
      String

    gate3BoundaryIsCanonical :
      gate3Boundary ≡ carrierMoscoGate3Statement

    promotionFlags :
      List CarrierMoscoPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open CarrierMoscoConvergenceFromPhysicsReceipt public

canonicalCarrierMoscoConvergenceFromPhysicsReceipt :
  CarrierMoscoConvergenceFromPhysicsReceipt
canonicalCarrierMoscoConvergenceFromPhysicsReceipt =
  record
    { status =
        physicalArgumentRecorded_formalProofRequired_gate3Open_noClayPromotion
    ; statusIsCanonical =
        refl
    ; noSpectralPollutionReceipt =
        NSP.canonicalNoSpectralPollutionReceipt
    ; gate3Receipt =
        Gate3.canonicalSpectralConvergenceGate3Receipt
    ; moscoStrongResolventAvailable =
        refl
    ; moscoNormResolventStillFalse =
        refl
    ; gate3NoSpectralPollutionRequired =
        refl
    ; gate3NormResolventStillFalse =
        refl
    ; gate3ClayStillFalse =
        refl
    ; physicalReadings =
        canonicalCarrierMoscoPhysicsReadings
    ; physicalReadingsAreCanonical =
        refl
    ; formalObligations =
        canonicalCarrierMoscoFormalObligations
    ; formalObligationsAreCanonical =
        refl
    ; conclusions =
        canonicalCarrierMoscoConclusions
    ; conclusionsAreCanonical =
        refl
    ; physicalArgumentRecorded =
        true
    ; physicalArgumentRecordedIsTrue =
        refl
    ; recoveryUpperBoundMotivated =
        true
    ; recoveryUpperBoundMotivatedIsTrue =
        refl
    ; recoveryUpperBoundProvedHere =
        false
    ; recoveryUpperBoundProvedHereIsFalse =
        refl
    ; energyLowerSemicontinuityProvedHere =
        false
    ; energyLowerSemicontinuityProvedHereIsFalse =
        refl
    ; noSpectralPollutionProvedHere =
        false
    ; noSpectralPollutionProvedHereIsFalse =
        refl
    ; caissonIndependenceMotivatesCarrierDensity =
        true
    ; caissonIndependenceMotivatesCarrierDensityIsTrue =
        refl
    ; carrierDensityProvedHere =
        false
    ; carrierDensityProvedHereIsFalse =
        refl
    ; formalProofRequired =
        true
    ; formalProofRequiredIsTrue =
        refl
    ; gate3Closed =
        false
    ; gate3ClosedIsFalse =
        refl
    ; moscoGivesStrongResolvent =
        true
    ; moscoGivesStrongResolventIsTrue =
        refl
    ; moscoGivesNormResolvent =
        false
    ; moscoGivesNormResolventIsFalse =
        refl
    ; normResolventPromotion =
        false
    ; normResolventPromotionIsFalse =
        refl
    ; continuumYangMillsGapPromoted =
        false
    ; continuumYangMillsGapPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; physicsBoundary =
        carrierMoscoPhysicsStatement
    ; physicsBoundaryIsCanonical =
        refl
    ; obligationBoundary =
        carrierMoscoObligationStatement
    ; obligationBoundaryIsCanonical =
        refl
    ; resolventCorrectionBoundary =
        carrierMoscoResolventCorrectionStatement
    ; resolventCorrectionBoundaryIsCanonical =
        refl
    ; gate3Boundary =
        carrierMoscoGate3Statement
    ; gate3BoundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

carrierMoscoPhysicsArgumentRecorded :
  physicalArgumentRecorded
    canonicalCarrierMoscoConvergenceFromPhysicsReceipt
  ≡
  true
carrierMoscoPhysicsArgumentRecorded =
  refl

carrierMoscoFormalProofRequired :
  formalProofRequired canonicalCarrierMoscoConvergenceFromPhysicsReceipt
  ≡
  true
carrierMoscoFormalProofRequired =
  refl

carrierMoscoGate3RemainsOpen :
  gate3Closed canonicalCarrierMoscoConvergenceFromPhysicsReceipt ≡ false
carrierMoscoGate3RemainsOpen =
  refl

carrierMoscoNoNormResolventPromotion :
  normResolventPromotion canonicalCarrierMoscoConvergenceFromPhysicsReceipt
  ≡
  false
carrierMoscoNoNormResolventPromotion =
  refl

carrierMoscoNoClayPromotion :
  clayYangMillsPromoted canonicalCarrierMoscoConvergenceFromPhysicsReceipt
  ≡
  false
carrierMoscoNoClayPromotion =
  refl
