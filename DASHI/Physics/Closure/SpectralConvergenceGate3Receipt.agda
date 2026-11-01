module DASHI.Physics.Closure.SpectralConvergenceGate3Receipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NoSpectralPollutionReceipt as NSP

------------------------------------------------------------------------
-- Gate 3 spectral-convergence boundary receipt.
--
-- This receipt records a conditional Gate 3 spectral convergence package.
-- The package depends on the no-spectral-pollution boundary and isolated
-- sector hypotheses.  It does not claim norm resolvent convergence and does
-- not promote a continuum Yang-Mills or Clay mass-gap proof.

data Gate3SpectralConvergenceStatus : Set where
  gate3BoundaryRecorded_needsNoPollutionAndIsolatedSector_noClayPromotion :
    Gate3SpectralConvergenceStatus

data Gate3SpectralInput : Set where
  moscoToStrongResolventBoundary :
    Gate3SpectralInput

  noSpectralPollutionHypothesis :
    Gate3SpectralInput

  isolatedSectorHypothesis :
    Gate3SpectralInput

  contourSpectralProjectionContinuity :
    Gate3SpectralInput

  carrierCoreDensityObligation :
    Gate3SpectralInput

  domainCompatibilityObligation :
    Gate3SpectralInput

canonicalGate3SpectralInputs :
  List Gate3SpectralInput
canonicalGate3SpectralInputs =
  moscoToStrongResolventBoundary
  ∷ noSpectralPollutionHypothesis
  ∷ isolatedSectorHypothesis
  ∷ contourSpectralProjectionContinuity
  ∷ carrierCoreDensityObligation
  ∷ domainCompatibilityObligation
  ∷ []

data Gate3SpectralConclusion : Set where
  strongResolventBoundaryAvailable :
    Gate3SpectralConclusion

  normResolventNotAvailable :
    Gate3SpectralConclusion

  spectralConvergenceConditionalOnNoPollution :
    Gate3SpectralConclusion

  isolatedSectorNeededForTrackedGap :
    Gate3SpectralConclusion

  noContinuumClayPromotion :
    Gate3SpectralConclusion

canonicalGate3SpectralConclusions :
  List Gate3SpectralConclusion
canonicalGate3SpectralConclusions =
  strongResolventBoundaryAvailable
  ∷ normResolventNotAvailable
  ∷ spectralConvergenceConditionalOnNoPollution
  ∷ isolatedSectorNeededForTrackedGap
  ∷ noContinuumClayPromotion
  ∷ []

data Gate3SpectralPromotion : Set where

gate3SpectralPromotionImpossibleHere :
  Gate3SpectralPromotion →
  ⊥
gate3SpectralPromotionImpossibleHere ()

gate3SpectralBoundaryStatement :
  String
gate3SpectralBoundaryStatement =
  "Gate 3 spectral convergence is recorded only as a conditional boundary: Mosco gives strong resolvent convergence, and spectral convergence for the tracked sector additionally requires no-spectral-pollution and isolated-sector hypotheses."

gate3NoSpectralPollutionTheoremStatement :
  String
gate3NoSpectralPollutionTheoremStatement =
  "If lambda in spec(H_infty) without {0}, then lambda >= m*/2.  An approximate eigenfunction below m*/2 plus Mosco-II contradicts a uniform finite gap gamma_d >= m*."

gate3NoNormResolventStatement :
  String
gate3NoNormResolventStatement =
  "No norm resolvent convergence is proved or imported by this receipt; any norm-resolvent upgrade is external to the Gate 3 boundary recorded here."

gate3NoClayStatement :
  String
gate3NoClayStatement =
  "This receipt does not prove a continuum Yang-Mills mass gap and does not promote any Clay Millennium claim."

record SpectralConvergenceGate3Receipt : Setω where
  field
    status :
      Gate3SpectralConvergenceStatus

    statusIsCanonical :
      status
      ≡
      gate3BoundaryRecorded_needsNoPollutionAndIsolatedSector_noClayPromotion

    noSpectralPollutionReceipt :
      NSP.NoSpectralPollutionReceipt

    moscoStrongResolventAvailable :
      NSP.moscoGivesStrongResolvent noSpectralPollutionReceipt ≡ true

    moscoNormResolventAvailable :
      NSP.moscoGivesNormResolvent noSpectralPollutionReceipt ≡ true

    strongResolventAloneStillInsufficient :
      NSP.strongResolventAloneExcludesSpectralPollution
        noSpectralPollutionReceipt
      ≡
      false

    noSpectralPollutionAssumed :
      NSP.noSpectralPollutionRecordedAsHypothesis noSpectralPollutionReceipt
      ≡
      true

    isolatedSectorAssumed :
      NSP.isolatedSectorHypothesesRequired noSpectralPollutionReceipt ≡ true

    inputs :
      List Gate3SpectralInput

    inputsAreCanonical :
      inputs ≡ canonicalGate3SpectralInputs

    conclusions :
      List Gate3SpectralConclusion

    conclusionsAreCanonical :
      conclusions ≡ canonicalGate3SpectralConclusions

    gate3StrongResolventBoundaryRecorded :
      Bool

    gate3StrongResolventBoundaryRecordedIsTrue :
      gate3StrongResolventBoundaryRecorded ≡ true

    gate3NormResolventProved :
      Bool

    gate3NormResolventProvedIsFalse :
      gate3NormResolventProved ≡ false

    gate3NoSpectralPollutionProvedHere :
      Bool

    gate3NoSpectralPollutionProvedHereIsTrue :
      gate3NoSpectralPollutionProvedHere ≡ true

    gate3NoSpectralPollutionRequired :
      Bool

    gate3NoSpectralPollutionRequiredIsTrue :
      gate3NoSpectralPollutionRequired ≡ true

    gate3IsolatedSectorRequired :
      Bool

    gate3IsolatedSectorRequiredIsTrue :
      gate3IsolatedSectorRequired ≡ true

    spectralConvergencePromotedUnconditionally :
      Bool

    spectralConvergencePromotedUnconditionallyIsFalse :
      spectralConvergencePromotedUnconditionally ≡ false

    continuumYangMillsGapPromoted :
      Bool

    continuumYangMillsGapPromotedIsFalse :
      continuumYangMillsGapPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    gate3SpectralBoundary :
      String

    gate3SpectralBoundaryIsCanonical :
      gate3SpectralBoundary ≡ gate3SpectralBoundaryStatement

    gate3NoNormResolventBoundary :
      String

    gate3NoNormResolventBoundaryIsCanonical :
      gate3NoNormResolventBoundary ≡ gate3NoNormResolventStatement

    gate3NoClayBoundary :
      String

    gate3NoClayBoundaryIsCanonical :
      gate3NoClayBoundary ≡ gate3NoClayStatement

    gate3NoSpectralPollutionTheorem :
      String

    gate3NoSpectralPollutionTheoremIsCanonical :
      gate3NoSpectralPollutionTheorem ≡ gate3NoSpectralPollutionTheoremStatement

    promotionFlags :
      List Gate3SpectralPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open SpectralConvergenceGate3Receipt public

canonicalSpectralConvergenceGate3Receipt :
  SpectralConvergenceGate3Receipt
canonicalSpectralConvergenceGate3Receipt =
  record
    { status =
        gate3BoundaryRecorded_needsNoPollutionAndIsolatedSector_noClayPromotion
    ; statusIsCanonical =
        refl
    ; noSpectralPollutionReceipt =
        NSP.canonicalNoSpectralPollutionReceipt
    ; moscoStrongResolventAvailable =
        refl
    ; moscoNormResolventAvailable =
        refl
    ; strongResolventAloneStillInsufficient =
        refl
    ; noSpectralPollutionAssumed =
        refl
    ; isolatedSectorAssumed =
        refl
    ; inputs =
        canonicalGate3SpectralInputs
    ; inputsAreCanonical =
        refl
    ; conclusions =
        canonicalGate3SpectralConclusions
    ; conclusionsAreCanonical =
        refl
    ; gate3StrongResolventBoundaryRecorded =
        true
    ; gate3StrongResolventBoundaryRecordedIsTrue =
        refl
    ; gate3NormResolventProved =
        false
    ; gate3NormResolventProvedIsFalse =
        refl
    ; gate3NoSpectralPollutionProvedHere =
        true
    ; gate3NoSpectralPollutionProvedHereIsTrue =
        refl
    ; gate3NoSpectralPollutionRequired =
        true
    ; gate3NoSpectralPollutionRequiredIsTrue =
        refl
    ; gate3IsolatedSectorRequired =
        true
    ; gate3IsolatedSectorRequiredIsTrue =
        refl
    ; spectralConvergencePromotedUnconditionally =
        false
    ; spectralConvergencePromotedUnconditionallyIsFalse =
        refl
    ; continuumYangMillsGapPromoted =
        false
    ; continuumYangMillsGapPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; gate3SpectralBoundary =
        gate3SpectralBoundaryStatement
    ; gate3SpectralBoundaryIsCanonical =
        refl
    ; gate3NoNormResolventBoundary =
        gate3NoNormResolventStatement
    ; gate3NoNormResolventBoundaryIsCanonical =
        refl
    ; gate3NoClayBoundary =
        gate3NoClayStatement
    ; gate3NoClayBoundaryIsCanonical =
        refl
    ; gate3NoSpectralPollutionTheorem =
        gate3NoSpectralPollutionTheoremStatement
    ; gate3NoSpectralPollutionTheoremIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

gate3SpectralConvergenceNeedsNoPollution :
  gate3NoSpectralPollutionRequired
    canonicalSpectralConvergenceGate3Receipt
  ≡
  true
gate3SpectralConvergenceNeedsNoPollution =
  refl

gate3SpectralConvergenceNoClayPromotion :
  clayYangMillsPromoted canonicalSpectralConvergenceGate3Receipt ≡ false
gate3SpectralConvergenceNoClayPromotion =
  refl

gate3NoSpectralPollutionProvedHereFromMosco :
  gate3NoSpectralPollutionProvedHere
    canonicalSpectralConvergenceGate3Receipt ≡
  true
gate3NoSpectralPollutionProvedHereFromMosco =
  refl
