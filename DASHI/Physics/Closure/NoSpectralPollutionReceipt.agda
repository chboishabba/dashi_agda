module DASHI.Physics.Closure.NoSpectralPollutionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- No-spectral-pollution boundary receipt.
--
-- This is a bounded operator-convergence receipt.  It records the honest
-- boundary used by the Gate 3 spectral-convergence story: Mosco convergence
-- of closed semibounded forms gives strong resolvent convergence.  It is not
-- norm resolvent convergence, it does not by itself exclude spectral
-- pollution, and it does not promote a Yang-Mills or Clay result.

data ResolventConvergenceMode : Set where
  moscoFormConvergence :
    ResolventConvergenceMode

  strongResolventConvergence :
    ResolventConvergenceMode

  normResolventConvergence :
    ResolventConvergenceMode

moscoResolventImage :
  ResolventConvergenceMode
moscoResolventImage =
  strongResolventConvergence

data SpectralBoundaryHypothesis : Set where
  closedSemiboundedForms :
    SpectralBoundaryHypothesis

  commonLowerBound :
    SpectralBoundaryHypothesis

  moscoLiminfCondition :
    SpectralBoundaryHypothesis

  moscoRecoverySequenceCondition :
    SpectralBoundaryHypothesis

  compactnessOrTightnessAgainstEscapingModes :
    SpectralBoundaryHypothesis

  isolatedSectorForTrackedEigenvalues :
    SpectralBoundaryHypothesis

  spectralProjectionContinuityOnIsolatedContour :
    SpectralBoundaryHypothesis

canonicalMoscoStrongResolventHypotheses :
  List SpectralBoundaryHypothesis
canonicalMoscoStrongResolventHypotheses =
  closedSemiboundedForms
  ∷ commonLowerBound
  ∷ moscoLiminfCondition
  ∷ moscoRecoverySequenceCondition
  ∷ []

canonicalNoSpectralPollutionHypotheses :
  List SpectralBoundaryHypothesis
canonicalNoSpectralPollutionHypotheses =
  compactnessOrTightnessAgainstEscapingModes
  ∷ isolatedSectorForTrackedEigenvalues
  ∷ spectralProjectionContinuityOnIsolatedContour
  ∷ []

data NoSpectralPollutionStatus : Set where
  boundaryRecorded_moscoGivesStrongResolvent_notNormResolvent :
    NoSpectralPollutionStatus

data SpectralPollutionPromotion : Set where

spectralPollutionPromotionImpossibleHere :
  SpectralPollutionPromotion →
  ⊥
spectralPollutionPromotionImpossibleHere ()

moscoStrongResolventStatement :
  String
moscoStrongResolventStatement =
  "Mosco convergence of closed semibounded forms gives strong resolvent convergence of the associated self-adjoint operators."

moscoNotNormResolventStatement :
  String
moscoNotNormResolventStatement =
  "The Mosco input is not recorded as norm resolvent convergence; norm resolvent control remains a strictly stronger external obligation."

noSpectralPollutionStatement :
  String
noSpectralPollutionStatement =
  "Strong resolvent convergence alone does not exclude spectral pollution for approximating spectra.  No-spectral-pollution requires extra compactness/tightness and isolated-sector or spectral-projection hypotheses."

record NoSpectralPollutionReceipt : Setω where
  field
    status :
      NoSpectralPollutionStatus

    statusIsCanonical :
      status
      ≡
      boundaryRecorded_moscoGivesStrongResolvent_notNormResolvent

    moscoInput :
      ResolventConvergenceMode

    moscoInputIsMosco :
      moscoInput ≡ moscoFormConvergence

    resolventOutput :
      ResolventConvergenceMode

    resolventOutputIsStrong :
      resolventOutput ≡ moscoResolventImage

    moscoGivesStrongResolvent :
      Bool

    moscoGivesStrongResolventIsTrue :
      moscoGivesStrongResolvent ≡ true

    moscoGivesNormResolvent :
      Bool

    moscoGivesNormResolventIsFalse :
      moscoGivesNormResolvent ≡ false

    strongResolventAloneExcludesSpectralPollution :
      Bool

    strongResolventAloneExcludesSpectralPollutionIsFalse :
      strongResolventAloneExcludesSpectralPollution ≡ false

    noSpectralPollutionRecordedAsHypothesis :
      Bool

    noSpectralPollutionRecordedAsHypothesisIsTrue :
      noSpectralPollutionRecordedAsHypothesis ≡ true

    isolatedSectorHypothesesRequired :
      Bool

    isolatedSectorHypothesesRequiredIsTrue :
      isolatedSectorHypothesesRequired ≡ true

    continuumYangMillsGapPromoted :
      Bool

    continuumYangMillsGapPromotedIsFalse :
      continuumYangMillsGapPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    moscoStrongResolventHypotheses :
      List SpectralBoundaryHypothesis

    moscoStrongResolventHypothesesAreCanonical :
      moscoStrongResolventHypotheses
      ≡
      canonicalMoscoStrongResolventHypotheses

    noSpectralPollutionHypotheses :
      List SpectralBoundaryHypothesis

    noSpectralPollutionHypothesesAreCanonical :
      noSpectralPollutionHypotheses
      ≡
      canonicalNoSpectralPollutionHypotheses

    moscoStrongResolventBoundary :
      String

    moscoStrongResolventBoundaryIsCanonical :
      moscoStrongResolventBoundary ≡ moscoStrongResolventStatement

    moscoNotNormResolventBoundary :
      String

    moscoNotNormResolventBoundaryIsCanonical :
      moscoNotNormResolventBoundary ≡ moscoNotNormResolventStatement

    noSpectralPollutionBoundary :
      String

    noSpectralPollutionBoundaryIsCanonical :
      noSpectralPollutionBoundary ≡ noSpectralPollutionStatement

    promotionFlags :
      List SpectralPollutionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open NoSpectralPollutionReceipt public

canonicalNoSpectralPollutionReceipt :
  NoSpectralPollutionReceipt
canonicalNoSpectralPollutionReceipt =
  record
    { status =
        boundaryRecorded_moscoGivesStrongResolvent_notNormResolvent
    ; statusIsCanonical =
        refl
    ; moscoInput =
        moscoFormConvergence
    ; moscoInputIsMosco =
        refl
    ; resolventOutput =
        strongResolventConvergence
    ; resolventOutputIsStrong =
        refl
    ; moscoGivesStrongResolvent =
        true
    ; moscoGivesStrongResolventIsTrue =
        refl
    ; moscoGivesNormResolvent =
        false
    ; moscoGivesNormResolventIsFalse =
        refl
    ; strongResolventAloneExcludesSpectralPollution =
        false
    ; strongResolventAloneExcludesSpectralPollutionIsFalse =
        refl
    ; noSpectralPollutionRecordedAsHypothesis =
        true
    ; noSpectralPollutionRecordedAsHypothesisIsTrue =
        refl
    ; isolatedSectorHypothesesRequired =
        true
    ; isolatedSectorHypothesesRequiredIsTrue =
        refl
    ; continuumYangMillsGapPromoted =
        false
    ; continuumYangMillsGapPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; moscoStrongResolventHypotheses =
        canonicalMoscoStrongResolventHypotheses
    ; moscoStrongResolventHypothesesAreCanonical =
        refl
    ; noSpectralPollutionHypotheses =
        canonicalNoSpectralPollutionHypotheses
    ; noSpectralPollutionHypothesesAreCanonical =
        refl
    ; moscoStrongResolventBoundary =
        moscoStrongResolventStatement
    ; moscoStrongResolventBoundaryIsCanonical =
        refl
    ; moscoNotNormResolventBoundary =
        moscoNotNormResolventStatement
    ; moscoNotNormResolventBoundaryIsCanonical =
        refl
    ; noSpectralPollutionBoundary =
        noSpectralPollutionStatement
    ; noSpectralPollutionBoundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

moscoDoesNotPromoteNormResolvent :
  moscoGivesNormResolvent canonicalNoSpectralPollutionReceipt ≡ false
moscoDoesNotPromoteNormResolvent =
  refl

noSpectralPollutionNoClayPromotion :
  clayYangMillsPromoted canonicalNoSpectralPollutionReceipt ≡ false
noSpectralPollutionNoClayPromotion =
  refl
