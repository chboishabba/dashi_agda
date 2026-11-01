module DASHI.Physics.Closure.NSVorticityNoMechanismReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSFrameRestrictionReceipt as Restriction
import DASHI.Physics.Closure.NSRegularityGapReceipt as Gap

data NSVorticityNoMechanismStatus : Set where
  noCarrierVorticityMechanismRecorded :
    NSVorticityNoMechanismStatus

data NSVorticityNoMechanismBlocker : Set where
  missingCarrierVorticityDefinition :
    NSVorticityNoMechanismBlocker

  missingCarrierVorticityEvolutionLaw :
    NSVorticityNoMechanismBlocker

  missingUniformBKMVorticityControl :
    NSVorticityNoMechanismBlocker

  missingContinuumCompactnessPassage :
    NSVorticityNoMechanismBlocker

canonicalNSVorticityNoMechanismBlockers :
  List NSVorticityNoMechanismBlocker
canonicalNSVorticityNoMechanismBlockers =
  missingCarrierVorticityDefinition
  ∷ missingCarrierVorticityEvolutionLaw
  ∷ missingUniformBKMVorticityControl
  ∷ missingContinuumCompactnessPassage
  ∷ []

data NSVorticityNoMechanismPromotion : Set where

nsVorticityNoMechanismPromotionImpossibleHere :
  NSVorticityNoMechanismPromotion →
  ⊥
nsVorticityNoMechanismPromotionImpossibleHere ()

vorticityBoundaryStatement : String
vorticityBoundaryStatement =
  "The closure receipts record vorticity diagnostics, but no carrier-native mechanism produces BKM control or global NS regularity."

record NSVorticityNoMechanismReceipt : Setω where
  field
    status :
      NSVorticityNoMechanismStatus

    frameRestrictionReceipt :
      Restriction.NSFrameRestrictionReceipt

    restrictedFrameBoundStillOpen :
      Restriction.restrictedFrameBoundProved frameRestrictionReceipt ≡ false

    regularityGapReceipt :
      Gap.NSRegularityGapReceipt

    finiteVorticityRungRecorded :
      Gap.vorticityRungRecorded regularityGapReceipt ≡ true

    bkmVorticityControlStillOpen :
      Gap.bkmVorticityControlClosed regularityGapReceipt ≡ false

    carrierVorticityMechanismConstructed :
      Bool

    carrierVorticityMechanismConstructedIsFalse :
      carrierVorticityMechanismConstructed ≡ false

    vorticityZeroMeanRouteCandidate :
      Bool

    vorticityZeroMeanRouteCandidateIsTrue :
      vorticityZeroMeanRouteCandidate ≡ true

    vorticityZeroMeanMechanismProved :
      Bool

    vorticityZeroMeanMechanismProvedIsFalse :
      vorticityZeroMeanMechanismProved ≡ false

    uniformVorticityControlConstructed :
      Bool

    uniformVorticityControlConstructedIsFalse :
      uniformVorticityControlConstructed ≡ false

    globalSmoothRegularityPromoted :
      Bool

    globalSmoothRegularityPromotedIsFalse :
      globalSmoothRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ vorticityBoundaryStatement

    blockers :
      List NSVorticityNoMechanismBlocker

    blockersAreCanonical :
      blockers ≡ canonicalNSVorticityNoMechanismBlockers

    promotionFlags :
      List NSVorticityNoMechanismPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSVorticityNoMechanismReceipt public

canonicalNSVorticityNoMechanismReceipt :
  NSVorticityNoMechanismReceipt
canonicalNSVorticityNoMechanismReceipt =
  record
    { status =
        noCarrierVorticityMechanismRecorded
    ; frameRestrictionReceipt =
        Restriction.canonicalNSFrameRestrictionReceipt
    ; restrictedFrameBoundStillOpen =
        refl
    ; regularityGapReceipt =
        Gap.canonicalNSRegularityGapReceipt
    ; finiteVorticityRungRecorded =
        refl
    ; bkmVorticityControlStillOpen =
        refl
    ; carrierVorticityMechanismConstructed =
        false
    ; carrierVorticityMechanismConstructedIsFalse =
        refl
    ; vorticityZeroMeanRouteCandidate =
        true
    ; vorticityZeroMeanRouteCandidateIsTrue =
        refl
    ; vorticityZeroMeanMechanismProved =
        false
    ; vorticityZeroMeanMechanismProvedIsFalse =
        refl
    ; uniformVorticityControlConstructed =
        false
    ; uniformVorticityControlConstructedIsFalse =
        refl
    ; globalSmoothRegularityPromoted =
        false
    ; globalSmoothRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; boundaryStatement =
        vorticityBoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    ; blockers =
        canonicalNSVorticityNoMechanismBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Finite vorticity diagnostics and the zero-mean/vorticity route are recorded only as candidates"
        ∷ "No carrier-native vorticity definition, evolution law, or BKM control mechanism is constructed"
        ∷ "Global smooth Navier-Stokes regularity and Clay promotion remain false"
        ∷ []
    }

carrierVorticityMechanismStillAbsent :
  carrierVorticityMechanismConstructed
    canonicalNSVorticityNoMechanismReceipt ≡ false
carrierVorticityMechanismStillAbsent =
  refl

navierStokesClayStillFalse :
  clayNavierStokesPromoted canonicalNSVorticityNoMechanismReceipt ≡ false
navierStokesClayStillFalse =
  refl
