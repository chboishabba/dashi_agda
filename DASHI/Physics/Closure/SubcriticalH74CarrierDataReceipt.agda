module DASHI.Physics.Closure.SubcriticalH74CarrierDataReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AdjacentOnlyVortexStretchingReceipt as Adjacent

------------------------------------------------------------------------
-- Subcritical H^{7/4} carrier-data frontier receipt.
--
-- This records the smallest meaningful conditional gap: a restricted
-- carrier-approximant route would need both a Fourier restriction theorem
-- and a subcritical adjacent-only dissipation bound.  Neither ingredient is
-- proved here, and no Clay/global arbitrary-data promotion follows.

data SubcriticalH74Ingredient : Set where
  carrierSupportedH74Data :
    SubcriticalH74Ingredient

  fourierRestrictionTheorem :
    SubcriticalH74Ingredient

  subcriticalAdjacentOnlyDissipationBound :
    SubcriticalH74Ingredient

  restrictedCarrierApproximantRegularity :
    SubcriticalH74Ingredient

canonicalSubcriticalH74Ingredients :
  List SubcriticalH74Ingredient
canonicalSubcriticalH74Ingredients =
  carrierSupportedH74Data
  ∷ fourierRestrictionTheorem
  ∷ subcriticalAdjacentOnlyDissipationBound
  ∷ restrictedCarrierApproximantRegularity
  ∷ []

data SubcriticalH74Status : Set where
  option1SmallestMeaningfulGap :
    SubcriticalH74Status

  conditionalRestrictedCarrierRoute :
    SubcriticalH74Status

  fourierRestrictionMissing :
    SubcriticalH74Status

  notAClayPromotion :
    SubcriticalH74Status

canonicalSubcriticalH74Status :
  List SubcriticalH74Status
canonicalSubcriticalH74Status =
  option1SmallestMeaningfulGap
  ∷ conditionalRestrictedCarrierRoute
  ∷ fourierRestrictionMissing
  ∷ notAClayPromotion
  ∷ []

data SubcriticalH74Promotion : Set where

subcriticalH74PromotionImpossibleHere :
  SubcriticalH74Promotion →
  ⊥
subcriticalH74PromotionImpossibleHere ()

subcriticalH74ConditionalStatement :
  String
subcriticalH74ConditionalStatement =
  "Option 1 is the smallest meaningful gap: for H^{7/4} carrier-supported data, if a Fourier restriction theorem and a subcritical adjacent-only dissipation bound are supplied, global regularity for restricted carrier approximants may follow."

record SubcriticalH74CarrierDataReceipt : Setω where
  field
    adjacentOnlyReceipt :
      Adjacent.AdjacentOnlyVortexStretchingReceipt

    adjacentOnlyStatusCanonical :
      Adjacent.status adjacentOnlyReceipt
      ≡
      Adjacent.canonicalAdjacentOnlyVortexStretchingStatus

    adjacentOnlyDissipationCandidateRecorded :
      Adjacent.sameBaseResonancesAdjacentBandOnly adjacentOnlyReceipt
      ≡
      true

    adjacentOnlyDoesNotPromoteClay :
      Adjacent.clayNavierStokesPromoted adjacentOnlyReceipt
      ≡
      false

    ingredients :
      List SubcriticalH74Ingredient

    ingredientsAreCanonical :
      ingredients ≡ canonicalSubcriticalH74Ingredients

    status :
      List SubcriticalH74Status

    statusIsCanonical :
      status ≡ canonicalSubcriticalH74Status

    option1SmallestMeaningfulGapRecorded :
      Bool

    option1SmallestMeaningfulGapRecordedIsTrue :
      option1SmallestMeaningfulGapRecorded ≡ true

    h74CarrierSupportedDataScopeRecorded :
      Bool

    h74CarrierSupportedDataScopeRecordedIsTrue :
      h74CarrierSupportedDataScopeRecorded ≡ true

    conditionalFourierRestrictionPlusAdjacentDissipationRouteRecorded :
      Bool

    conditionalFourierRestrictionPlusAdjacentDissipationRouteRecordedIsTrue :
      conditionalFourierRestrictionPlusAdjacentDissipationRouteRecorded ≡ true

    restrictedCarrierApproximantRegularityMayFollowConditionally :
      Bool

    restrictedCarrierApproximantRegularityMayFollowConditionallyIsTrue :
      restrictedCarrierApproximantRegularityMayFollowConditionally ≡ true

    provedHere :
      Bool

    provedHereIsFalse :
      provedHere ≡ false

    fourierRestrictionTheoremSupplied :
      Bool

    fourierRestrictionTheoremSuppliedIsFalse :
      fourierRestrictionTheoremSupplied ≡ false

    subcriticalAdjacentOnlyDissipationBoundSupplied :
      Bool

    subcriticalAdjacentOnlyDissipationBoundSuppliedIsFalse :
      subcriticalAdjacentOnlyDissipationBoundSupplied ≡ false

    restrictedCarrierGlobalRegularityProved :
      Bool

    restrictedCarrierGlobalRegularityProvedIsFalse :
      restrictedCarrierGlobalRegularityProved ≡ false

    arbitraryDataPromotionClaimed :
      Bool

    arbitraryDataPromotionClaimedIsFalse :
      arbitraryDataPromotionClaimed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ subcriticalH74ConditionalStatement

    promotionFlags :
      List SubcriticalH74Promotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open SubcriticalH74CarrierDataReceipt public

canonicalSubcriticalH74CarrierDataReceipt :
  SubcriticalH74CarrierDataReceipt
canonicalSubcriticalH74CarrierDataReceipt =
  record
    { adjacentOnlyReceipt =
        Adjacent.canonicalAdjacentOnlyVortexStretchingReceipt
    ; adjacentOnlyStatusCanonical =
        refl
    ; adjacentOnlyDissipationCandidateRecorded =
        refl
    ; adjacentOnlyDoesNotPromoteClay =
        refl
    ; ingredients =
        canonicalSubcriticalH74Ingredients
    ; ingredientsAreCanonical =
        refl
    ; status =
        canonicalSubcriticalH74Status
    ; statusIsCanonical =
        refl
    ; option1SmallestMeaningfulGapRecorded =
        true
    ; option1SmallestMeaningfulGapRecordedIsTrue =
        refl
    ; h74CarrierSupportedDataScopeRecorded =
        true
    ; h74CarrierSupportedDataScopeRecordedIsTrue =
        refl
    ; conditionalFourierRestrictionPlusAdjacentDissipationRouteRecorded =
        true
    ; conditionalFourierRestrictionPlusAdjacentDissipationRouteRecordedIsTrue =
        refl
    ; restrictedCarrierApproximantRegularityMayFollowConditionally =
        true
    ; restrictedCarrierApproximantRegularityMayFollowConditionallyIsTrue =
        refl
    ; provedHere =
        false
    ; provedHereIsFalse =
        refl
    ; fourierRestrictionTheoremSupplied =
        false
    ; fourierRestrictionTheoremSuppliedIsFalse =
        refl
    ; subcriticalAdjacentOnlyDissipationBoundSupplied =
        false
    ; subcriticalAdjacentOnlyDissipationBoundSuppliedIsFalse =
        refl
    ; restrictedCarrierGlobalRegularityProved =
        false
    ; restrictedCarrierGlobalRegularityProvedIsFalse =
        refl
    ; arbitraryDataPromotionClaimed =
        false
    ; arbitraryDataPromotionClaimedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        subcriticalH74ConditionalStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "This receipt records a conditional H^{7/4} carrier-supported-data route only"
        ∷ "The route requires a Fourier restriction theorem plus a subcritical adjacent-only dissipation bound"
        ∷ "The Fourier restriction theorem is not supplied here"
        ∷ "The subcritical adjacent-only dissipation bound is not supplied here"
        ∷ "Restricted carrier global regularity, arbitrary-data promotion, and Clay promotion remain false"
        ∷ []
    }

subcriticalH74FourierRestrictionMissing :
  fourierRestrictionTheoremSupplied canonicalSubcriticalH74CarrierDataReceipt
  ≡
  false
subcriticalH74FourierRestrictionMissing =
  refl

subcriticalH74DoesNotPromoteClay :
  clayNavierStokesPromoted canonicalSubcriticalH74CarrierDataReceipt ≡ false
subcriticalH74DoesNotPromoteClay =
  refl

subcriticalH74DoesNotPromoteArbitraryData :
  arbitraryDataPromotionClaimed canonicalSubcriticalH74CarrierDataReceipt
  ≡
  false
subcriticalH74DoesNotPromoteArbitraryData =
  refl
