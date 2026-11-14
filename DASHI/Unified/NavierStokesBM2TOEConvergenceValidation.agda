{-# OPTIONS --safe #-}
module DASHI.Unified.NavierStokesBM2TOEConvergenceValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.NavierStokesBM2TOEConvergenceExact as NSBM2
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as U
import DASHI.Unified.Physics as Physics

adapterFiniteFoldClosed :
  NSBM2.cardinalityFreeFiniteFoldClosed ≡ true
adapterFiniteFoldClosed =
  NSBM2.cardinalityFreeFiniteFoldClosedIsTrue

adapterSamplewisePaymentStillAnalytic :
  NSBM2.samplewisePhysicalPaymentStillAnalytic ≡ true
adapterSamplewisePaymentStillAnalytic =
  NSBM2.samplewisePhysicalPaymentStillAnalyticIsTrue

adapterGalerkinFoldStillAnalytic :
  NSBM2.literalFoldIntoGalerkinDissipationStillAnalytic ≡ true
adapterGalerkinFoldStillAnalytic =
  NSBM2.literalFoldIntoGalerkinDissipationStillAnalyticIsTrue

adapterOldPDFB1B2B3B4Retired :
  NSBM2.oldPDFB1B2B3B4Mandatory ≡ false
adapterOldPDFB1B2B3B4Retired =
  NSBM2.oldPDFB1B2B3B4MandatoryIsFalse

adapterOldPDFB7Retired :
  NSBM2.oldPDFB7DirectCovarianceEqualityMandatory ≡ false
adapterOldPDFB7Retired =
  NSBM2.oldPDFB7DirectCovarianceEqualityMandatoryIsFalse

adapterR571ClayStillFalse :
  NSBM2.r571ClayPromotion ≡ false
adapterR571ClayStillFalse =
  NSBM2.r571ClayPromotionStillFalse

adapterModernClayStillFalse :
  NSBM2.modernNSClayPromotion ≡ false
adapterModernClayStillFalse =
  NSBM2.modernNSClayPromotionStillFalse

toeFiniteFoldMatchesAdapter :
  TOE.toeNavierStokesBM2FiniteFoldClosed
  ≡ NSBM2.cardinalityFreeFiniteFoldClosed
toeFiniteFoldMatchesAdapter = refl

toeClayBoundaryMatchesAdapter :
  TOE.toeNavierStokesBM2ClayPromotion
  ≡ NSBM2.modernNSClayPromotion
toeClayBoundaryMatchesAdapter = refl

unifierFiniteFoldMatchesAdapter :
  U.unifierNavierStokesBM2FiniteFoldClosed
  ≡ NSBM2.cardinalityFreeFiniteFoldClosed
unifierFiniteFoldMatchesAdapter = refl

unifierClayBoundaryMatchesAdapter :
  U.unifierNavierStokesBM2ClayPromotion
  ≡ NSBM2.modernNSClayPromotion
unifierClayBoundaryMatchesAdapter = refl

physicsFiniteFoldMatchesAdapter :
  Physics.navierStokesBM2FiniteFoldClosed
  ≡ NSBM2.cardinalityFreeFiniteFoldClosed
physicsFiniteFoldMatchesAdapter = refl

physicsClayBoundaryMatchesAdapter :
  Physics.navierStokesBM2ClayPromotion
  ≡ NSBM2.modernNSClayPromotion
physicsClayBoundaryMatchesAdapter = refl

toeSamplewisePaymentStillAnalytic :
  NSBM2.samplewisePhysicalPaymentStillAnalytic ≡ true
toeSamplewisePaymentStillAnalytic =
  TOE.toeNavierStokesBM2SamplewisePaymentStillAnalytic

toeGalerkinFoldStillAnalytic :
  NSBM2.literalFoldIntoGalerkinDissipationStillAnalytic ≡ true
toeGalerkinFoldStillAnalytic =
  TOE.toeNavierStokesBM2GalerkinFoldStillAnalytic

toeOldPDFRouteNotMandatory :
  NSBM2.oldPDFB1B2B3B4Mandatory ≡ false
toeOldPDFRouteNotMandatory =
  TOE.toeNavierStokesBM2OldPDFB1B2B3B4NotMandatory

toeOldPDFB7NotMandatory :
  NSBM2.oldPDFB7DirectCovarianceEqualityMandatory ≡ false
toeOldPDFB7NotMandatory =
  TOE.toeNavierStokesBM2OldPDFB7NotMandatory

toeClayStillFalse :
  NSBM2.modernNSClayPromotion ≡ false
toeClayStillFalse =
  TOE.toeNavierStokesBM2ClayPromotionStillFalse
