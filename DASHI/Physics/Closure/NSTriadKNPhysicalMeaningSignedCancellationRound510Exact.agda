module DASHI.Physics.Closure.NSTriadKNPhysicalMeaningSignedCancellationRound510Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNClayResidualIntrospectionRound509Exact as R509
import DASHI.Physics.Closure.NSTriadKNWaleffeForcingRouteAuditRound108Exact as R108

------------------------------------------------------------------------
-- ROUND510 / PHYSICAL MEANING OF THE LIVE SIGNED-CANCELLATION SEARCH
--
-- The live R406 problem is not a generic large-nonlinearity estimate.  The
-- self-phase contribution is already algebraically exposed; the remaining
-- physical risk is coherent EXTERNAL cross-triad forcing.  Any useful producer
-- must therefore preserve enough sign/phase/network/time information to control
-- that remainder uniformly in the Galerkin cutoff.
------------------------------------------------------------------------

data PhysicalQuestion510 : Set where
  sameOutputSignedInteractionPersistsAcrossCutoff : PhysicalQuestion510
  externalTriadsStayCoherentlyAdverseInTime : PhysicalQuestion510
  exactRemainderLivesOnSameTrajectory : PhysicalQuestion510

data SearchRoute510 : Set where
  signedPhaseNetworkTimeGeometry : SearchRoute510
  positivePartReplacement : SearchRoute510
  absoluteQuarticSchurMajorant : SearchRoute510
  unmaskedNetworkCancellation : SearchRoute510
  retaxSelfPhaseAsExternalForcing : SearchRoute510
  directSameObjectR406Weld : SearchRoute510

data RouteDisposition510 : Set where
  liveProducer : RouteDisposition510
  requiredAfterPhysicalPayment : RouteDisposition510
  ruledOutByExistingNoGo : RouteDisposition510

routeDisposition : SearchRoute510 → RouteDisposition510
routeDisposition signedPhaseNetworkTimeGeometry = liveProducer
routeDisposition directSameObjectR406Weld = requiredAfterPhysicalPayment
routeDisposition positivePartReplacement = ruledOutByExistingNoGo
routeDisposition absoluteQuarticSchurMajorant = ruledOutByExistingNoGo
routeDisposition unmaskedNetworkCancellation = ruledOutByExistingNoGo
routeDisposition retaxSelfPhaseAsExternalForcing = ruledOutByExistingNoGo

-- Physical interpretation of the current R509 residuals.
physicalQuestionFor : R509.ClayResidual509 → PhysicalQuestion510
physicalQuestionFor R509.signedCrossUniformBoundResidual =
  sameOutputSignedInteractionPersistsAcrossCutoff
physicalQuestionFor R509.externalCrossTriadCriticalPaymentResidual =
  externalTriadsStayCoherentlyAdverseInTime
physicalQuestionFor R509.literalR406RemainderWeldResidual =
  exactRemainderLivesOnSameTrajectory
physicalQuestionFor R509.clayCutsetClosed =
  exactRemainderLivesOnSameTrajectory

-- Existing R108 results justify pruning the sign-destroying / already-refuted
-- families before further theorem search.
positivePartNotRequired :
  R108.round108PositivePartOfNetworkForcingRequired ≡ false
positivePartNotRequired = R108.round108PositivePartOfNetworkForcingRequiredIsFalse

quarticSchurDoesNotGiveFixedQuadraticAbsorption :
  R108.round108DirectGapWeightedQuarticSchurSuppliesFixedQuadraticAbsorption ≡ false
quarticSchurDoesNotGiveFixedQuadraticAbsorption =
  R108.round108DirectGapWeightedQuarticSchurSuppliesFixedQuadraticAbsorptionIsFalse

unmaskedCancellationNotAutomatic :
  R108.round108AdverseMaskPreservesUnmaskedCancellationAutomatically ≡ false
unmaskedCancellationNotAutomatic =
  R108.round108AdverseMaskPreservesUnmaskedCancellationAutomaticallyIsFalse

selfPhaseMustNotBeRetaxed :
  R108.round108SelfPhaseMayBeTaxedAsArbitraryExternalForcing ≡ false
selfPhaseMustNotBeRetaxed =
  R108.round108SelfPhaseMayBeTaxedAsArbitraryExternalForcingIsFalse

externalCrossTriadPaymentStillOpen :
  R108.round108PhysicalExternalCrossTriadForcingRemainderPaymentClosed ≡ false
externalCrossTriadPaymentStillOpen =
  R108.round108PhysicalExternalCrossTriadForcingRemainderPaymentClosedIsFalse

------------------------------------------------------------------------
-- Implications for proof search.
------------------------------------------------------------------------

round510PreserveSignBeforeMajorizing : Bool
round510PreserveSignBeforeMajorizing = true

round510PhaseNetworkTimeGeometryIsLiveProducerFamily : Bool
round510PhaseNetworkTimeGeometryIsLiveProducerFamily = true

round510AbsoluteValueFirstIsPreferred : Bool
round510AbsoluteValueFirstIsPreferred = false

round510SearchSpaceStrictlyPruned : Bool
round510SearchSpaceStrictlyPruned = true

round510ClayPromotion : Bool
round510ClayPromotion = false

round510SearchSpaceStrictlyPrunedIsTrue : round510SearchSpaceStrictlyPruned ≡ true
round510SearchSpaceStrictlyPrunedIsTrue = refl

round510ClayPromotionIsFalse : round510ClayPromotion ≡ false
round510ClayPromotionIsFalse = refl
