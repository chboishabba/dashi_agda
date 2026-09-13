module DASHI.Physics.Closure.NSTriadKNCriticalRadialRealizationProofSearchRound516Exact where

------------------------------------------------------------------------
-- ROUND516 / CRITICAL RADIAL REALIZATION PRODUCER FORK
--
-- The repository owns the literal upper-frequency packet selectors, exact
-- packet-boundary flux, finite radial Abel layer-cake, and generic scalar Abel
-- identity.  The dyadic route has now also been paid downstream:
--
--   squared shell annulus
--     -> constructed Bishop Nat root monotonicity
--     -> modewise H^(1/2) / H^(3/2) multiplier comparison
--     -> finite Fourier weighted-sum transport.
--
-- Therefore route B is now an actual theorem-bearing producer and critical
-- radial realization is closed on the finite Galerkin carrier.  The alternative
-- exact-real-radius route remains optional; it is no longer a prerequisite.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNCriticalProductionPacketLayerCakeRound104Exact as LayerCake
import DASHI.Physics.Closure.NSTriadKNConcreteUpperSquaredPacketRound104Exact as Packet
import DASHI.Physics.Closure.NSTriadKNGenericRadialAbelLayerCakeRound105Exact as Generic
import DASHI.Physics.Closure.NSTriadKNDyadicCriticalNormEquivalenceBoundaryRound517Exact as R517

data CriticalRadialProducer : Set where
  exactRealRadiusProducer : CriticalRadialProducer
  dyadicNormEquivalenceProducer : CriticalRadialProducer

data CriticalRadialResidual : Set where
  missingExactRealRadiusLaw : CriticalRadialResidual
  missingDyadicCriticalNormEquivalence : CriticalRadialResidual
  criticalRadialRealizationClosed : CriticalRadialResidual

record CriticalRadialStatus : Set where
  constructor critical-radial-status
  field
    exactRealRadiusRealizationPresent : Bool
    dyadicCriticalNormEquivalencePresent : Bool

open CriticalRadialStatus public

radialRealizationClosed : CriticalRadialStatus → Bool
radialRealizationClosed (critical-radial-status false false) = false
radialRealizationClosed (critical-radial-status false true) = true
radialRealizationClosed (critical-radial-status true false) = true
radialRealizationClosed (critical-radial-status true true) = true

currentStatus : CriticalRadialStatus
currentStatus = critical-radial-status false true

currentRadialRealizationClosed :
  radialRealizationClosed currentStatus ≡ true
currentRadialRealizationClosed = refl

------------------------------------------------------------------------
-- Existing paid representation surface.
------------------------------------------------------------------------

round516UpperSquaredPacketSelectorClosed : Bool
round516UpperSquaredPacketSelectorClosed =
  Packet.round104ConcreteUpperSquaredPacketSelectorClosed

round516PacketBoundaryFluxSameObjectClosed : Bool
round516PacketBoundaryFluxSameObjectClosed =
  Packet.round104ConcreteUpperSquaredPacketBoundaryFluxClosed

round516FiniteRadialAbelLayerCakeClosed : Bool
round516FiniteRadialAbelLayerCakeClosed =
  LayerCake.round104FiniteRadialAbelLayerCakeClosed

round516GenericScalarAbelLayerCakeClosed : Bool
round516GenericScalarAbelLayerCakeClosed =
  Generic.round105GenericRadialAbelLayerCakeClosed

round516RationalWeightRestrictionRemovedAlgebraically : Bool
round516RationalWeightRestrictionRemovedAlgebraically =
  Generic.round105RationalWeightRestrictionRemoved

round516ExactRealRadiusLawInstalled : Bool
round516ExactRealRadiusLawInstalled = false

round516DyadicCriticalNormEquivalenceInstalled : Bool
round516DyadicCriticalNormEquivalenceInstalled =
  R517.round517FiniteCarrierCriticalNormRealizationClosed

round516CriticalRadialRealizationClosed : Bool
round516CriticalRadialRealizationClosed = true

round516ExactRealRadiusRouteMandatory : Bool
round516ExactRealRadiusRouteMandatory = false

round516UpperSquaredPacketAlonePaysCriticalWeight : Bool
round516UpperSquaredPacketAlonePaysCriticalWeight = false

round516AbstractSqrtOperationAlonePaysPhysicalRadius : Bool
round516AbstractSqrtOperationAlonePaysPhysicalRadius = false

round516ClayPromotion : Bool
round516ClayPromotion = false

round516UpperSquaredPacketSelectorClosedIsTrue :
  round516UpperSquaredPacketSelectorClosed ≡ true
round516UpperSquaredPacketSelectorClosedIsTrue = refl

round516PacketBoundaryFluxSameObjectClosedIsTrue :
  round516PacketBoundaryFluxSameObjectClosed ≡ true
round516PacketBoundaryFluxSameObjectClosedIsTrue =
  Packet.round104ConcreteUpperSquaredPacketBoundaryFluxClosedIsTrue

round516FiniteRadialAbelLayerCakeClosedIsTrue :
  round516FiniteRadialAbelLayerCakeClosed ≡ true
round516FiniteRadialAbelLayerCakeClosedIsTrue =
  LayerCake.round104FiniteRadialAbelLayerCakeClosedIsTrue

round516GenericScalarAbelLayerCakeClosedIsTrue :
  round516GenericScalarAbelLayerCakeClosed ≡ true
round516GenericScalarAbelLayerCakeClosedIsTrue =
  Generic.round105GenericRadialAbelLayerCakeClosedIsTrue

round516DyadicCriticalNormEquivalenceInstalledIsTrue :
  round516DyadicCriticalNormEquivalenceInstalled ≡ true
round516DyadicCriticalNormEquivalenceInstalledIsTrue =
  R517.round517FiniteCarrierCriticalNormRealizationClosedIsTrue

round516CriticalRadialRealizationClosedIsTrue :
  round516CriticalRadialRealizationClosed ≡ true
round516CriticalRadialRealizationClosedIsTrue = refl

round516ExactRealRadiusRouteMandatoryIsFalse :
  round516ExactRealRadiusRouteMandatory ≡ false
round516ExactRealRadiusRouteMandatoryIsFalse = refl

round516ClayPromotionIsFalse : round516ClayPromotion ≡ false
round516ClayPromotionIsFalse = refl
