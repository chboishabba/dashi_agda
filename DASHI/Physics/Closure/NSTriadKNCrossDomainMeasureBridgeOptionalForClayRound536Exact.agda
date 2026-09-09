module DASHI.Physics.Closure.NSTriadKNCrossDomainMeasureBridgeOptionalForClayRound536Exact where

------------------------------------------------------------------------
-- ROUND536 / CROSS-DOMAIN MEASURE TRANSPORT IS OPTIONAL FOR CLAY R406
--
-- R535 specifies the exact theorem-bearing direct rich-carrier consumer:
--
--   measure bridge -> cutoff correspondence -> literal R406 weld
--                  -> cutoff-uniform constant transport.
--
-- This owner adds two dependency corrections without changing that consumer:
--
--  (1) periodization/Poisson, scaled-lattice Riemann limits, and externally
--      sourced normalizations are ALTERNATIVE PRODUCER FAMILIES for the same
--      missing measure theorem. Choosing one is proof-search metadata, not a
--      new theorem prerequisite.
--
--  (2) Clay C/D retain distinct domain envelopes. A domain-specific literal
--      R406 proof need not first transport itself to the other domain. Thus the
--      whole cross-domain lane is useful strengthening/reuse, but optional for
--      the shortest Clay route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNLiteralR406LatticeContinuumTransportConsumerRound535Exact as Consumer
import DASHI.Physics.Closure.NSTriadKNClayCDDomainResidualBidiRound527Exact as R527
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

------------------------------------------------------------------------
-- 1. Alternative producer families for ONE existing measure residual.
------------------------------------------------------------------------

data MeasureBridgeProducerFamily536 : Set where
  periodizationPoisson536 : MeasureBridgeProducerFamily536
  scaledLatticeRiemannLimit536 : MeasureBridgeProducerFamily536
  externallySourcedNormalization536 : MeasureBridgeProducerFamily536

-- A raw lattice sum and raw continuum integral are not identified by carrier
-- names alone. Any inhabitant of Consumer.SpectralMeasureBridge535 must carry
-- its own same-observable transport theorem.
data BareSumIntegralIdentityPermission536 : Set where

bareSumIntegralIdentityNotAutomatic536 :
  BareSumIntegralIdentityPermission536 → ⊥
bareSumIntegralIdentityNotAutomatic536 ()

------------------------------------------------------------------------
-- 2. Canonical theorem residual is inherited exactly from the direct consumer.
------------------------------------------------------------------------

currentCrossDomainResidual536 : Consumer.DirectTransportResidual535
currentCrossDomainResidual536 = Consumer.currentDirectTransportResidual535

currentCrossDomainResidualIsMeasureBridge536 :
  currentCrossDomainResidual536 ≡ Consumer.missingDirectSpectralMeasureBridge535
currentCrossDomainResidualIsMeasureBridge536 = refl

currentCrossDomainProducer536 : Consumer.DirectTransportProducer535
currentCrossDomainProducer536 = Consumer.currentDirectTransportProducer535

currentCrossDomainProducerIsMeasureBridge536 :
  currentCrossDomainProducer536 ≡ Consumer.proveRichCarrierMeasureBridge535
currentCrossDomainProducerIsMeasureBridge536 = refl

------------------------------------------------------------------------
-- 3. Dependency firewall: cross-domain transport is not a domain-specific Clay
-- prerequisite.
------------------------------------------------------------------------

data CrossDomainTransportRequiredForDomainSpecificR406Permission536 : Set where

crossDomainTransportDoesNotGateDomainSpecificR406536 :
  CrossDomainTransportRequiredForDomainSpecificR406Permission536 → ⊥
crossDomainTransportDoesNotGateDomainSpecificR406536 ()

round536ClayDomainResidualRetained : Bool
round536ClayDomainResidualRetained = R527.round527DomainResidualRetained

round536DirectRichCarrierMeasureConsumerSpecified : Bool
round536DirectRichCarrierMeasureConsumerSpecified =
  Consumer.round535DirectRichCarrierConsumerSpecified

round536DirectMeasureBridgeClosed : Bool
round536DirectMeasureBridgeClosed = Consumer.round535DirectSpectralMeasureBridgeClosed

round536CrossDomainTransportMandatoryForClay : Bool
round536CrossDomainTransportMandatoryForClay = false

round536BareSumIntegralEqualityClaimed : Bool
round536BareSumIntegralEqualityClaimed = false

------------------------------------------------------------------------
-- 4. Global Clay frontier remains exactly the literal R406 signed-cross payment.
------------------------------------------------------------------------

round536LiveR406ResidualStillFirst :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round536LiveR406ResidualStillFirst = R504.currentFirstTerminalResidual

round536ClayPromotion : Bool
round536ClayPromotion = false

round536DirectRichCarrierMeasureConsumerSpecifiedIsTrue :
  round536DirectRichCarrierMeasureConsumerSpecified ≡ true
round536DirectRichCarrierMeasureConsumerSpecifiedIsTrue =
  Consumer.round535DirectRichCarrierConsumerSpecifiedIsTrue

round536DirectMeasureBridgeClosedIsFalse :
  round536DirectMeasureBridgeClosed ≡ false
round536DirectMeasureBridgeClosedIsFalse = refl

round536CrossDomainTransportMandatoryForClayIsFalse :
  round536CrossDomainTransportMandatoryForClay ≡ false
round536CrossDomainTransportMandatoryForClayIsFalse = refl

round536BareSumIntegralEqualityClaimedIsFalse :
  round536BareSumIntegralEqualityClaimed ≡ false
round536BareSumIntegralEqualityClaimedIsFalse = refl

round536ClayPromotionIsFalse : round536ClayPromotion ≡ false
round536ClayPromotionIsFalse = refl
