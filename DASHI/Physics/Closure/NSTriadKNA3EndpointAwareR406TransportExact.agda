module DASHI.Physics.Closure.NSTriadKNA3EndpointAwareR406TransportExact where

------------------------------------------------------------------------
-- A3 -> R406 / ENDPOINT-AWARE CONSUMER TRANSPORT
--
-- The preferred A3 payment is an instantaneous signed coherent-covariance
-- payment.  The d1b0/d1b1 consumer is not pointwise: d1b0 isolates the
-- coherent covariance from the tangent/endpoint contribution, while d1b1
-- pays that tangent contribution only after time integration by ordinary FTC.
--
-- Therefore the least-privilege A3 -> R406 interface lives at spacetime level:
--
--   integral R406
--     = endpoint contribution
--       + integral (4 * signed coherent covariance family)
--
-- followed by:
--
--   signed covariance family <= residual budgets          (A3)
--   endpoint + integrated residual budgets <= global cap  (consumer budget)
--
-- No direct instantaneous equality
--
--   R406.weightedRemainder = signed covariance
--
-- is requested or implied here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossToR410Round415Exact as R415
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact as R500
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
import DASHI.Physics.Closure.NSTriadKNSignedRateVectorPaymentToR503Exact as A3

F : C3.RealField _
F = Rational.rationalRealField

module EndpointAware
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Dyn = R240.PhysicalNSDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Heat = R415.SignedHeatCross
    Time initialTime integrateTo DerivativeOf
  module Direct = R500.IntegratedDirect
    Time initialTime integrateTo DerivativeOf integration
  module DirectBudget = R503.DirectSignedCross
    Time initialTime integrateTo DerivativeOf integration
  module Core = A3.GlobalCompiler
    Time initialTime integrateTo DerivativeOf integration
  module Local = A3.LiveA3
    Time initialTime integrateTo DerivativeOf

  ----------------------------------------------------------------------
  -- d1b0+d1b1 consumer boundary.
  --
  -- endpointContribution is intentionally explicit.  The equality below is
  -- the SAME-object transport that must be supplied by the coherent-work split
  -- plus the literal endpoint/FTC compiler; it is not a nonlinear estimate.
  ----------------------------------------------------------------------

  record EndpointAwareA3SpacetimeProducer
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      familyAt :
        (cutoff : Nat) (time : Time) →
        Local.CanonicalLivePaymentFamily T R cutoff time

      endpointContribution :
        Nat → Time → ℚ

      literalR406IntegralIsEndpointPlusA3 :
        (cutoff : Nat) (terminal : Time) →
        Heat.literalRemainderIntegral T R cutoff terminal
        ≡
        endpointContribution cutoff terminal
        +
        integrateTo
          (λ time →
            R299.four
              * Local.sumSignedRateVectorPayment
                  (familyAt cutoff time))
          terminal

      cutoffIndependentBound : Time → ℚ

      endpointAndResidualBudgetsPaid :
        (cutoff : Nat) (terminal : Time) →
        endpointContribution cutoff terminal
        +
        integrateTo
          (λ time →
            R299.four
              * Local.sumResidualBudgets
                  (familyAt cutoff time))
          terminal
        ≤ cutoffIndependentBound terminal

  open EndpointAwareA3SpacetimeProducer public

  ----------------------------------------------------------------------
  -- A3 itself supplies the only signed nonlinear inequality used here.
  ----------------------------------------------------------------------

  integratedA3SignedBelowResidual :
    (orderIntegration : A3.IntegrationOrderAuthority Time integrateTo) →
    ∀ {T R} →
    (P : EndpointAwareA3SpacetimeProducer T R) →
    (cutoff : Nat) (terminal : Time) →
    integrateTo
      (λ time →
        R299.four
          * Local.sumSignedRateVectorPayment
              (familyAt P cutoff time))
      terminal
    ≤
    integrateTo
      (λ time →
        R299.four
          * Local.sumResidualBudgets
              (familyAt P cutoff time))
      terminal
  integratedA3SignedBelowResidual orderIntegration P cutoff terminal =
    A3.integrateMonotone orderIntegration
      (λ time →
        R299.four
          * Local.sumSignedRateVectorPayment
              (familyAt P cutoff time))
      (λ time →
        R299.four
          * Local.sumResidualBudgets
              (familyAt P cutoff time))
      (λ time →
        Core.fourTimesMonotone
          (Local.liveA3FamilySumWithoutOutputCardinalityFactor
            (familyAt P cutoff time)))
      terminal

  endpointAwareLiteralRemainderUpper :
    (orderIntegration : A3.IntegrationOrderAuthority Time integrateTo) →
    ∀ {T R} →
    (P : EndpointAwareA3SpacetimeProducer T R) →
    (cutoff : Nat) (terminal : Time) →
    Heat.literalRemainderIntegral T R cutoff terminal
    ≤ cutoffIndependentBound P terminal
  endpointAwareLiteralRemainderUpper orderIntegration P cutoff terminal =
    let
      signedBelowResidual =
        integratedA3SignedBelowResidual
          orderIntegration P cutoff terminal

      withEndpoint :
        endpointContribution P cutoff terminal
        +
        integrateTo
          (λ time →
            R299.four
              * Local.sumSignedRateVectorPayment
                  (familyAt P cutoff time))
          terminal
        ≤
        endpointContribution P cutoff terminal
        +
        integrateTo
          (λ time →
            R299.four
              * Local.sumResidualBudgets
                  (familyAt P cutoff time))
          terminal
      withEndpoint =
        ℚP.+-mono-≤ ℚP.≤-refl signedBelowResidual

      transported :
        Heat.literalRemainderIntegral T R cutoff terminal
        ≤
        endpointContribution P cutoff terminal
        +
        integrateTo
          (λ time →
            R299.four
              * Local.sumResidualBudgets
                  (familyAt P cutoff time))
          terminal
      transported =
        subst
          (λ lower →
            lower
            ≤
            endpointContribution P cutoff terminal
            +
            integrateTo
              (λ time →
                R299.four
                  * Local.sumResidualBudgets
                      (familyAt P cutoff time))
              terminal)
          (sym (literalR406IntegralIsEndpointPlusA3 P cutoff terminal))
          withEndpoint
    in
    ℚP.≤-trans transported
      (endpointAndResidualBudgetsPaid P cutoff terminal)

  endpointAwareA3BuildsDirectOffDiagonalBudget :
    (orderIntegration : A3.IntegrationOrderAuthority Time integrateTo) →
    ∀ {T R} →
    EndpointAwareA3SpacetimeProducer T R →
    DirectBudget.DirectOffDiagonalBudget T R
  endpointAwareA3BuildsDirectOffDiagonalBudget
      orderIntegration {T} {R} P = record
    { DirectBudget.cutoffIndependentBound =
        cutoffIndependentBound P
    ; DirectBudget.directOffDiagonalBudget =
        λ cutoff terminal →
          subst
            (λ lhs → lhs ≤ cutoffIndependentBound P terminal)
            (Direct.literalR406IntegralIsFourIntegratedDirectCompanion
              T R cutoff terminal)
            (endpointAwareLiteralRemainderUpper
              orderIntegration P cutoff terminal)
    }

------------------------------------------------------------------------
-- Status / fail-closed routing.
------------------------------------------------------------------------

endpointAwareConsumerTransportTypeConstructed : Bool
endpointAwareConsumerTransportTypeConstructed = true

preferredPointwiseR406AttachmentRequired : Bool
preferredPointwiseR406AttachmentRequired = false

endpointTermExplicitInPreferredTransport : Bool
endpointTermExplicitInPreferredTransport = true

newNonlinearEstimateIntroducedByConsumerTransport : Bool
newNonlinearEstimateIntroducedByConsumerTransport = false

d1b0d1b1SameObjectTransportStillProofBearing : Bool
d1b0d1b1SameObjectTransportStillProofBearing = true

a3QuantitativeSignedPaymentStillProofBearing : Bool
a3QuantitativeSignedPaymentStillProofBearing = true

endpointAwareConsumerTransportTypeConstructedIsTrue :
  endpointAwareConsumerTransportTypeConstructed ≡ true
endpointAwareConsumerTransportTypeConstructedIsTrue = refl

preferredPointwiseR406AttachmentRequiredIsFalse :
  preferredPointwiseR406AttachmentRequired ≡ false
preferredPointwiseR406AttachmentRequiredIsFalse = refl

endpointTermExplicitInPreferredTransportIsTrue :
  endpointTermExplicitInPreferredTransport ≡ true
endpointTermExplicitInPreferredTransportIsTrue = refl

newNonlinearEstimateIntroducedByConsumerTransportIsFalse :
  newNonlinearEstimateIntroducedByConsumerTransport ≡ false
newNonlinearEstimateIntroducedByConsumerTransportIsFalse = refl

d1b0d1b1SameObjectTransportStillProofBearingIsTrue :
  d1b0d1b1SameObjectTransportStillProofBearing ≡ true
d1b0d1b1SameObjectTransportStillProofBearingIsTrue = refl

a3QuantitativeSignedPaymentStillProofBearingIsTrue :
  a3QuantitativeSignedPaymentStillProofBearing ≡ true
a3QuantitativeSignedPaymentStillProofBearingIsTrue = refl
