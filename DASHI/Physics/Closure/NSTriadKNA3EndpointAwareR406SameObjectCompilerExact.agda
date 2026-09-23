{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNA3EndpointAwareR406SameObjectCompilerExact where

------------------------------------------------------------------------
-- ENDPOINT-AWARE A3 / POINTWISE SAME-OBJECT SPLIT -> INTEGRATED R406
--
-- The current EndpointAwareA3SpacetimeProducer stores the integrated identity
--
--   integral R406
--     = endpointContribution + integral (4 * signed A3 family)
--
-- as a proof-bearing field.
--
-- This module removes that unnecessary integrated interface.  It shows that
-- ordinary integration transport plus:
--
--   (i)  a POINTWISE same-object split of the literal R406 density, and
--   (ii) the endpoint identity for the tangent density,
--
-- compile the integrated equality automatically.
--
-- Thus the remaining consumer weld is representation-level:
--
--   literal R406 weighted density
--     = endpointDensity + 4 * A3 signed density.
--
-- No nonlinear estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNSignedRateVectorPaymentToR503Exact as A3
import DASHI.Physics.Closure.NSTriadKNA3EndpointAwareR406TransportExact as EndpointAware

------------------------------------------------------------------------
-- Generic scalar compiler.
------------------------------------------------------------------------

module Scalar
    (Time : Set)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  record PointwiseEndpointSplit : Set₁ where
    field
      literalDensity : Nat → Time → ℚ
      endpointDensity : Nat → Time → ℚ
      residualDensity : Nat → Time → ℚ
      endpointContribution : Nat → Time → ℚ

      pointwiseSplit :
        (cutoff : Nat) (time : Time) →
        literalDensity cutoff time
        ≡ endpointDensity cutoff time + residualDensity cutoff time

      endpointFTC :
        (cutoff : Nat) (terminal : Time) →
        integrateTo (endpointDensity cutoff) terminal
        ≡ endpointContribution cutoff terminal

  open PointwiseEndpointSplit public

  integratedEndpointSplit :
    (P : PointwiseEndpointSplit) →
    (cutoff : Nat) (terminal : Time) →
    integrateTo (literalDensity P cutoff) terminal
    ≡
    endpointContribution P cutoff terminal
      + integrateTo (residualDensity P cutoff) terminal
  integratedEndpointSplit P cutoff terminal =
    trans
      (R495.integrateCongruent integration
        (literalDensity P cutoff)
        (λ time →
          endpointDensity P cutoff time
            + residualDensity P cutoff time)
        (pointwiseSplit P cutoff)
        terminal)
      (trans
        (R495.integrateAdd integration
          (endpointDensity P cutoff)
          (residualDensity P cutoff)
          terminal)
        (cong
          (λ endpoint →
            endpoint + integrateTo (residualDensity P cutoff) terminal)
          (endpointFTC P cutoff terminal)))

------------------------------------------------------------------------
-- Live A3 specialization.
------------------------------------------------------------------------

module Live
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier.Complex3
        DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2.rationalRealField) →
      (Time → DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier.Complex3
        DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2.rationalRealField) →
      Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Dyn = R240.PhysicalNSDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Local = A3.LiveA3
    Time initialTime integrateTo DerivativeOf
  module Existing = EndpointAware.EndpointAware
    Time initialTime integrateTo DerivativeOf integration
  module ScalarCompiler = Scalar Time integrateTo integration

  ----------------------------------------------------------------------
  -- Refined producer: pointwise representation + endpoint FTC.
  ----------------------------------------------------------------------

  record PointwiseEndpointAwareA3SpacetimeProducer
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      familyAt :
        (cutoff : Nat) (time : Time) →
        Local.CanonicalLivePaymentFamily T R cutoff time

      endpointDensity :
        Nat → Time → ℚ

      endpointContribution :
        Nat → Time → ℚ

      -- This is now the exact same-object representation seam.  It should be
      -- constructed from the literal R406 weighted normal form plus d1b0.
      literalR406PointwiseIsEndpointPlusA3 :
        (cutoff : Nat) (time : Time) →
        Local.Direct499.Flux.At.weightedRemainder T R cutoff time
        ≡
        endpointDensity cutoff time
          + R299.four * Local.sumSignedRateVectorPayment
              (familyAt cutoff time)

      -- d1b1 / ordinary scalar FTC owns this coordinate once endpointDensity
      -- is identified with its actual fixed-output tangent-work sum.
      endpointDensityFTC :
        (cutoff : Nat) (terminal : Time) →
        integrateTo (endpointDensity cutoff) terminal
        ≡ endpointContribution cutoff terminal

      cutoffIndependentBound : Time → ℚ

      endpointAndResidualBudgetsPaid :
        (cutoff : Nat) (terminal : Time) →
        endpointContribution cutoff terminal
          + integrateTo
              (λ time →
                R299.four * Local.sumResidualBudgets
                  (familyAt cutoff time))
              terminal
        ≤ cutoffIndependentBound terminal

  open PointwiseEndpointAwareA3SpacetimeProducer public

  asScalarPointwiseSplit :
    ∀ {T R} →
    PointwiseEndpointAwareA3SpacetimeProducer T R →
    ScalarCompiler.PointwiseEndpointSplit
  asScalarPointwiseSplit {T} {R} P = record
    { ScalarCompiler.PointwiseEndpointSplit.literalDensity =
        λ cutoff time →
          Local.Direct499.Flux.At.weightedRemainder T R cutoff time
    ; ScalarCompiler.PointwiseEndpointSplit.endpointDensity =
        endpointDensity P
    ; ScalarCompiler.PointwiseEndpointSplit.residualDensity =
        λ cutoff time →
          R299.four * Local.sumSignedRateVectorPayment
            (familyAt P cutoff time)
    ; ScalarCompiler.PointwiseEndpointSplit.endpointContribution =
        endpointContribution P
    ; ScalarCompiler.PointwiseEndpointSplit.pointwiseSplit =
        literalR406PointwiseIsEndpointPlusA3 P
    ; ScalarCompiler.PointwiseEndpointSplit.endpointFTC =
        endpointDensityFTC P
    }

  literalR406IntegralIsEndpointPlusA3 :
    ∀ {T R} →
    (P : PointwiseEndpointAwareA3SpacetimeProducer T R) →
    (cutoff : Nat) (terminal : Time) →
    integrateTo
      (λ time →
        Local.Direct499.Flux.At.weightedRemainder T R cutoff time)
      terminal
    ≡
    endpointContribution P cutoff terminal
      + integrateTo
          (λ time →
            R299.four * Local.sumSignedRateVectorPayment
              (familyAt P cutoff time))
          terminal
  literalR406IntegralIsEndpointPlusA3 P =
    ScalarCompiler.integratedEndpointSplit (asScalarPointwiseSplit P)

  asEndpointAwareProducer :
    ∀ {T R} →
    PointwiseEndpointAwareA3SpacetimeProducer T R →
    Existing.EndpointAwareA3SpacetimeProducer T R
  asEndpointAwareProducer P = record
    { Existing.EndpointAwareA3SpacetimeProducer.familyAt =
        familyAt P
    ; Existing.EndpointAwareA3SpacetimeProducer.endpointContribution =
        endpointContribution P
    ; Existing.EndpointAwareA3SpacetimeProducer.literalR406IntegralIsEndpointPlusA3 =
        literalR406IntegralIsEndpointPlusA3 P
    ; Existing.EndpointAwareA3SpacetimeProducer.cutoffIndependentBound =
        cutoffIndependentBound P
    ; Existing.EndpointAwareA3SpacetimeProducer.endpointAndResidualBudgetsPaid =
        endpointAndResidualBudgetsPaid P
    }

------------------------------------------------------------------------
-- Status / frontier reduction.
------------------------------------------------------------------------

integratedR406EndpointIdentityCompilerClosed : Bool
integratedR406EndpointIdentityCompilerClosed = true

arbitraryIntegratedR406EqualityRequired : Bool
arbitraryIntegratedR406EqualityRequired = false

pointwiseR406WeightedToEndpointPlusA3WeldStillProofBearing : Bool
pointwiseR406WeightedToEndpointPlusA3WeldStillProofBearing = true

endpointFTCStillSeparateNonlinearEstimate : Bool
endpointFTCStillSeparateNonlinearEstimate = false

a3QuantitativeSignedPaymentStillProofBearing : Bool
a3QuantitativeSignedPaymentStillProofBearing = true

integratedR406EndpointIdentityCompilerClosedIsTrue :
  integratedR406EndpointIdentityCompilerClosed ≡ true
integratedR406EndpointIdentityCompilerClosedIsTrue = refl

arbitraryIntegratedR406EqualityRequiredIsFalse :
  arbitraryIntegratedR406EqualityRequired ≡ false
arbitraryIntegratedR406EqualityRequiredIsFalse = refl

pointwiseR406WeightedToEndpointPlusA3WeldStillProofBearingIsTrue :
  pointwiseR406WeightedToEndpointPlusA3WeldStillProofBearing ≡ true
pointwiseR406WeightedToEndpointPlusA3WeldStillProofBearingIsTrue = refl

endpointFTCStillSeparateNonlinearEstimateIsFalse :
  endpointFTCStillSeparateNonlinearEstimate ≡ false
endpointFTCStillSeparateNonlinearEstimateIsFalse = refl

a3QuantitativeSignedPaymentStillProofBearingIsTrue :
  a3QuantitativeSignedPaymentStillProofBearing ≡ true
a3QuantitativeSignedPaymentStillProofBearingIsTrue = refl
