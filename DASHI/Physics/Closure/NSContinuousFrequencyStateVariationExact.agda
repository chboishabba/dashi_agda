module DASHI.Physics.Closure.NSContinuousFrequencyStateVariationExact where

------------------------------------------------------------------------
-- A / CONTINUOUS FREQUENCY STATE VARIATION
--
-- The periodic R571 route may pay a state increment by discreteness.  Whole
-- space A has no lattice floor, so the corresponding exact object is the
-- line-segment identity
--
--   g(xi+h) - g(xi)
--     = integral_0^1 Dg(xi+t h)[h] dt.
--
-- This owner does not postulate that equality.  It obtains it from the
-- repository's existing Marx finite-factorisation derivative plus the existing
-- FundamentalTheoremBridge.  The only realization-specific input is the
-- factorisation of the selected scalar state along its literal frequency
-- segment and integrability of its derived function.
--
-- No periodic transport, lattice gap, finite difference, or Clay promotion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Analysis.MarxDifferentialCore as Marx
import DASHI.Analysis.MarxExteriorIntegration as Integral
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean

record ContinuousFrequencyStateVariation
    (A : Marx.MarxAlgebra)
    (R : Integral.RiemannIntegralStructure A)
    (FTC : Integral.FundamentalTheoremBridge R) : Set₁ where
  field
    center displacement : Euclidean.R3Frequency

    -- Concrete scalar observable restricted to t |-> xi + t h.
    segmentState : Marx.Function A
    segmentFactorisation : Marx.MarxFactorisation A segmentState

    parameterInterval : Integral.Interval A
    intervalStartsAtZero :
      Integral.leftEndpoint parameterInterval ≡ Marx.zero A
    intervalEndsAtOne :
      Integral.rightEndpoint parameterInterval ≡ Marx.one A

    derivativeIntegrable :
      Integral.IntegrableOn R parameterInterval
        (Marx.marxDerivative segmentFactorisation)

    stateAtCenter : Marx.Carrier A
    stateAtShiftedCenter : Marx.Carrier A

    stateAtCenterExact :
      segmentState (Marx.zero A) ≡ stateAtCenter

    stateAtShiftedCenterExact :
      segmentState (Marx.one A) ≡ stateAtShiftedCenter

open ContinuousFrequencyStateVariation public

segmentDerivativeIntegral :
  ∀ {A R FTC} →
  ContinuousFrequencyStateVariation A R FTC →
  Marx.Carrier A
segmentDerivativeIntegral {R = R} V =
  Integral.integral R
    (parameterInterval V)
    (Marx.marxDerivative (segmentFactorisation V))

segmentFundamentalTheoremRaw :
  ∀ {A R FTC}
    (V : ContinuousFrequencyStateVariation A R FTC) →
  segmentDerivativeIntegral V
  ≡
  Marx._-_ A
    (segmentState V (Integral.rightEndpoint (parameterInterval V)))
    (segmentState V (Integral.leftEndpoint (parameterInterval V)))
segmentFundamentalTheoremRaw {R = R} {FTC = FTC} V =
  Integral.integralOfDerivative FTC
    (parameterInterval V)
    (segmentState V)
    (segmentFactorisation V)
    (derivativeIntegrable V)

segmentStateIncrementExact :
  ∀ {A R FTC}
    (V : ContinuousFrequencyStateVariation A R FTC) →
  Marx._-_ A
    (stateAtShiftedCenter V)
    (stateAtCenter V)
  ≡
  segmentDerivativeIntegral V
segmentStateIncrementExact {A = A} V =
  let
    endpointDifference :
      Marx._-_ A
        (segmentState V (Integral.rightEndpoint (parameterInterval V)))
        (segmentState V (Integral.leftEndpoint (parameterInterval V)))
      ≡
      Marx._-_ A
        (stateAtShiftedCenter V)
        (stateAtCenter V)
    endpointDifference
      rewrite intervalStartsAtZero V
            | intervalEndsAtOne V
            | stateAtCenterExact V
            | stateAtShiftedCenterExact V = refl
  in
  sym
    (trans
      (segmentFundamentalTheoremRaw V)
      endpointDifference)

------------------------------------------------------------------------
-- The derivative appearing under the integral is the exact producer that a
-- weighted G2 estimate must control.  This keeps the order of operations:
--
-- derivative / directional geometry
--   -> integrate along frequency segment
--   -> state increment
--   -> signed second-moment recombination.
------------------------------------------------------------------------

continuousStateIncrementFromFTCClosed : Bool
continuousStateIncrementFromFTCClosed = true

continuousStateVariationUsesFiniteDifferenceShortcut : Bool
continuousStateVariationUsesFiniteDifferenceShortcut = false

continuousStateVariationUsesPeriodicGap : Bool
continuousStateVariationUsesPeriodicGap = false

weightedDerivativeMajorantClosedHere : Bool
weightedDerivativeMajorantClosedHere = false

clayPromotion : Bool
clayPromotion = false

continuousStateIncrementFromFTCClosedIsTrue :
  continuousStateIncrementFromFTCClosed ≡ true
continuousStateIncrementFromFTCClosedIsTrue = refl

continuousStateVariationUsesPeriodicGapIsFalse :
  continuousStateVariationUsesPeriodicGap ≡ false
continuousStateVariationUsesPeriodicGapIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
