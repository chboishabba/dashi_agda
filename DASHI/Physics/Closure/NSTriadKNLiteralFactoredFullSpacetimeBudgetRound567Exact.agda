module DASHI.Physics.Closure.NSTriadKNLiteralFactoredFullSpacetimeBudgetRound567Exact where

------------------------------------------------------------------------
-- ROUND567 / EXACT A1 CONSUMER: LIVE GLOBAL FACTORED-FULL SPACETIME BUDGET
--
-- R566 identifies the substantive direct leaf-A wall after finite algebra and
-- NS-specific temporal differentiation have been compiled away.  This module
-- freezes that wall on the literal R556/R557 live observable itself:
--
--   factoredFull(N,t)
--
-- is not replaceable by a norm proxy, heat surrogate, shell majorant, or
-- caller-selected commutator.  A producer must prove a cutoff-uniform integrated
-- upper bound for exactly this signed scalar.
--
-- The record intentionally asks only for the bound.  All same-object finite
-- structure upstream is compiler-owned by R541-R557.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNLiveIntegratedDiagonalReducedNormalFormRound557Exact as R557
import DASHI.Physics.Closure.NSTriadKNFactoredFullAnalyticFrontierRound566Exact as R566
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module ExactFactoredBudget
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Live = R557.LiveIntegrated
    Time initialTime integrateTo DerivativeOf integration

  record LiteralFactoredFullSpacetimeBudget567
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    constructor literal-factored-full-spacetime-budget-567
    field
      cutoffIndependentBound : Time → ℚ

      literalFactoredFullUpper :
        (cutoff : Nat) (terminal : Time) →
        integrateTo (Live.factoredFull T R cutoff) terminal
        ≤ cutoffIndependentBound terminal

  open LiteralFactoredFullSpacetimeBudget567 public

------------------------------------------------------------------------
-- BIDI / consumer audit.
------------------------------------------------------------------------

round567TargetIsLiteralR557FactoredFull : Bool
round567TargetIsLiteralR557FactoredFull = true

round567CallerSelectedReplacementObservableAllowed : Bool
round567CallerSelectedReplacementObservableAllowed = false

round567AbsoluteValueRequiredByConsumer : Bool
round567AbsoluteValueRequiredByConsumer = false

round567HeatLaplaceRepresentationRequiredByConsumer : Bool
round567HeatLaplaceRepresentationRequiredByConsumer = false

round567CutoffUniformityRequired : Bool
round567CutoffUniformityRequired = true

round567SignedSpacetimeUpperClosed : Bool
round567SignedSpacetimeUpperClosed = false

round567AfterScalarFTCResidualIsThisBudget :
  R566.afterScalarFTC566 ≡ R566.missingLiteralFactoredFullSpacetimeUpper566
round567AfterScalarFTCResidualIsThisBudget = refl

round567CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round567CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round567ClayPromotion : Bool
round567ClayPromotion = false

round567TargetIsLiteralR557FactoredFullIsTrue :
  round567TargetIsLiteralR557FactoredFull ≡ true
round567TargetIsLiteralR557FactoredFullIsTrue = refl

round567CallerSelectedReplacementObservableAllowedIsFalse :
  round567CallerSelectedReplacementObservableAllowed ≡ false
round567CallerSelectedReplacementObservableAllowedIsFalse = refl

round567HeatLaplaceRepresentationRequiredByConsumerIsFalse :
  round567HeatLaplaceRepresentationRequiredByConsumer ≡ false
round567HeatLaplaceRepresentationRequiredByConsumerIsFalse = refl

round567ClayPromotionIsFalse : round567ClayPromotion ≡ false
round567ClayPromotionIsFalse = refl
