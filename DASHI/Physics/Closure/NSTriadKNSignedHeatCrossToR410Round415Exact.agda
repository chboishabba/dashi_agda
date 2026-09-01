module DASHI.Physics.Closure.NSTriadKNSignedHeatCrossToR410Round415Exact where

------------------------------------------------------------------------
-- ROUND415 / PRESERVE R299'S SIGNED HEAT CROSS ALL THE WAY TO R410
--
-- R299 already identifies the finite pair remainder, BEFORE norms, as
--
--   4 Re < sum_a w_a A_a , sum_b w_b F_b >.
--
-- The failed Wiener route destroys this structure by majorising that pairing
-- cellwise.  The correct highest-alpha consumer is therefore an integrated
-- bound on the SAME signed aggregate cross.  This round freezes the exact
-- compiler from such a bound to R410's literal R406 remainder budget.
--
-- The only non-algebraic same-object payment requested here is the equality
-- between the integrated R406 remainder and four times the integrated signed
-- R299 aggregate cross.  Once that equality and a cutoff-uniform cross bound
-- are supplied, R410 follows with no l1/Wiener majorisation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNSignedTTStarCriticalCancellationTargetRound410Exact as R410

F : C3.RealField _
F = Rational.rationalRealField

module SignedHeatCross
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Flux = R406.FixedLiveFlux
    Time initialTime integrateTo DerivativeOf
  module Target = R410.Target
    Time initialTime integrateTo DerivativeOf

  literalRemainderIntegral :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  literalRemainderIntegral T R cutoff terminal =
    integrateTo
      (λ time → Flux.At.weightedRemainder T R cutoff time)
      terminal

  record IntegratedSignedHeatCrossPayment
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      integratedSignedAggregateCross : Nat → Time → ℚ
      cutoffIndependentCrossBound : Time → ℚ

      literalR406RemainderIsFourSignedCross :
        (cutoff : Nat) (terminal : Time) →
        literalRemainderIntegral T R cutoff terminal
        ≡ R299.four * integratedSignedAggregateCross cutoff terminal

      signedCrossBudget :
        (cutoff : Nat) (terminal : Time) →
        R299.four * integratedSignedAggregateCross cutoff terminal
        ≤ cutoffIndependentCrossBound terminal

  open IntegratedSignedHeatCrossPayment public

  signedHeatCrossBuildsR410 :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    IntegratedSignedHeatCrossPayment T R →
    Target.SignedCriticalCancellation T R
  signedHeatCrossBuildsR410 T R P = record
    { Target.cutoffIndependentRemainderBound = cutoffIndependentCrossBound P
    ; Target.signedRemainderBudget = λ cutoff terminal →
        subst
          (λ x → x ≤ cutoffIndependentCrossBound P terminal)
          (sym (literalR406RemainderIsFourSignedCross P cutoff terminal))
          (signedCrossBudget P cutoff terminal)
    }

round415R299PreNormSignedFactorizationReused : Bool
round415R299PreNormSignedFactorizationReused =
  R299.round299FinitePairFactorizationCompilerClosed

round415FinalWienerMajorizationRequired : Bool
round415FinalWienerMajorizationRequired = false

round415R410ReducedToSignedCrossBudget : Bool
round415R410ReducedToSignedCrossBudget = true

round415RemainingNovelLeafIsSignedCrossEstimate : Bool
round415RemainingNovelLeafIsSignedCrossEstimate = true

round415FinalWienerMajorizationRequiredIsFalse :
  round415FinalWienerMajorizationRequired ≡ false
round415FinalWienerMajorizationRequiredIsFalse = refl

round415R410ReducedToSignedCrossBudgetIsTrue :
  round415R410ReducedToSignedCrossBudget ≡ true
round415R410ReducedToSignedCrossBudgetIsTrue = refl
