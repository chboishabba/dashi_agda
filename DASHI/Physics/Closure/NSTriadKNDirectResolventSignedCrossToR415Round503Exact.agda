module DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact where

------------------------------------------------------------------------
-- ROUND503 / DIRECT OFF-DIAGONAL RESOLVENT SIGNED CROSS -> R415
--
-- R500 proves, on the literal R406 live carrier and conditional only on a
-- standard integration-transport authority,
--
--   literalR406RemainderIntegral(N,T)
--     = 4 * integratedDirectCompanion(N,T).
--
-- R415 is the exact consumer of precisely this same-object signed-cross
-- payment.  Therefore no full R439 square companion, diagonal correction,
-- Laplace factorization, R487 decomposition, or R423 naming field is needed.
--
-- The only genuinely analytic field below is the cutoff-uniform upper bound
-- on the exact integrated off-diagonal direct resolvent cross.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossToR410Round415Exact as R415
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact as R500

F : C3.RealField _
F = Rational.rationalRealField

module DirectSignedCross
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
  module Heat = R415.SignedHeatCross
    Time initialTime integrateTo DerivativeOf
  module Direct = R500.IntegratedDirect
    Time initialTime integrateTo DerivativeOf integration

  record DirectOffDiagonalBudget
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      cutoffIndependentBound : Time → ℚ
      directOffDiagonalBudget :
        (cutoff : Nat) (terminal : Time) →
        R299.four * Direct.integratedDirectCompanion T R cutoff terminal
        ≤ cutoffIndependentBound terminal

  open DirectOffDiagonalBudget public

  directBudgetBuildsR415 :
    ∀ {T R} →
    DirectOffDiagonalBudget T R →
    Heat.IntegratedSignedHeatCrossPayment T R
  directBudgetBuildsR415 {T} {R} P = record
    { Heat.integratedSignedAggregateCross =
        Direct.integratedDirectCompanion T R
    ; Heat.cutoffIndependentCrossBound = cutoffIndependentBound P
    ; Heat.literalR406RemainderIsFourSignedCross =
        Direct.literalR406IntegralIsFourIntegratedDirectCompanion T R
    ; Heat.signedCrossBudget = directOffDiagonalBudget P
    }

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

round503ExactR500ToR415CompilerClosed : Bool
round503ExactR500ToR415CompilerClosed = true

round503FullR439CompanionRequired : Bool
round503FullR439CompanionRequired = false

round503R423Required : Bool
round503R423Required = false

round503LaplaceRequired : Bool
round503LaplaceRequired = false

round503RemainingNovelLeafIsDirectOffDiagonalBudget : Bool
round503RemainingNovelLeafIsDirectOffDiagonalBudget = true

round503DirectOffDiagonalBudgetClosed : Bool
round503DirectOffDiagonalBudgetClosed = false

round503ClayPromotion : Bool
round503ClayPromotion = false

round503ExactR500ToR415CompilerClosedIsTrue :
  round503ExactR500ToR415CompilerClosed ≡ true
round503ExactR500ToR415CompilerClosedIsTrue = refl

round503FullR439CompanionRequiredIsFalse :
  round503FullR439CompanionRequired ≡ false
round503FullR439CompanionRequiredIsFalse = refl

round503R423RequiredIsFalse : round503R423Required ≡ false
round503R423RequiredIsFalse = refl

round503ClayPromotionIsFalse : round503ClayPromotion ≡ false
round503ClayPromotionIsFalse = refl
