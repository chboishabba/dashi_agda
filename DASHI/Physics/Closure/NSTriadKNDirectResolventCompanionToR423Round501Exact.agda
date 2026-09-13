module DASHI.Physics.Closure.NSTriadKNDirectResolventCompanionToR423Round501Exact where

------------------------------------------------------------------------
-- ROUND501 / DIRECT NONSEPARABLE RESOLVENT COMPANION -> R423
--
-- R500 constructs the literal integrated direct companion on the R406 carrier
-- and proves
--
--   literalR406RemainderIntegral = 4 * integratedDirectCompanion.
--
-- Therefore the Clay-facing R423 record needs only one genuinely analytic
-- theorem on this producer route:
--
--   4 * integratedDirectCompanion(N,T) <= B(T), uniformly in N.
--
-- This compiler does not require the R487 fixed-output budget decomposition,
-- R492 external naming weld, Laplace factorization, Schur/Wiener majorization,
-- or cross-output coherence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNQuadraticCompanionSignedHeatToBarrierRound423Exact as R423
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact as R500

F : C3.RealField _
F = Rational.rationalRealField

module DirectToR423
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
  module Direct = R500.IntegratedDirect
    Time initialTime integrateTo DerivativeOf integration
  module Clay = R423.QuadraticCompanionBarrier
    Time initialTime integrateTo DerivativeOf

  record DirectResolventCompanionBudget
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      cutoffIndependentCompanionBound : Time → ℚ
      directCompanionBudget :
        (cutoff : Nat) (terminal : Time) →
        R299.four * Direct.integratedDirectCompanion T R cutoff terminal
        ≤ cutoffIndependentCompanionBound terminal

  open DirectResolventCompanionBudget public

  directBudgetBuildsR423 :
    ∀ {T R} →
    DirectResolventCompanionBudget T R →
    Clay.QuadraticCompanionSignedPayment T R
  directBudgetBuildsR423 {T} {R} P = record
    { Clay.integratedQuadraticCompanionCross =
        Direct.integratedDirectCompanion T R
    ; Clay.cutoffIndependentCompanionBound =
        cutoffIndependentCompanionBound P
    ; Clay.integratedSignedHeatCross =
        Direct.integratedDirectCompanion T R
    ; Clay.heatCrossIsQuadraticCompanionCross = λ cutoff terminal → refl
    ; Clay.literalR406RemainderIsFourSignedCross =
        Direct.literalR406IntegralIsFourIntegratedDirectCompanion T R
    ; Clay.quadraticCompanionSignedBudget = directCompanionBudget P
    }

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

round501DirectR500ToR423CompilerClosed : Bool
round501DirectR500ToR423CompilerClosed = true

round501R487FixedOutputBudgetDecompositionRequired : Bool
round501R487FixedOutputBudgetDecompositionRequired = false

round501R492ExternalNamingWeldRequired : Bool
round501R492ExternalNamingWeldRequired = false

round501LaplaceRequired : Bool
round501LaplaceRequired = false

round501CrossOutputCoherenceRequired : Bool
round501CrossOutputCoherenceRequired = false

round501RemainingNovelLeafIsCutoffUniformDirectCompanionBudget : Bool
round501RemainingNovelLeafIsCutoffUniformDirectCompanionBudget = true

round501DirectCompanionBudgetClosed : Bool
round501DirectCompanionBudgetClosed = false

round501ClayPromotion : Bool
round501ClayPromotion = false

round501DirectR500ToR423CompilerClosedIsTrue :
  round501DirectR500ToR423CompilerClosed ≡ true
round501DirectR500ToR423CompilerClosedIsTrue = refl

round501R487FixedOutputBudgetDecompositionRequiredIsFalse :
  round501R487FixedOutputBudgetDecompositionRequired ≡ false
round501R487FixedOutputBudgetDecompositionRequiredIsFalse = refl

round501LaplaceRequiredIsFalse : round501LaplaceRequired ≡ false
round501LaplaceRequiredIsFalse = refl

round501ClayPromotionIsFalse : round501ClayPromotion ≡ false
round501ClayPromotionIsFalse = refl
