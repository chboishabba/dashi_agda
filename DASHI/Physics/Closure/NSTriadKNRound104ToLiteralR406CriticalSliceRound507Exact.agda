module DASHI.Physics.Closure.NSTriadKNRound104ToLiteralR406CriticalSliceRound507Exact where

------------------------------------------------------------------------
-- ROUND507 / ROUND104 SIGNED CRITICAL SLICE -> LITERAL R406 SLICE
--
-- R414's `CriticalSliceOnLiteralR406` is not a new seven-coordinate analytic
-- object. It is the existing Round104 `IntegratedSignedCriticalSlice` with its
-- integrable remainder fixed to the literal live R406 remainder integral.
--
-- Therefore one exact same-object receipt
--
--   Round104.integrableRemainder(S)
--     = integral_0^T R406_remainder(N,t) dt
--
-- is sufficient to transport an existing Round104 slice into R414. No new
-- critical-energy inequality or signed-production estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as R104
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414

F : C3.RealField _
F = Rational.rationalRealField

module Compile
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Unified = R414.Unified
    Time initialTime integrateTo DerivativeOf

  record LiteralR406RemainderWeld
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (terminal : Time)
      (cutoff : Nat)
      (slice : R104.IntegratedSignedCriticalSlice) : Set where
    constructor literal-r406-remainder-weld
    field
      remainderSameObject :
        R104.integrableRemainder slice
        ≡ Unified.literalRemainderIntegral T R cutoff terminal

  open LiteralR406RemainderWeld public

  round104SliceToLiteralR406 :
    ∀ {T R terminal cutoff}
      (slice : R104.IntegratedSignedCriticalSlice) →
      LiteralR406RemainderWeld T R terminal cutoff slice →
      Unified.CriticalSliceOnLiteralR406 T R terminal cutoff
  round104SliceToLiteralR406 {T} {R} {terminal} {cutoff} slice weld = record
    { Unified.initialCritical = R104.initialCritical slice
    ; Unified.terminalCritical = R104.terminalCritical slice
    ; Unified.criticalDissipation = R104.criticalDissipation slice
    ; Unified.integratedSignedProduction = R104.integratedSignedProduction slice
    ; Unified.viscousCoefficient = R104.viscousCoefficient slice
    ; Unified.absorbedCoefficient = R104.absorbedCoefficient slice
    ; Unified.criticalEnergyInequality = R104.criticalEnergyInequality slice
    ; Unified.signedProductionEstimateByLiteralRemainder =
        subst
          (λ remainder →
            R104.integratedSignedProduction slice
            R104.≤ R104.absorbedCoefficient slice
              R104.* R104.criticalDissipation slice + remainder)
          (remainderSameObject weld)
          (R104.signedProductionEstimate slice)
    }

round507Round104AndR414SliceCoordinatesAlreadyMatch : Bool
round507Round104AndR414SliceCoordinatesAlreadyMatch = true

round507OnlyAdditionalRepresentationReceiptIsR406RemainderEquality : Bool
round507OnlyAdditionalRepresentationReceiptIsR406RemainderEquality = true

round507PhysicalRound104SignedCriticalSliceClosed : Bool
round507PhysicalRound104SignedCriticalSliceClosed =
  R104.round104PhysicalUniformSignedCriticalProductionClosed

round507LiteralR406RemainderSameObjectWeldClosed : Bool
round507LiteralR406RemainderSameObjectWeldClosed = false

round507CriticalProductionAnalyticEstimateManufactured : Bool
round507CriticalProductionAnalyticEstimateManufactured = false

round507ClayPromotion : Bool
round507ClayPromotion = false

round507Round104AndR414SliceCoordinatesAlreadyMatchIsTrue :
  round507Round104AndR414SliceCoordinatesAlreadyMatch ≡ true
round507Round104AndR414SliceCoordinatesAlreadyMatchIsTrue = refl

round507OnlyAdditionalRepresentationReceiptIsR406RemainderEqualityIsTrue :
  round507OnlyAdditionalRepresentationReceiptIsR406RemainderEquality ≡ true
round507OnlyAdditionalRepresentationReceiptIsR406RemainderEqualityIsTrue = refl

round507PhysicalRound104SignedCriticalSliceClosedIsFalse :
  round507PhysicalRound104SignedCriticalSliceClosed ≡ false
round507PhysicalRound104SignedCriticalSliceClosedIsFalse =
  R104.round104PhysicalUniformSignedCriticalProductionClosedIsFalse

round507LiteralR406RemainderSameObjectWeldClosedIsFalse :
  round507LiteralR406RemainderSameObjectWeldClosed ≡ false
round507LiteralR406RemainderSameObjectWeldClosedIsFalse = refl

round507ClayPromotionIsFalse : round507ClayPromotion ≡ false
round507ClayPromotionIsFalse = refl
