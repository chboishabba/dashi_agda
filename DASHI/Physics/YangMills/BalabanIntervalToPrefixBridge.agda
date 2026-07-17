module DASHI.Physics.YangMills.BalabanIntervalToPrefixBridge where

-- Specialise an arbitrary-interval beta upper bound at start scale zero and
-- construct the existing `BalabanBetaPrefixBound` consumer.  This connects the
-- cumulative block-determinant route to the already-verified inverse-square
-- budget without creating a parallel estimate record.

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _+_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _+ℝ_
  ; _≤ℝ_
  ; cong
  ; trans
  )
open import DASHI.Geometry.Gauge.SUNPrimitives using
  ( clayYangMillsPromoted )
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; VerificationStatus
  )
open import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory using
  ( BalabanInverseSquareCouplingStep
  ; inverseSquaredCoupling
  ; betaCorrection
  )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareThresholdControlsCoupling
  ; gammaInverseSquare
  ; BalabanBetaPrefixBound
  ; betaPrefixSum
  )
open import DASHI.Physics.YangMills.BalabanIntervalDeterminantAlgebra using
  ( intervalSum )

natAddZeroRight : ∀ k → k + zero ≡ k
natAddZeroRight zero = refl
natAddZeroRight (suc k) = cong suc (natAddZeroRight k)

intervalZeroStartEqualsPrefix :
  (step : BalabanInverseSquareCouplingStep) →
  ∀ k →
  intervalSum (betaCorrection step) zero k
    ≡ betaPrefixSum step k
intervalZeroStartEqualsPrefix step zero = refl
intervalZeroStartEqualsPrefix step (suc k) =
  let
    sourceIndex = k + zero
    ih = intervalZeroStartEqualsPrefix step k
    p1 = cong
      (λ prefix →
        prefix +ℝ betaCorrection step (suc sourceIndex))
      ih
    p2 = cong
      (λ index →
        betaPrefixSum step k +ℝ betaCorrection step (suc index))
      (natAddZeroRight k)
  in
    trans p1 p2

replaceLeft :
  ∀ {a b c : ℝ} →
  a ≡ b →
  b ≤ℝ c →
  a ≤ℝ c
replaceLeft refl b≤c = b≤c

intervalUpperBoundToBetaPrefix :
  (K : ℕ) →
  (step : BalabanInverseSquareCouplingStep) →
  {γ : ℝ} →
  (threshold : InverseSquareThresholdControlsCoupling K γ step) →
  (prefixMajorant : ℕ → ℝ) →
  (intervalUpper :
    ∀ k → k ≤ K →
    intervalSum (betaCorrection step) zero k
      ≤ℝ prefixMajorant k) →
  (bareCouplingBudget :
    ∀ k → k ≤ K →
    gammaInverseSquare threshold +ℝ prefixMajorant k
      ≤ℝ inverseSquaredCoupling step zero) →
  (sourceAuthorityId : SourceAuthorityId) →
  (theoremLocator : String) →
  (status : VerificationStatus) →
  (noClayPromotion : clayYangMillsPromoted ≡ false) →
  BalabanBetaPrefixBound K step threshold
intervalUpperBoundToBetaPrefix
  K step threshold prefixMajorant
  intervalUpper bareCouplingBudget
  sourceAuthorityId theoremLocator status noClayPromotion =
  record
    { prefixMajorant = prefixMajorant
    ; betaPrefixControlled = λ k k≤K →
        replaceLeft
          (sym (intervalZeroStartEqualsPrefix step k))
          (intervalUpper k k≤K)
    ; bareCouplingBudget = bareCouplingBudget
    ; sourceAuthorityId = sourceAuthorityId
    ; theoremLocator = theoremLocator
    ; status = status
    ; noClayPromotion = noClayPromotion
    }
  where
    sym :
      ∀ {A : Set} {x y : A} →
      x ≡ y →
      y ≡ x
    sym refl = refl
