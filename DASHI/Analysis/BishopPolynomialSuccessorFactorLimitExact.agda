module DASHI.Analysis.BishopPolynomialSuccessorFactorLimitExact where

------------------------------------------------------------------------
-- FIXED-DEGREE POLYNOMIAL SUCCESSOR FACTOR TENDS TO ONE
--
-- SOURCE / ATTRIBUTION
--
-- The pinned Murray/Bishop Sequence library supplies:
--
--   * reciprocal convergence;
--   * convergence under addition and multiplication;
--   * epsilon extraction from convergence.
--
-- DASHI CONTRIBUTION
--
-- For every fixed degree k and Bishop real ratio r,
--
--   r * (1 + 1/(n+1))^k  ->  r.
--
-- Hence any strict upper ratio rho with r<rho eventually dominates the
-- polynomial successor factor.  This is the analytic heart of the standard
-- proof that n^k r^n has an eventual ratio strictly below one.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Nat.Base as Nat using (_≤_)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel

open import DASHI.Physics.YangMills.CompactLieProofLevel

oneSequence : Nat → BishopReal.ℝ
oneSequence _ = BishopReal.1ℝ

oneSequenceConverges :
  BishopSequence._ConvergesTo_ oneSequence BishopReal.1ℝ
oneSequenceConverges =
  BishopSequence.xₙ≃c⇒xₙ→c
    (λ {(suc index) → BishopP.≃-refl})

onePlusReciprocal : Nat → BishopReal.ℝ
onePlusReciprocal index =
  BishopReal._+_
    BishopReal.1ℝ
    (Basel.reciprocalSequence index)

onePlusReciprocalConvergesOne :
  BishopSequence._ConvergesTo_
    onePlusReciprocal
    BishopReal.1ℝ
onePlusReciprocalConvergesOne =
  BishopSequence.xₙ→x∧x≃y⇒xₙ→y
    (BishopSequence.xₙ+yₙ→x₀+y₀
      (BishopReal.1ℝ , oneSequenceConverges)
      (BishopReal.0ℝ , Basel.reciprocalSequenceConvergesZero))
    (BishopP.+-identityʳ BishopReal.1ℝ)

fixedPowerPreservesConvergence :
  ∀ {sequence : Nat → BishopReal.ℝ} {limit : BishopReal.ℝ} →
  BishopSequence._ConvergesTo_ sequence limit →
  ∀ degree →
  BishopSequence._ConvergesTo_
    (λ index → BishopReal.pow (sequence index) degree)
    (BishopReal.pow limit degree)
fixedPowerPreservesConvergence convergence zero =
  BishopSequence.xₙ≃c⇒xₙ→c
    (λ {(suc index) → BishopP.≃-refl})
fixedPowerPreservesConvergence {sequence} {limit} convergence (suc degree) =
  BishopSequence.xₙyₙ→x₀y₀
    (BishopReal.pow limit degree ,
      fixedPowerPreservesConvergence convergence degree)
    (limit , convergence)

powOne :
  ∀ degree →
  BishopReal._≃_
    (BishopReal.pow BishopReal.1ℝ degree)
    BishopReal.1ℝ
powOne zero = BishopP.≃-refl
powOne (suc degree) =
  BishopP.≃-trans
    (BishopP.*-congʳ (powOne degree))
    (BishopP.*-identityˡ BishopReal.1ℝ)

onePlusReciprocalPowerConvergesOne :
  ∀ degree →
  BishopSequence._ConvergesTo_
    (λ index → BishopReal.pow (onePlusReciprocal index) degree)
    BishopReal.1ℝ
onePlusReciprocalPowerConvergesOne degree =
  BishopSequence.xₙ→x∧x≃y⇒xₙ→y
    (fixedPowerPreservesConvergence
      onePlusReciprocalConvergesOne degree)
    (powOne degree)

polynomialSuccessorFactor :
  BishopReal.ℝ →
  Nat →
  Nat →
  BishopReal.ℝ
polynomialSuccessorFactor ratio degree index =
  BishopReal._*_
    ratio
    (BishopReal.pow (onePlusReciprocal index) degree)

constantSequence :
  BishopReal.ℝ →
  Nat →
  BishopReal.ℝ
constantSequence value _ = value

constantSequenceConverges :
  ∀ value →
  BishopSequence._ConvergesTo_
    (constantSequence value)
    value
constantSequenceConverges value =
  BishopSequence.xₙ≃c⇒xₙ→c
    (λ {(suc index) → BishopP.≃-refl})

polynomialSuccessorFactorConverges :
  ∀ (ratio : BishopReal.ℝ) degree →
  BishopSequence._ConvergesTo_
    (polynomialSuccessorFactor ratio degree)
    ratio
polynomialSuccessorFactorConverges ratio degree =
  BishopSequence.xₙ→x∧x≃y⇒xₙ→y
    (BishopSequence.xₙyₙ→x₀y₀
      (ratio , constantSequenceConverges ratio)
      (BishopReal.1ℝ ,
        onePlusReciprocalPowerConvergesOne degree))
    (BishopP.*-identityʳ ratio)

EventuallyBelow :
  (Nat → BishopReal.ℝ) →
  BishopReal.ℝ →
  Set
EventuallyBelow sequence upper =
  Σ Nat (λ start →
    ∀ index →
    Nat._≤_ start index →
    BishopReal._<_ (sequence index) upper)

polynomialSuccessorFactorEventuallyBelow :
  ∀ {ratio upper : BishopReal.ℝ} degree →
  BishopReal._<_ ratio upper →
  EventuallyBelow
    (polynomialSuccessorFactor ratio degree)
    upper
polynomialSuccessorFactorEventuallyBelow
    {ratio} {upper} degree ratioBelowUpper =
  start ,
  λ index indexAtLeastStart →
    let
      difference = BishopReal._-_ upper ratio
      differencePositive =
        BishopP.0<x⇒posx
          (BishopP.x<y⇒0<y-x ratio upper ratioBelowUpper)
      convergence =
        polynomialSuccessorFactorConverges ratio degree
      epsilonReceipt =
        BishopSequence.fast-ε-from-convergence
          (ratio , convergence)
          difference
          differencePositive
      errorBelowDifference =
        proj₂ epsilonReceipt index indexAtLeastStart
      rawDifferenceBelow :
        BishopReal._<_
          (BishopReal._-_
            (polynomialSuccessorFactor ratio degree index)
            ratio)
          difference
      rawDifferenceBelow =
        BishopP.≤-<-trans
          (BishopP.x≤∣x∣
            (BishopReal._-_
              (polynomialSuccessorFactor ratio degree index)
              ratio))
          errorBelowDifference
    in
    BishopP.<-respʳ-≃
      (BishopP.≃-symm
        (let open BishopP.ℝ-Solver
         in solve 2
           (λ lower upper′ →
             lower ⊕ (upper′ ⊖ lower) ⊜ upper′)
           BishopP.≃-refl
           ratio upper))
      (BishopP.<-respˡ-≃
        (let open BishopP.ℝ-Solver
         in solve 2
           (λ term lower →
             lower ⊕ (term ⊖ lower) ⊜ term)
           BishopP.≃-refl
           (polynomialSuccessorFactor ratio degree index)
           ratio)
        (BishopP.+-monoˡ-<
          ratio rawDifferenceBelow))
  where
  epsilonReceipt =
    BishopSequence.fast-ε-from-convergence
      (ratio , polynomialSuccessorFactorConverges ratio degree)
      (BishopReal._-_ upper ratio)
      (BishopP.0<x⇒posx
        (BishopP.x<y⇒0<y-x ratio upper ratioBelowUpper))

  start : Nat
  start = suc (proj₁ epsilonReceipt)

bishopPolynomialSuccessorFactorLimitLevel : ProofLevel
bishopPolynomialSuccessorFactorLimitLevel = conditional
