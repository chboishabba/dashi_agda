module DASHI.Foundations.BishopExponentialSeriesConvergenceExact where

------------------------------------------------------------------------
-- CONCRETE BISHOP EXPONENTIAL SERIES: ABSOLUTE CONVERGENCE
--
-- The pinned Bishop Sequence.agda already proves the ratio test
-- (Proposition 3.6(1) in the Murray development).  For
--
--     e_x(n) = x^n / n!
--
-- choose a natural M with |x| < M and take n >= 2M.  Then
--
--     |e_x(n+1)| <= (M/(n+1)) |e_x(n)| <= (1/2)|e_x(n)|.
--
-- Thus the absolute series converges for every Bishop real x.  This removes
-- the exponential-convergence authority field from the partition lane.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Integer.Base as ℤ using (+_; +≤+)
open import Data.Nat.Base as ℕ using (NonZero; _≤_; _!; z≤n)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; 0ℚᵘ; 1ℚᵘ; _/_; _*_; _≤_; NonNegative)
import Data.Rational.Unnormalised.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (sym)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as SeriesExt
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Physics.YangMills.BalabanBishopConcreteFactorialCoefficientDischargeExact as Factorial
open import DASHI.Physics.YangMills.CompactLieProofLevel

inverseFactorial : Nat → ℚᵘ
inverseFactorial = Estimates.inverseFactorialRational

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

expTerm : BishopReal.ℝ → Nat → BishopReal.ℝ
expTerm x n = BishopReal._*_ (BishopReal.pow x n) (embed (inverseFactorial n))

expMagnitudeTerm : BishopReal.ℝ → Nat → BishopReal.ℝ
expMagnitudeTerm x n =
  BishopReal._*_
    (embed (inverseFactorial n))
    (BishopReal.∣_∣ (BishopReal.pow x n))

inverseFactorialNonnegative : ∀ n → ℚ.NonNegative (inverseFactorial n)
inverseFactorialNonnegative n =
  ℚ.nonNegative
    (ℚP.nonNegative⁻¹ (inverseFactorial n))

embeddedInverseFactorialNonnegative : ∀ n →
  BishopReal.NonNegative (embed (inverseFactorial n))
embeddedInverseFactorialNonnegative n =
  BishopP.0≤x⇒nonNegx
    (BishopP.p≤q⇒p⋆≤q⋆
      0ℚᵘ (inverseFactorial n)
      (ℚP.nonNegative⁻¹ (inverseFactorial n)))

expMagnitudeNonnegative : ∀ x n →
  BishopReal.NonNegative (expMagnitudeTerm x n)
expMagnitudeNonnegative x n =
  BishopP.nonNegx,y⇒nonNegx*y
    (embeddedInverseFactorialNonnegative n)
    (BishopP.nonNeg∣x∣ (BishopReal.pow x n))

expTermAbsIsMagnitude : ∀ x n →
  BishopReal._≃_
    (BishopReal.∣_∣ (expTerm x n))
    (expMagnitudeTerm x n)
expTermAbsIsMagnitude x n =
  BishopP.≃-trans
    (BishopP.∣x*y∣≃∣x∣*∣y∣
      (BishopReal.pow x n)
      (embed (inverseFactorial n)))
    (let open BishopP.ℝ-Solver
     in solve 2
       (λ power coefficient →
         (power ⊗ coefficient) ⊜ (coefficient ⊗ power))
       BishopP.≃-refl
       (BishopReal.∣_∣ (BishopReal.pow x n))
       (BishopReal.∣_∣ (embed (inverseFactorial n))))
    |> BishopP.≃-trans
      (BishopP.*-congʳ
        (BishopP.0≤x⇒∣x∣≃x
          (BishopP.nonNegx⇒0≤x
            (embeddedInverseFactorialNonnegative n))))
  where
  infixl 0 _|>_
  _|>_ : ∀ {A B : Set} → A → (A → B) → B
  value |> f = f value

inverseFactorialSuccessor : ∀ n →
  inverseFactorial (suc n)
  ℚ.≃
  ((+ 1 / suc n) ℚ.* inverseFactorial n)
inverseFactorialSuccessor n =
  ℚP.≃-sym
    (ℚP.≃-reflexive
      (Factorial.positiveUnitFractionProduct
        (suc n) (n !)))

embeddedInverseFactorialSuccessor : ∀ n →
  BishopReal._≃_
    (embed (inverseFactorial (suc n)))
    (BishopReal._*_
      (embed (+ 1 / suc n))
      (embed (inverseFactorial n)))
embeddedInverseFactorialSuccessor n =
  BishopP.≃-trans
    (BishopP.⋆-cong (inverseFactorialSuccessor n))
    (BishopP.⋆-distrib-*
      (+ 1 / suc n)
      (inverseFactorial n))

magnitudeSuccessorFactorization : ∀ x n →
  BishopReal._≃_
    (expMagnitudeTerm x (suc n))
    (BishopReal._*_
      (BishopReal._*_
        (BishopReal.∣_∣ x)
        (embed (+ 1 / suc n)))
      (expMagnitudeTerm x n))
magnitudeSuccessorFactorization x n =
  BishopP.≃-trans
    (BishopP.*-cong
      (embeddedInverseFactorialSuccessor n)
      (BishopSequence.∣xⁿ∣≃∣x∣ⁿ x (suc n)))
    (let open BishopP.ℝ-Solver
     in solve 4
       (λ reciprocal coefficient oldPower absx →
         ((reciprocal ⊗ coefficient) ⊗ (oldPower ⊗ absx))
         ⊜ ((absx ⊗ reciprocal) ⊗ (coefficient ⊗ oldPower)))
       BishopP.≃-refl
       (embed (+ 1 / suc n))
       (embed (inverseFactorial n))
       (BishopReal.pow (BishopReal.∣_∣ x) n)
       (BishopReal.∣_∣ x))
    |> BishopP.≃-trans
      (BishopP.*-cong
        BishopP.≃-refl
        (BishopP.*-congˡ
          (BishopP.≃-symm
            (BishopSequence.∣xⁿ∣≃∣x∣ⁿ x n))))
  where
  infixl 0 _|>_
  _|>_ : ∀ {A B : Set} → A → (A → B) → B
  value |> f = f value

half : BishopReal.ℝ
half = embed (+ 1 / 2)

halfPositive : BishopReal._<_ BishopReal.0ℝ half
halfPositive =
  BishopP.p<q⇒p⋆<q⋆
    0ℚᵘ (+ 1 / 2)
    (ℚP.positive⁻¹ (+ 1 / 2))

halfBelowOne : BishopReal._<_ half BishopReal.1ℝ
halfBelowOne =
  BishopP.p<q⇒p⋆<q⋆
    (+ 1 / 2) 1ℚᵘ
    (ℚ.*<* (ℤ.+<+ (ℕ.s≤s ℕP.≤-refl)))

magnitudeNaturalBound : (x : BishopReal.ℝ) → Nat
magnitudeNaturalBound x = suc (proj₁ (BishopP.archimedean-ℝ (BishopReal.∣_∣ x)))

magnitudeBelowNaturalBound : ∀ x →
  BishopReal._<_
    (BishopReal.∣_∣ x)
    (embed (+ magnitudeNaturalBound x / 1))
magnitudeBelowNaturalBound x =
  proj₂ (BishopP.archimedean-ℝ (BishopReal.∣_∣ x))

ratioRationalBelowHalf :
  ∀ {bound n : Nat} →
  2 * bound ≤ suc n →
  (+ bound / suc n) ℚ.≤ (+ 1 / 2)
ratioRationalBelowHalf {bound} {n} twoBound≤sucN =
  ℚ.*≤*
    (ℤ.+≤+
      (ℕP.≤-reflexive
        (let open ℕP.≤-Reasoning
         in begin
           bound * 2
             ≡⟨ ℕP.*-comm bound 2 ⟩
           2 * bound
             ≤⟨ twoBound≤sucN ⟩
           suc n
             ≡⟨ sym (ℕP.*-identityʳ (suc n)) ⟩
           suc n * 1
         ∎)))

magnitudeRatioBelowHalf :
  ∀ x n →
  2 * magnitudeNaturalBound x ≤ suc n →
  BishopReal._≤_
    (BishopReal._*_
      (BishopReal.∣_∣ x)
      (embed (+ 1 / suc n)))
    half
magnitudeRatioBelowHalf x n cutoff =
  let
    bound = magnitudeNaturalBound x
    boundR = embed (+ bound / 1)
    reciprocal = embed (+ 1 / suc n)

    reciprocalNN : BishopReal.NonNegative reciprocal
    reciprocalNN =
      BishopP.0≤x⇒nonNegx
        (BishopP.p≤q⇒p⋆≤q⋆
          0ℚᵘ (+ 1 / suc n)
          (ℚP.nonNegative⁻¹ (+ 1 / suc n)))

    raw :
      BishopReal._≤_
        (BishopReal._*_ (BishopReal.∣_∣ x) reciprocal)
        (BishopReal._*_ boundR reciprocal)
    raw =
      BishopP.*-monoˡ-≤-nonNeg
        (BishopP.<⇒≤ (magnitudeBelowNaturalBound x))
        reciprocalNN
  in
  BishopP.≤-trans raw
    (BishopP.≤-respʳ-≃
      (BishopP.≃-symm
        (BishopP.⋆-distrib-*
          (+ bound / 1)
          (+ 1 / suc n)))
      (BishopP.p≤q⇒p⋆≤q⋆
        ((+ bound / 1) ℚ.* (+ 1 / suc n))
        (+ 1 / 2)
        (ℚP.≤-respˡ-≃
          (ℚP.≃-sym
            (ℚP.≃-reflexive refl))
          (ratioRationalBelowHalf cutoff))))

expMagnitudeSuccessorRatioHalf :
  ∀ x n →
  2 * magnitudeNaturalBound x ≤ suc n →
  BishopReal._≤_
    (expMagnitudeTerm x (suc n))
    (BishopReal._*_ half (expMagnitudeTerm x n))
expMagnitudeSuccessorRatioHalf x n cutoff =
  BishopP.≤-respˡ-≃
    (magnitudeSuccessorFactorization x n)
    (BishopP.*-monoʳ-≤-nonNeg
      (magnitudeRatioBelowHalf x n cutoff)
      (expMagnitudeNonnegative x n))

expMagnitudeSeriesConvergent : ∀ x →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf (expMagnitudeTerm x))
expMagnitudeSeriesConvergent x =
  let bound = magnitudeNaturalBound x in
  BishopSequence.proposition-3-6-1
    (halfPositive , halfBelowOne)
    (2 * bound , λ n nAtLeastSuccessorCutoff →
      expMagnitudeSuccessorRatioHalf x n
        (ℕP.≤-trans
          (ℕP.n≤1+n (2 * bound))
          nAtLeastSuccessorCutoff))

expAbsoluteSeriesConvergent : ∀ x →
  BishopSequence.SeriesOf_ConvergesAbsolutely (expTerm x)
expAbsoluteSeriesConvergent x =
  let magnitudeConvergent = expMagnitudeSeriesConvergent x
      magnitudeLimit = proj₁ magnitudeConvergent
      magnitudeConverges = proj₂ magnitudeConvergent
      partialSumsEquivalent =
        SeriesExt.seriesPartialSumsCongruent
          (expTermAbsIsMagnitude x)
  in
  magnitudeLimit ,
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count-1) →
      BishopP.≃-symm (partialSumsEquivalent (suc count-1))})
    magnitudeConvergent

bishopExp : BishopReal.ℝ → BishopReal.ℝ
bishopExp x =
  BishopSequence.lim
    (BishopSequence.absolute⇒isConvergent
      (expAbsoluteSeriesConvergent x))

bishopExpConverges : ∀ x →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf (expTerm x))
    (bishopExp x)
bishopExpConverges x =
  proj₂
    (BishopSequence.absolute⇒isConvergent
      (expAbsoluteSeriesConvergent x))

bishopExponentialTermDefinitionLevel : ProofLevel
bishopExponentialTermDefinitionLevel = machineChecked

bishopExponentialAbsoluteConvergenceLevel : ProofLevel
bishopExponentialAbsoluteConvergenceLevel = machineChecked

bishopExponentialConstructionLevel : ProofLevel
bishopExponentialConstructionLevel = machineChecked
