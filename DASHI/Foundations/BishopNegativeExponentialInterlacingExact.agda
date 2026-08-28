module DASHI.Foundations.BishopNegativeExponentialInterlacingExact where

------------------------------------------------------------------------
-- NEGATIVE EXPONENTIAL AS A CONCRETE ALTERNATING BISHOP SERIES
--
-- On 0 <= x <= 1 the magnitudes x^n/n! decrease.  The concrete factorial
-- series for exp(-x) therefore inhabits the generic alternating-decreasing
-- interlacing owner already proved in the Yang--Mills lane.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
import Data.Integer.Properties as ℤP
import Data.Nat.Properties as ℕP
open import Data.Rational.Unnormalised as ℚ using (0ℚᵘ; 1ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Signs
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as SignParity
import DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact as Alt
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Bracket
open import DASHI.Physics.YangMills.CompactLieProofLevel

record UnitIntervalPoint (x : BishopReal.ℝ) : Set₁ where
  field
    nonnegative : BishopReal.NonNegative x
    belowOne : BishopReal._≤_ x BishopReal.1ℝ

open UnitIntervalPoint public

absIsSelf : ∀ {x} → UnitIntervalPoint x →
  BishopReal._≃_ (BishopReal.∣_∣ x) x
absIsSelf point =
  BishopP.0≤x⇒∣x∣≃x
    (BishopP.nonNegx⇒0≤x (nonnegative point))

reciprocalNonnegative : ∀ n →
  BishopReal.NonNegative (Exp.embed (+ 1 / suc n))
reciprocalNonnegative n =
  BishopP.0≤x⇒nonNegx
    (BishopP.p≤q⇒p⋆≤q⋆
      0ℚᵘ (+ 1 / suc n)
      (ℚP.nonNegative⁻¹ (+ 1 / suc n)))

unitReciprocalBelowOne : ∀ n →
  BishopReal._≤_ (Exp.embed (+ 1 / suc n)) BishopReal.1ℝ
unitReciprocalBelowOne n =
  BishopP.p≤q⇒p⋆≤q⋆
    (+ 1 / suc n) 1ℚᵘ
    (ℚ.*≤* (ℤP.+≤+ (ℕP.n≤1+n n)))

magnitudeRatioBelowOne :
  ∀ {x} → UnitIntervalPoint x → ∀ n →
  BishopReal._≤_
    (BishopReal._*_
      (BishopReal.∣_∣ x)
      (Exp.embed (+ 1 / suc n)))
    BishopReal.1ℝ
magnitudeRatioBelowOne {x} point n =
  let
    reciprocal = Exp.embed (+ 1 / suc n)
    raw :
      BishopReal._≤_
        (BishopReal._*_ x reciprocal)
        (BishopReal._*_ BishopReal.1ℝ BishopReal.1ℝ)
    raw =
      BishopP.*-mono-≤
        (nonnegative point)
        (reciprocalNonnegative n)
        (belowOne point)
        (unitReciprocalBelowOne n)
  in
  BishopP.≤-respʳ-≃
    (BishopP.*-identityˡ BishopReal.1ℝ)
    (BishopP.≤-respˡ-≃
      (BishopP.*-congʳ (absIsSelf point))
      raw)

magnitudeDecreasing :
  ∀ {x} → UnitIntervalPoint x → ∀ n →
  BishopReal._≤_
    (Exp.expMagnitudeTerm x (suc n))
    (Exp.expMagnitudeTerm x n)
magnitudeDecreasing {x} point n =
  BishopP.≤-respˡ-≃
    (Exp.magnitudeSuccessorFactorization x n)
    (BishopP.≤-respʳ-≃
      (BishopP.*-identityˡ (Exp.expMagnitudeTerm x n))
      (BishopP.*-monoʳ-≤-nonNeg
        (magnitudeRatioBelowOne point n)
        (Exp.expMagnitudeNonnegative x n)))

powNegativeByAlternatingSign :
  (x : BishopReal.ℝ) → ∀ n →
  BishopReal._≃_
    (BishopReal.pow (BishopReal.- x) n)
    (BishopReal._*_
      (Signs.alternatingSign n)
      (BishopReal.pow x n))
powNegativeByAlternatingSign x zero =
  let open BishopP.ℝ-Solver
  in solve 0
    (Κ 1ℚᵘ ⊜ Κ 1ℚᵘ ⊗ Κ 1ℚᵘ)
    BishopP.≃-refl
powNegativeByAlternatingSign x (suc n) =
  let
    sign = Signs.alternatingSign n
    power = BishopReal.pow x n
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-cong
      (powNegativeByAlternatingSign x n)
      BishopP.≃-refl)
    (solve 3
      (λ s p x′ →
        (s ⊗ p) ⊗ (⊝ x′)
        ⊜ (s ⊗ (⊝ Κ 1ℚᵘ)) ⊗ (p ⊗ x′))
      BishopP.≃-refl sign power x)

powerAbsIsPower :
  ∀ {x} → UnitIntervalPoint x → ∀ n →
  BishopReal._≃_
    (BishopReal.∣_∣ (BishopReal.pow x n))
    (BishopReal.pow x n)
powerAbsIsPower {x} point n =
  BishopP.nonNegx⇒∣x∣≃x
    (BishopSequence.nonNegx⇒nonNegxⁿ n (nonnegative point))

negativeExpTermIsAlternatingMagnitude :
  ∀ {x} → UnitIntervalPoint x → ∀ n →
  BishopReal._≃_
    (Exp.expTerm (BishopReal.- x) n)
    (BishopReal._*_
      (Signs.alternatingSign n)
      (Exp.expMagnitudeTerm x n))
negativeExpTermIsAlternatingMagnitude {x} point n =
  let
    sign = Signs.alternatingSign n
    power = BishopReal.pow x n
    coefficient = Exp.embed (Exp.inverseFactorial n)
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-congʳ (powNegativeByAlternatingSign x n))
    (BishopP.≃-trans
      (solve 3
        (λ s p c → (s ⊗ p) ⊗ c ⊜ s ⊗ (c ⊗ p))
        BishopP.≃-refl sign power coefficient)
      (BishopP.*-congˡ
        (BishopP.*-congˡ
          (BishopP.≃-symm (powerAbsIsPower point n)))))

evenTermIsMagnitude :
  ∀ {x} → UnitIntervalPoint x → ∀ index →
  BishopReal._≃_
    (Exp.expTerm (BishopReal.- x) (Alt.double index))
    (Exp.expMagnitudeTerm x (Alt.double index))
evenTermIsMagnitude {x} point index =
  BishopP.≃-trans
    (negativeExpTermIsAlternatingMagnitude point (Alt.double index))
    (BishopP.≃-trans
      (BishopP.*-congʳ (SignParity.alternatingSignEven index))
      (BishopP.*-identityˡ
        (Exp.expMagnitudeTerm x (Alt.double index))))

oddTermIsNegativeMagnitude :
  ∀ {x} → UnitIntervalPoint x → ∀ index →
  BishopReal._≃_
    (Exp.expTerm (BishopReal.- x) (suc (Alt.double index)))
    (BishopReal.-
      (Exp.expMagnitudeTerm x (suc (Alt.double index))))
oddTermIsNegativeMagnitude {x} point index =
  BishopP.≃-trans
    (negativeExpTermIsAlternatingMagnitude point
      (suc (Alt.double index)))
    (BishopP.≃-trans
      (BishopP.*-congʳ (SignParity.alternatingSignOdd index))
      (let open BishopP.ℝ-Solver
       in solve 1
          (λ m → (⊝ Κ 1ℚᵘ) ⊗ m ⊜ ⊝ m)
          BishopP.≃-refl
          (Exp.expMagnitudeTerm x (suc (Alt.double index)))))

negativeExponentialAlternatingData :
  ∀ {x} → UnitIntervalPoint x →
  Alt.AlternatingDecreasingSeriesData
negativeExponentialAlternatingData {x} point = record
  { term = Exp.expTerm (BishopReal.- x)
  ; magnitude = Exp.expMagnitudeTerm x
  ; representedLimit = Exp.bishopExp (BishopReal.- x)
  ; magnitudeNonnegative = Exp.expMagnitudeNonnegative x
  ; magnitudeDecreasing = magnitudeDecreasing point
  ; evenTermIsPositiveMagnitude = evenTermIsMagnitude point
  ; oddTermIsNegativeMagnitude = oddTermIsNegativeMagnitude point
  ; seriesConvergesToRepresentedLimit =
      Exp.bishopExpConverges (BishopReal.- x)
  }

negativeExponentialInterlacing :
  ∀ {x} → UnitIntervalPoint x →
  Bracket.BishopAlternatingInterlacingData
negativeExponentialInterlacing point =
  Alt.alternatingInterlacingData
    (negativeExponentialAlternatingData point)

bishopNegativeExponentialInterlacingLevel : ProofLevel
bishopNegativeExponentialInterlacingLevel = machineChecked
