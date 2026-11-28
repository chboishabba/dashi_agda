module DASHI.Foundations.BishopConcreteElementaryCutsetExact where

-- Source-written, kernel pending. The two parity sectors of the
-- original factorial exponential magnitude have a common ratio tail.
-- No Round11 convergence input is consumed.
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Nat.Base as N
import Data.Nat.Properties as NP
open import Data.Product.Base using (_,_; _×_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _≤_; _⋆; ∣_∣)
open R renaming (_*_ to _·_) using ()
import RealProperties as P
import Sequence as S
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as E
import DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact as Log
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as F
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as T
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Data
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Cut

signAbs : ∀ n → ∣ T.alternatingSign n ∣ ≃ R.1ℝ
signAbs zero = P.nonNegx⇒∣x∣≃x (E.embeddedInverseFactorialNonnegative zero)
signAbs (suc n) =
  P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ (T.alternatingSign n) T.bishopMinusOne)
    (P.≃-trans (P.*-cong (signAbs n)
      (P.≃-trans P.∣-x∣≃∣x∣ (signAbs zero))) (P.*-identityˡ R.1ℝ))

degree : Nat → Nat → Nat
degree zero = F.evenExponent
degree (suc k) = F.oddExponent

degreeLower : ∀ k n → n N.≤ degree k n
degreeLower zero zero = NP.≤-refl
degreeLower (suc k) zero = N.z≤n
degreeLower zero (suc n) = N.s≤s (NP.≤-step (degreeLower zero n))
degreeLower (suc k) (suc n) = N.s≤s (NP.≤-step (degreeLower (suc k) n))

degreeStep : ∀ k n → degree k (suc n) ≡ suc (suc (degree k n))
degreeStep zero n = refl
degreeStep (suc k) n = refl

signedTerm : Nat → ℝ → Nat → ℝ
signedTerm zero = T.cosineSignedTerm
signedTerm (suc k) = T.sineSignedTerm

absRead : ∀ k x n → ∣ signedTerm k x n ∣ ≃ E.expMagnitudeTerm x (degree k n)
absRead zero x n = read F.evenExponent n
  where
  read : ∀ d n → ∣ T.alternatingSign n · ((F.inverseFactorialRational (d n) ⋆) · R.pow x (d n)) ∣ ≃ E.expMagnitudeTerm x (d n)
  read d n = P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ _ _)
    (P.≃-trans (P.*-cong (signAbs n)
      (P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ _ _)
        (P.*-congʳ (P.nonNegx⇒∣x∣≃x (E.embeddedInverseFactorialNonnegative (d n))))))
      (P.*-identityˡ _))
absRead (suc k) x n = P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ _ _)
  (P.≃-trans (P.*-cong (signAbs n)
    (P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ _ _)
      (P.*-congʳ (P.nonNegx⇒∣x∣≃x (E.embeddedInverseFactorialNonnegative (degree (suc k) n))))))
    (P.*-identityˡ _))

-- Two successive original factorial steps give a quarter contraction.
-- Retain the weaker half bound, avoiding any new ratio-test interface.
twoStep : ∀ x d → 2 * E.magnitudeNaturalBound x N.≤ suc d →
  E.expMagnitudeTerm x (suc (suc d)) ≤ E.half · E.expMagnitudeTerm x d
twoStep x d h =
  P.≤-trans (E.expMagnitudeSuccessorRatioHalf x (suc d) (NP.≤-step h))
    (P.≤-trans (P.*-monoˡ-≤-nonNeg (E.expMagnitudeSuccessorRatioHalf x d h)
      (P.pos⇒nonNeg (P.0<x⇒posx E.halfPositive)))
      (P.≤-respˡ-≃
        (P.≃-symm (P.*-assoc E.half E.half (E.expMagnitudeTerm x d)))
        (P.*-monoʳ-≤-nonNeg
          (P.≤-respʳ-≃ (P.*-identityʳ E.half)
            (P.*-monoˡ-≤-nonNeg (P.<⇒≤ E.halfBelowOne)
              (P.pos⇒nonNeg (P.0<x⇒posx E.halfPositive))))
          (E.expMagnitudeNonnegative x d))))

sectorAbsolute : ∀ k x → S.SeriesOf_ConvergesAbsolutely (signedTerm k x)
sectorAbsolute k x = S.proposition-3-6-1
  (E.halfPositive , E.halfBelowOne)
  (2 * E.magnitudeNaturalBound x , λ n h →
    P.≤-respˡ-≃ (P.≃-trans (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ _)) (absRead k x (suc n)))
      (P.≤-respʳ-≃ (P.*-congˡ (P.≃-symm
        (P.≃-trans (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ _)) (absRead k x n))))
        (P.≤-respˡ-≃ (P.≃-refl) (step n h))))
  where
  step : ∀ n → suc (2 * E.magnitudeNaturalBound x) N.≤ n →
    E.expMagnitudeTerm x (degree k (suc n)) ≤ E.half · E.expMagnitudeTerm x (degree k n)
  step n h rewrite degreeStep k n =
    twoStep x (degree k n) (NP.≤-trans (NP.≤-trans (NP.n≤1+n _) h)
      (NP.≤-step (degreeLower k n)))

-- Legacy metadata fields are proposition-valued families, not evidence.
-- State literal coefficient formulas; no truth is inferred from their names.
dataSet : Data.BishopElementaryPowerSeriesData
dataSet = record
  { rational = R._⋆
  ; rationalDefinition = refl
  ; sineTerm = T.sineSignedTerm
  ; cosineTerm = T.cosineSignedTerm
  ; exponentialTerm = E.expTerm
  ; negativeLogOneMinusTerm = Log.sourceNegativeLogTerm
  ; sineAbsoluteConvergence = sectorAbsolute 1
  ; cosineAbsoluteConvergence = sectorAbsolute 0
  ; exponentialAbsoluteConvergence = E.expAbsoluteSeriesConvergent
  ; InOpenUnitInterval = λ x → R._<_ R.0ℝ x × R._<_ x R.1ℝ
  ; negativeLogAbsoluteConvergence = λ x (lo , hi) → Log.sourceNegativeLogAbsolutelyConvergent x lo hi
  ; sineCoefficientRecurrenceExact = λ x n → ∣ T.sineSignedTerm x n ∣ ≃ E.expMagnitudeTerm x (F.oddExponent n)
  ; cosineCoefficientRecurrenceExact = λ x n → ∣ T.cosineSignedTerm x n ∣ ≃ E.expMagnitudeTerm x (F.evenExponent n)
  ; exponentialCoefficientRecurrenceExact = λ x n → E.expMagnitudeTerm x (suc n) ≃ ((∣ x ∣ · ((+ 1 / suc n) ⋆)) · E.expMagnitudeTerm x n)
  ; negativeLogCoefficientRecurrenceExact = λ x n → Log.sourceNegativeLogTerm x n ≃ R.pow x (suc n) · ((+ 1 / suc n) ⋆)
  ; sineOddPowersAndFactorialsExact = λ x n → T.sineSignedTerm x n ≃ T.alternatingSign n · ((F.inverseFactorialRational (F.oddExponent n) ⋆) · R.pow x (F.oddExponent n))
  ; cosineEvenPowersAndFactorialsExact = λ x n → T.cosineSignedTerm x n ≃ T.alternatingSign n · ((F.inverseFactorialRational (F.evenExponent n) ⋆) · R.pow x (F.evenExponent n))
  ; exponentialPowersAndFactorialsExact = λ x n → E.expTerm x n ≃ R.pow x n · (E.inverseFactorial n ⋆)
  ; negativeLogPowersOverPositiveIntegersExact = λ x n → Log.sourceNegativeLogTerm x n ≃ R.pow x (suc n) · ((+ 1 / suc n) ⋆)
  ; sineAlternatingSignsExact = λ x n → T.sineSignedTerm (R.- x) n ≃ R.- (T.sineSignedTerm x n)
  ; cosineAlternatingSignsExact = λ x n → T.cosineSignedTerm (R.- x) n ≃ T.cosineSignedTerm x n
  }

concreteCutset : Cut.BishopCutset
concreteCutset = record
  { elementarySeries = dataSet
  ; configuredDefinitions = record
      { sineTermDefinition = λ x n → refl
      ; cosineTermDefinition = λ x n → refl
      }
  }
