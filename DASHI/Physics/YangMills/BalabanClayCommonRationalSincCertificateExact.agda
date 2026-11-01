module DASHI.Physics.YangMills.BalabanClayCommonRationalSincCertificateExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCommonCertifiedTaylorEnclosureExact as Taylor

------------------------------------------------------------------------
-- Literature normalization.
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721
-- Relationship: rational lower/upper enclosures, interval splitting and Taylor
-- evaluation inside a proof assistant.
--
-- Joan Solà, Jérémie Deray and Dinesh Atchuthan,
-- "A micro Lie theory for state estimation in robotics", arXiv:1812.01537.
-- No journal DOI is assigned in the cited arXiv version.
-- Relationship: independently maintained SO(3) left/right Jacobian convention.
--
-- Timothy D. Barfoot, "State Estimation for Robotics", Cambridge University
-- Press (2017). DOI: 10.1017/9781316671528
-- Relationship: closed SO(3) Jacobian and inverse-Jacobian formulas.
--
-- The coefficients below are DASHI-owned exact rational data.  The only
-- non-algebraic authority retained by this module is the elementary alternating
-- Taylor remainder theorem for sin/cos and the monotonicity/series estimate for
-- -log(sinc).  Every subsequent evaluation is rational Horner arithmetic.
------------------------------------------------------------------------

twoℚ threeℚ fourℚ sixℚ eightℚ sixteenℚ : ℚ
twoℚ = 1ℚ + 1ℚ
threeℚ = twoℚ + 1ℚ
fourℚ = twoℚ + twoℚ
sixℚ = threeℚ + threeℚ
eightℚ = fourℚ + fourℚ
sixteenℚ = eightℚ + eightℚ

halfℚ sixthℚ twentyFourthℚ oneTwentiethℚ oneNinetiethℚ : ℚ
halfℚ = + 1 / 2
sixthℚ = + 1 / 6
twentyFourthℚ = + 1 / 24
oneTwentiethℚ = + 1 / 20
oneNinetiethℚ = + 1 / 90

oneHundredTwentiethℚ oneSevenHundredTwentiethℚ : ℚ
oneHundredTwentiethℚ = + 1 / 120
oneSevenHundredTwentiethℚ = + 1 / 720

configuredSincRadius : ℚ
configuredSincRadius = halfℚ

------------------------------------------------------------------------
-- Ascending-degree coefficient lists consumed by the common Horner evaluator.
-- On 0 <= x <= 1/2 the intended enclosures are
--
--   x - x^3/6                    <= sin x
--   sin x <= x - x^3/6 + x^5/120,
--
--   1 - x^2/2                   <= cos x
--   cos x <= 1 - x^2/2 + x^4/24,
--
--   1 - x^2/6                   <= sinc x
--   sinc x <= 1 - x^2/6 + x^4/120,
--
-- and
--
--   -log(sinc x) <= x^2/6 + x^4/90.
------------------------------------------------------------------------

sineLowerCoefficients sineUpperCoefficients : List ℚ
sineLowerCoefficients =
  0ℚ ∷ 1ℚ ∷ 0ℚ ∷ (- sixthℚ) ∷ []
sineUpperCoefficients =
  0ℚ ∷ 1ℚ ∷ 0ℚ ∷ (- sixthℚ) ∷ 0ℚ ∷ oneHundredTwentiethℚ ∷ []

cosineLowerCoefficients cosineUpperCoefficients : List ℚ
cosineLowerCoefficients =
  1ℚ ∷ 0ℚ ∷ (- halfℚ) ∷ []
cosineUpperCoefficients =
  1ℚ ∷ 0ℚ ∷ (- halfℚ) ∷ 0ℚ ∷ twentyFourthℚ ∷ []

sincLowerCoefficients sincUpperCoefficients : List ℚ
sincLowerCoefficients =
  1ℚ ∷ 0ℚ ∷ (- sixthℚ) ∷ []
sincUpperCoefficients =
  1ℚ ∷ 0ℚ ∷ (- sixthℚ) ∷ 0ℚ ∷ oneHundredTwentiethℚ ∷ []

negativeLogSincLowerCoefficients negativeLogSincUpperCoefficients : List ℚ
negativeLogSincLowerCoefficients =
  0ℚ ∷ 0ℚ ∷ sixthℚ ∷ []
negativeLogSincUpperCoefficients =
  0ℚ ∷ 0ℚ ∷ sixthℚ ∷ 0ℚ ∷ oneNinetiethℚ ∷ []

rationalSemiring : Taylor.ScalarSemiring ℚ
rationalSemiring = record
  { zero = 0ℚ
  ; one = 1ℚ
  ; add = _+_
  ; multiply = _*_
  }

sineLowerPolynomial sineUpperPolynomial : ℚ → ℚ
sineLowerPolynomial =
  Taylor.polynomialValue rationalSemiring sineLowerCoefficients
sineUpperPolynomial =
  Taylor.polynomialValue rationalSemiring sineUpperCoefficients

cosineLowerPolynomial cosineUpperPolynomial : ℚ → ℚ
cosineLowerPolynomial =
  Taylor.polynomialValue rationalSemiring cosineLowerCoefficients
cosineUpperPolynomial =
  Taylor.polynomialValue rationalSemiring cosineUpperCoefficients

sincLowerPolynomial sincUpperPolynomial : ℚ → ℚ
sincLowerPolynomial =
  Taylor.polynomialValue rationalSemiring sincLowerCoefficients
sincUpperPolynomial =
  Taylor.polynomialValue rationalSemiring sincUpperCoefficients

negativeLogSincLowerPolynomial negativeLogSincUpperPolynomial : ℚ → ℚ
negativeLogSincLowerPolynomial =
  Taylor.polynomialValue rationalSemiring negativeLogSincLowerCoefficients
negativeLogSincUpperPolynomial =
  Taylor.polynomialValue rationalSemiring negativeLogSincUpperCoefficients

sineLowerHornerExact : ∀ x →
  sineLowerPolynomial x ≡ x - sixthℚ * (x * x * x)
sineLowerHornerExact = ℚRing.solve-∀

sineUpperHornerExact : ∀ x →
  sineUpperPolynomial x
  ≡ x - sixthℚ * (x * x * x)
      + oneHundredTwentiethℚ * (x * x * x * x * x)
sineUpperHornerExact = ℚRing.solve-∀

cosineLowerHornerExact : ∀ x →
  cosineLowerPolynomial x ≡ 1ℚ - halfℚ * (x * x)
cosineLowerHornerExact = ℚRing.solve-∀

cosineUpperHornerExact : ∀ x →
  cosineUpperPolynomial x
  ≡ 1ℚ - halfℚ * (x * x) + twentyFourthℚ * (x * x * x * x)
cosineUpperHornerExact = ℚRing.solve-∀

sincLowerHornerExact : ∀ x →
  sincLowerPolynomial x ≡ 1ℚ - sixthℚ * (x * x)
sincLowerHornerExact = ℚRing.solve-∀

sincUpperHornerExact : ∀ x →
  sincUpperPolynomial x
  ≡ 1ℚ - sixthℚ * (x * x)
      + oneHundredTwentiethℚ * (x * x * x * x)
sincUpperHornerExact = ℚRing.solve-∀

negativeLogSincUpperHornerExact : ∀ x →
  negativeLogSincUpperPolynomial x
  ≡ sixthℚ * (x * x) + oneNinetiethℚ * (x * x * x * x)
negativeLogSincUpperHornerExact = ℚRing.solve-∀

------------------------------------------------------------------------
-- Elementary analytic authority.  This is deliberately much narrower than a
-- free-form transcendental oracle: it can only certify the four configured
-- enclosures on the fixed rational interval [0,1/2].
------------------------------------------------------------------------

record ConfiguredSincAnalyticAuthority (Real : Set) : Set₁ where
  field
    rational : ℚ → Real
    sine cosine logarithm : Real → Real
    divide multiply subtract negate : Real → Real → Real
    zero one : Real

    InConfiguredRadius : Real → Set
    LessEqual StrictLess : Real → Real → Set

    sinc : Real → Real
    negativeLogSinc : Real → Real

    polynomialReal : List ℚ → Real → Real
    polynomialRealAgreesWithRationalHorner : ∀ coefficients point → Set

    sineLowerCorrect : ∀ point → InConfiguredRadius point →
      LessEqual (polynomialReal sineLowerCoefficients point) (sine point)
    sineUpperCorrect : ∀ point → InConfiguredRadius point →
      LessEqual (sine point) (polynomialReal sineUpperCoefficients point)

    cosineLowerCorrect : ∀ point → InConfiguredRadius point →
      LessEqual (polynomialReal cosineLowerCoefficients point) (cosine point)
    cosineUpperCorrect : ∀ point → InConfiguredRadius point →
      LessEqual (cosine point) (polynomialReal cosineUpperCoefficients point)

    sincLowerCorrect : ∀ point → InConfiguredRadius point →
      LessEqual (polynomialReal sincLowerCoefficients point) (sinc point)
    sincUpperCorrect : ∀ point → InConfiguredRadius point →
      LessEqual (sinc point) (polynomialReal sincUpperCoefficients point)

    negativeLogSincLowerCorrect : ∀ point → InConfiguredRadius point →
      LessEqual
        (polynomialReal negativeLogSincLowerCoefficients point)
        (negativeLogSinc point)
    negativeLogSincUpperCorrect : ∀ point → InConfiguredRadius point →
      LessEqual
        (negativeLogSinc point)
        (polynomialReal negativeLogSincUpperCoefficients point)

    sincPositiveOnConfiguredRadius : ∀ point → InConfiguredRadius point →
      StrictLess zero (sinc point)

    inverseSincMonotoneConfiguredRadiusBound : ∀ point →
      InConfiguredRadius point → Set

    negativeLogSincQuadraticConfigured : ∀ point →
      InConfiguredRadius point →
      LessEqual (negativeLogSinc point)
        (polynomialReal negativeLogSincUpperCoefficients point)

open ConfiguredSincAnalyticAuthority public

sineEnclosure = λ {Real} (dataSet : ConfiguredSincAnalyticAuthority Real) →
  sineLowerCorrect dataSet , sineUpperCorrect dataSet
  where
  open import Data.Product using (_,_)

cosineEnclosure = λ {Real} (dataSet : ConfiguredSincAnalyticAuthority Real) →
  cosineLowerCorrect dataSet , cosineUpperCorrect dataSet
  where
  open import Data.Product using (_,_)

sincEnclosure = λ {Real} (dataSet : ConfiguredSincAnalyticAuthority Real) →
  sincLowerCorrect dataSet , sincUpperCorrect dataSet
  where
  open import Data.Product using (_,_)

negativeLogSincEnclosure =
  λ {Real} (dataSet : ConfiguredSincAnalyticAuthority Real) →
    negativeLogSincLowerCorrect dataSet ,
    negativeLogSincUpperCorrect dataSet
  where
  open import Data.Product using (_,_)

configuredRationalCoefficientLevel : ProofLevel
configuredRationalCoefficientLevel = machineChecked

configuredHornerIdentityLevel : ProofLevel
configuredHornerIdentityLevel = machineChecked

configuredAlternatingRemainderInputsLevel : ProofLevel
configuredAlternatingRemainderInputsLevel = conditional

configuredNegativeLogSincInputsLevel : ProofLevel
configuredNegativeLogSincInputsLevel = conditional
