module DASHI.Mathematics.Arithmetic.SmallPrimeTruncatedEulerProductExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", second edition.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms".
-- DOI: 10.1007/978-0-387-27226-9.
--
-- DASHI CONTRIBUTION
--
-- Consume the seven checked Frobenius rows for E : y^2=x^3-x and construct
-- the finite Euler denominator
--
--   product_{p in {3,5,7,11,13,17,19}} (1-a_p T+pT^2).
--
-- A finite modular Fourier candidate whose selected coefficients agree with
-- the Frobenius traces has exactly the same local factors and truncated Euler
-- product.  This is the finite local-to-global bridge; the Modularity Theorem
-- and infinite analytic L-function remain separate boundaries.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Arithmetic.EllipticCurveSmallPrimeFrobeniusExact as Rows
import DASHI.Mathematics.Automorphic.TruncatedLFunctionExact as L
import DASHI.Mathematics.NumberTheory.FiniteEulerProductExact as Euler

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

rowFactorValue : Rows.SmallPrimeFrobeniusRow → ℚ → ℚ
rowFactorValue row T =
  1ℚ - Rows.signedToRational (Rows.frobeniusTrace row) * T
    + Rows.natToRational (Rows.prime row) * T * T

smallPrimeEulerDenominator : ℚ → ℚ
smallPrimeEulerDenominator T =
  Euler.productList L.rationalSemiring
    (mapList (λ row → rowFactorValue row T) Rows.smallPrimeRows)

smallPrimeEulerDenominatorUnfolds : ∀ T →
  smallPrimeEulerDenominator T
  ≡ rowFactorValue Rows.p3Row T
    * (rowFactorValue Rows.p5Row T
    * (rowFactorValue Rows.p7Row T
    * (rowFactorValue Rows.p11Row T
    * (rowFactorValue Rows.p13Row T
    * (rowFactorValue Rows.p17Row T
    * (rowFactorValue Rows.p19Row T * 1ℚ))))))
smallPrimeEulerDenominatorUnfolds T = refl

p3LocalFactor : ∀ T →
  rowFactorValue Rows.p3Row T ≡ 1ℚ + Rows.natToRational 3 * T * T
p3LocalFactor T = solve (T ∷ [])

p5LocalFactor : ∀ T →
  rowFactorValue Rows.p5Row T
  ≡ 1ℚ + Rows.natToRational 2 * T + Rows.natToRational 5 * T * T
p5LocalFactor T = solve (T ∷ [])

p13LocalFactor : ∀ T →
  rowFactorValue Rows.p13Row T
  ≡ 1ℚ - Rows.natToRational 6 * T + Rows.natToRational 13 * T * T
p13LocalFactor T = solve (T ∷ [])

p17LocalFactor : ∀ T →
  rowFactorValue Rows.p17Row T
  ≡ 1ℚ - Rows.natToRational 2 * T + Rows.natToRational 17 * T * T
p17LocalFactor T = solve (T ∷ [])

record SelectedModularCoefficientCandidate : Set₁ where
  field
    fourierCoefficient : Rows.SmallPrimeFrobeniusRow → ℚ
    coefficientMatchesFrobenius : ∀ row →
      fourierCoefficient row
      ≡ Rows.signedToRational (Rows.frobeniusTrace row)
    weightTwoBoundary : Set
    heckeEigenformBoundary : Set

open SelectedModularCoefficientCandidate public

modularRowFactorValue :
  SelectedModularCoefficientCandidate →
  Rows.SmallPrimeFrobeniusRow → ℚ → ℚ
modularRowFactorValue candidate row T =
  1ℚ - fourierCoefficient candidate row * T
    + Rows.natToRational (Rows.prime row) * T * T

selectedModularEulerDenominator :
  SelectedModularCoefficientCandidate → ℚ → ℚ
selectedModularEulerDenominator candidate T =
  Euler.productList L.rationalSemiring
    (mapList
      (λ row → modularRowFactorValue candidate row T)
      Rows.smallPrimeRows)

localFrobeniusModularAgreement :
  ∀ candidate row T →
  rowFactorValue row T ≡ modularRowFactorValue candidate row T
localFrobeniusModularAgreement candidate row T
    with coefficientMatchesFrobenius candidate row
... | refl = refl

finiteListProductAgreement :
  ∀ candidate T rows →
  Euler.productList L.rationalSemiring
    (mapList (λ row → rowFactorValue row T) rows)
  ≡ Euler.productList L.rationalSemiring
    (mapList (λ row → modularRowFactorValue candidate row T) rows)
finiteListProductAgreement candidate T [] = refl
finiteListProductAgreement candidate T (row ∷ rows) =
  multiplyCongruence
    (localFrobeniusModularAgreement candidate row T)
    (finiteListProductAgreement candidate T rows)
  where
    multiplyCongruence : ∀ {a a' b b' : ℚ} →
      a ≡ a' → b ≡ b' → a * b ≡ a' * b'
    multiplyCongruence refl refl = refl

selectedCoefficientAgreementGivesEulerAgreement :
  ∀ candidate T →
  smallPrimeEulerDenominator T
  ≡ selectedModularEulerDenominator candidate T
selectedCoefficientAgreementGivesEulerAgreement candidate T =
  finiteListProductAgreement candidate T Rows.smallPrimeRows

canonicalSelectedModularCandidate : SelectedModularCoefficientCandidate
canonicalSelectedModularCandidate = record
  { fourierCoefficient = λ row →
      Rows.signedToRational (Rows.frobeniusTrace row)
  ; coefficientMatchesFrobenius = λ row → refl
  ; weightTwoBoundary = ⊤
  ; heckeEigenformBoundary = ⊤
  }

canonicalSmallPrimeEulerAgreement : ∀ T →
  smallPrimeEulerDenominator T
  ≡ selectedModularEulerDenominator canonicalSelectedModularCandidate T
canonicalSmallPrimeEulerAgreement T =
  selectedCoefficientAgreementGivesEulerAgreement
    canonicalSelectedModularCandidate T
