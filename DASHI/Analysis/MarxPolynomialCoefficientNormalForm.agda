module DASHI.Analysis.MarxPolynomialCoefficientNormalForm where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Set₁)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxPolynomialDifferential
open import DASHI.Analysis.MarxPowerRuleNormalisation

------------------------------------------------------------------------
-- Coefficient-list presentation
--
--   [a0,a1,...,an]  |->  sum_k ak*x^k.

record CoefficientPolynomial
  (A : MarxAlgebra)
  : Set where
  constructor coefficientPolynomial
  field
    coefficients : List (Carrier A)

open CoefficientPolynomial public

coefficientTermsFrom :
  {A : MarxAlgebra} →
  Nat →
  List (Carrier A) →
  Carrier A →
  List (Carrier A)
coefficientTermsFrom degree [] x = []
coefficientTermsFrom {A} degree (a ∷ rest) x =
  _*_ A a (powerFunction degree x)
  ∷ coefficientTermsFrom (suc degree) rest x

sumCoefficients :
  {A : MarxAlgebra} →
  List (Carrier A) → Carrier A
sumCoefficients {A} [] = zero A
sumCoefficients {A} (a ∷ rest) =
  _+_ A a (sumCoefficients rest)

interpretCoefficientPolynomial :
  {A : MarxAlgebra} →
  CoefficientPolynomial A →
  Function A
interpretCoefficientPolynomial polynomial x =
  sumCoefficients
    (coefficientTermsFrom zero (coefficients polynomial) x)

------------------------------------------------------------------------
-- The derivative coefficient list is generated with its literal natural
-- multiplier, preserving the zero constant slot explicitly.

derivativeCoefficientsFrom :
  {A : MarxAlgebra} →
  Nat →
  List (Carrier A) →
  List (Carrier A)
derivativeCoefficientsFrom degree [] = []
derivativeCoefficientsFrom {A} degree (a ∷ rest) =
  natScale degree a
  ∷ derivativeCoefficientsFrom (suc degree) rest

dropConstant :
  {A : MarxAlgebra} →
  List (Carrier A) →
  List (Carrier A)
dropConstant [] = []
dropConstant (_ ∷ rest) = rest

coefficientDerivative :
  {A : MarxAlgebra} →
  CoefficientPolynomial A →
  CoefficientPolynomial A
coefficientDerivative polynomial =
  coefficientPolynomial
    (derivativeCoefficientsFrom
      (suc zero)
      (dropConstant (coefficients polynomial)))

------------------------------------------------------------------------
-- Transport between the coefficient list and the structurally differentiated
-- tree requires collection/distributivity normalisation.  That exact theorem
-- is isolated as a reusable authority rather than hidden in the evaluator.

record CoefficientPolynomialNormalisation
  (A : MarxAlgebra)
  : Set₁ where
  field
    coefficientFactorisation :
      (p : CoefficientPolynomial A) →
      MarxFactorisation A (interpretCoefficientPolynomial p)

    polynomialDerivativeCoefficientForm :
      (p : CoefficientPolynomial A) →
      (x : Carrier A) →
      marxDerivative (coefficientFactorisation p) x
      ≡ interpretCoefficientPolynomial (coefficientDerivative p) x

open CoefficientPolynomialNormalisation public

polynomialDerivativeCoefficientFormTheorem :
  {A : MarxAlgebra} →
  (N : CoefficientPolynomialNormalisation A) →
  (p : CoefficientPolynomial A) →
  (x : Carrier A) →
  marxDerivative (coefficientFactorisation N p) x
  ≡ interpretCoefficientPolynomial (coefficientDerivative p) x
polynomialDerivativeCoefficientFormTheorem =
  polynomialDerivativeCoefficientForm
