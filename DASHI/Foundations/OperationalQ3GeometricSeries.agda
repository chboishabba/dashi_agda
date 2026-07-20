module DASHI.Foundations.OperationalQ3GeometricSeries where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Integer using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Solver using (module +-*-Solver)
open +-*-Solver

------------------------------------------------------------------------
-- Operational rational core embedded in the intended Q3 completion.

oneQ threeQ halfQ twoQ minusOneQ : ℚ
oneQ = 1ℚ
threeQ = + 3 / 1
halfQ = + 1 / 2
twoQ = + 2 / 1
minusOneQ = - 1ℚ

pow3Q : Nat → ℚ
pow3Q zero = 1ℚ
pow3Q (suc n) = pow3Q n * threeQ

-- Closed form for the n-term series 1 + 3 + ... + 3^(n-1).
geometricPartial : Nat → ℚ
geometricPartial n = (pow3Q n + minusOneQ) * halfQ

negativeHalfQ : ℚ
negativeHalfQ = - halfQ

geometricPartialEquation :
  (n : Nat) →
  twoQ * geometricPartial n + oneQ ≡ pow3Q n
geometricPartialEquation n =
  solve 1
    (λ x →
      ((con twoQ :* ((x :+ con minusOneQ) :* con halfQ)) :+ con oneQ)
      := x)
    refl
    (pow3Q n)

errorToNegativeHalf : Nat → ℚ
errorToNegativeHalf n = pow3Q n * halfQ

geometricErrorEquation :
  (n : Nat) →
  geometricPartial n + halfQ ≡ errorToNegativeHalf n
geometricErrorEquation n =
  solve 1
    (λ x →
      (((x :+ con minusOneQ) :* con halfQ) :+ con halfQ)
      := (x :* con halfQ))
    refl
    (pow3Q n)

------------------------------------------------------------------------
-- Proof-relevant 3-adic precision certificate.
--
-- The residual is exactly 3^n times the 3-adic unit 1/2, so its valuation
-- exponent grows by one at every refinement depth.

record ThreeAdicPrecisionCertificate (n : Nat) : Set where
  constructor threeAdicPrecisionCertificate
  field
    approximation : ℚ
    proposedLimit : ℚ
    residual : ℚ
    valuationExponent : Nat
    unitFactor : ℚ
    approximationExact : approximation ≡ geometricPartial n
    proposedLimitExact : proposedLimit ≡ negativeHalfQ
    residualExact : residual ≡ errorToNegativeHalf n
    exponentExact : valuationExponent ≡ n
    unitFactorExact : unitFactor ≡ halfQ
    residualFactorisation : residual ≡ pow3Q n * unitFactor

precisionAt : (n : Nat) → ThreeAdicPrecisionCertificate n
precisionAt n =
  threeAdicPrecisionCertificate
    (geometricPartial n)
    negativeHalfQ
    (errorToNegativeHalf n)
    n
    halfQ
    refl refl refl refl refl refl

precision0 : geometricPartial 0 ≡ 0ℚ
precision0 = refl

precision1 : geometricPartial 1 ≡ 1ℚ
precision1 = refl

precision2 : geometricPartial 2 ≡ + 4 / 1
precision2 = refl

precision3 : geometricPartial 3 ≡ + 13 / 1
precision3 = refl

record Q3CompletionAuthority : Set₁ where
  field
    Q3 : Set
    embedRational : ℚ → Q3
    valuationExponentQ3 : Q3 → Nat
    fieldLaws : Set
    rationalEmbeddingPreservesField : Set
    precisionFactorImpliesBallMembership : Set
    completeForCauchySequences : Set

record OperationalQ3GeometricSeriesBoundary : Set where
  constructor operationalQ3GeometricSeriesBoundary
  field
    rationalFieldCoreChecked : Bool
    exactPartialSumFormulaChecked : Bool
    exactResidualFactorisationChecked : Bool
    valuationExponentGrowthRecorded : Bool
    completedQ3FieldConstructedHere : Bool
    completedQ3FieldConstructedHereIsFalse :
      completedQ3FieldConstructedHere ≡ false
    realAndPadicConvergenceIdentified : Bool
    realAndPadicConvergenceIdentifiedIsFalse :
      realAndPadicConvergenceIdentified ≡ false
    interpretation : String

canonicalOperationalQ3GeometricSeriesBoundary :
  OperationalQ3GeometricSeriesBoundary
canonicalOperationalQ3GeometricSeriesBoundary =
  operationalQ3GeometricSeriesBoundary
    true true true true false refl false refl
    "the rational partial sums and exact residual 3^n/2 are machine-checkable; a reusable completed Q3 field consumes the explicit completion authority rather than being inferred from the symbol Q3"
