module DASHI.Physics.Closure.NSTriadKNRationalInfinityShellBernsteinRound465Exact where

------------------------------------------------------------------------
-- ROUND465 / EXISTING RATIONAL BERNSTEIN -> R234 DEEP-FL PAYMENT
--
-- BIDI CORRECTION
-- ---------------
-- An earlier draft of this round re-proved finite rational Cauchy--Schwarz.
-- That was parallel implementation: NSTriadKNRationalFiniteBernstein already
-- owns the exact theorem
--
--   (sum a_i)^2 <= |S| * sum a_i^2.
--
-- This owner now does only the missing composition.  It multiplies that
-- existing Bernstein estimate by a nonnegative high-shell energy and compiles
-- the result into R234.DeepFarLowScalarPayment.  A physical shell producer only
-- has to show that the literal finite support cardinality is below the chosen
-- high-derivative coefficient; no Cauchy--Schwarz theorem is duplicated here.
--
-- The dyadic/infinity-cube owners may be used upstream to pay that cardinality
-- comparison.  Constants such as 27 are therefore retained where they belong,
-- rather than silently normalized away in this adapter.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalFiniteBernstein as Bernstein
import DASHI.Physics.Closure.NSTriadKNDeepFarLowCriticalShoulderRound234Exact as R234

coefficientNormSquaredNonnegative :
  (coefficients : List ℚ) →
  0ℚ ≤ Bernstein.coefficientNormSquared coefficients
coefficientNormSquaredNonnegative [] = ℚP.≤-refl
coefficientNormSquaredNonnegative (x ∷ xs) =
  Rational.addNonnegative
    (Rational.squareNonnegative x)
    (coefficientNormSquaredNonnegative xs)

supportCardinalityNonnegative :
  (coefficients : List ℚ) →
  0ℚ ≤ Bernstein.supportCardinality coefficients
supportCardinalityNonnegative [] = ℚP.≤-refl
supportCardinalityNonnegative (_ ∷ xs) =
  Rational.addNonnegative
    (Rational.squareNonnegative (Data.Rational.Base.1ℚ))
    (supportCardinalityNonnegative xs)
  where
  open import Data.Rational.Base using (1ℚ)

record DeepFarLowFiniteBernsteinData : Set where
  constructor deep-far-low-finite-bernstein-data
  field
    coefficients : List ℚ
    highEnergy highDerivativeCoefficient productMass : ℚ

    highEnergyNN : 0ℚ ≤ highEnergy
    highDerivativeCoefficientNN : 0ℚ ≤ highDerivativeCoefficient

    supportCardinalityPaidByDerivative :
      Bernstein.supportCardinality coefficients ≤ highDerivativeCoefficient

    productMassBelowBernsteinInput :
      productMass
      ≤ Rational.square (Bernstein.coefficientSum coefficients) * highEnergy

open DeepFarLowFiniteBernsteinData public

bernsteinTimesHighEnergy :
  (D : DeepFarLowFiniteBernsteinData) →
  Rational.square (Bernstein.coefficientSum (coefficients D)) * highEnergy D
  ≤ Bernstein.supportCardinality (coefficients D)
      * Bernstein.coefficientNormSquared (coefficients D) * highEnergy D
bernsteinTimesHighEnergy D =
  let
    base = Bernstein.finiteBernsteinSquared (coefficients D)
    instance highNNI : NonNegative (highEnergy D)
    highNNI = nonNegative (highEnergyNN D)
  in
  ℚP.*-monoʳ-≤-nonNeg (highEnergy D) base

toR234DeepFarLowScalarPayment :
  DeepFarLowFiniteBernsteinData → R234.DeepFarLowScalarPayment
toR234DeepFarLowScalarPayment D = record
  { R234.lowEnergy = Bernstein.coefficientNormSquared (coefficients D)
  ; R234.highEnergy = highEnergy D
  ; R234.bernsteinCoefficient = Bernstein.supportCardinality (coefficients D)
  ; R234.highDerivativeCoefficient = highDerivativeCoefficient D
  ; R234.productMass = productMass D
  ; R234.lowEnergyNN = coefficientNormSquaredNonnegative (coefficients D)
  ; R234.highEnergyNN = highEnergyNN D
  ; R234.bernsteinCoefficientNN = supportCardinalityNonnegative (coefficients D)
  ; R234.highDerivativeCoefficientNN = highDerivativeCoefficientNN D
  ; R234.coefficientPayment = supportCardinalityPaidByDerivative D
  ; R234.productMassBound =
      ℚP.≤-trans
        (productMassBelowBernsteinInput D)
        (bernsteinTimesHighEnergy D)
  }

deepFarLowFiniteBernsteinPaidByEnergyDissipation :
  (D : DeepFarLowFiniteBernsteinData) →
  productMass D
  ≤ Bernstein.coefficientNormSquared (coefficients D)
      * R234.highDissipation (toR234DeepFarLowScalarPayment D)
deepFarLowFiniteBernsteinPaidByEnergyDissipation D =
  R234.deepFarLowMassPaidByEnergyTimesDissipation
    (toR234DeepFarLowScalarPayment D)

round465ExistingRationalFiniteBernsteinReused : Bool
round465ExistingRationalFiniteBernsteinReused = true

round465FiniteCauchySchwarzReprovedHere : Bool
round465FiniteCauchySchwarzReprovedHere = false

round465R234ScalarPaymentCompilerConstructed : Bool
round465R234ScalarPaymentCompilerConstructed = true

round465PhysicalShellCardinalityToDerivativeWeldStillRequired : Bool
round465PhysicalShellCardinalityToDerivativeWeldStillRequired = true

round465ContainsPostulate : Bool
round465ContainsPostulate = false

round465PackageAClosed : Bool
round465PackageAClosed = false

round465ClayPromotion : Bool
round465ClayPromotion = false

round465FiniteCauchySchwarzReprovedHereIsFalse :
  round465FiniteCauchySchwarzReprovedHere ≡ false
round465FiniteCauchySchwarzReprovedHereIsFalse = refl

round465ContainsPostulateIsFalse : round465ContainsPostulate ≡ false
round465ContainsPostulateIsFalse = refl
