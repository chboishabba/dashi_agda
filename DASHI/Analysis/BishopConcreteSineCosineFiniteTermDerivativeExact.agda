module DASHI.Analysis.BishopConcreteSineCosineFiniteTermDerivativeExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (1ℚᵘ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact as Power
import DASHI.Analysis.BishopNaturalScaleEmbeddingBridgeExact as Scale
import DASHI.Analysis.BishopInverseFactorialDerivativeCoefficientExact as Coefficient
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms

------------------------------------------------------------------------
-- INDEX IDENTITIES
------------------------------------------------------------------------

oddIsSuccessorEven :
  ∀ index → Estimates.oddExponent index ≡ suc (Estimates.evenExponent index)
oddIsSuccessorEven zero = refl
oddIsSuccessorEven (suc index) =
  cong suc (cong suc (oddIsSuccessorEven index))

evenSuccessorIsSuccessorOdd :
  ∀ index →
  Estimates.evenExponent (suc index) ≡ suc (Estimates.oddExponent index)
evenSuccessorIsSuccessorOdd index =
  cong suc (oddIsSuccessorEven index)

------------------------------------------------------------------------
-- ALGEBRA HELPERS
------------------------------------------------------------------------

coefficientTimesScaledPower :
  ∀ n coefficient power →
  Bishop._≃_
    (Bishop._*_
      coefficient
      (Power.natScale (suc n) power))
    (Bishop._*_
      (Power.natScale (suc n) coefficient)
      power)
coefficientTimesScaledPower n coefficient power =
  let
    embedded = NatReal.natReal (suc n)
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-cong
      BishopP.≃-refl
      (Scale.recursiveScaleIsEmbeddedNaturalMultiply (suc n) power))
    (BishopP.≃-trans
      (solve 3
        (λ c natural p → c ⊗ (natural ⊗ p) ⊜ (natural ⊗ c) ⊗ p)
        BishopP.≃-refl
        coefficient embedded power)
      (BishopP.*-cong
        (BishopP.≃-symm
          (Scale.recursiveScaleIsEmbeddedNaturalMultiply
            (suc n) coefficient))
        BishopP.≃-refl))

alternatingSignSuccessor :
  ∀ index →
  Bishop._≃_
    (Terms.alternatingSign (suc index))
    (Bishop.-_ (Terms.alternatingSign index))
alternatingSignSuccessor index =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ sign → sign ⊗ (⊝ Κ 1ℚᵘ) ⊜ ⊝ sign)
    BishopP.≃-refl
    (Terms.alternatingSign index)

------------------------------------------------------------------------
-- DERIVED TERM FAMILIES
--
-- These use the index-normalized exponents directly.  The two index lemmas
-- above identify them with the literal exponents in `sineSignedTerm` and the
-- successor cosine term.
------------------------------------------------------------------------

sineAlgebraicDerivedTerm : Bishop.ℝ → Nat → Bishop.ℝ
sineAlgebraicDerivedTerm point index =
  let even = Estimates.evenExponent index
  in
  Bishop._*_
    (Terms.alternatingSign index)
    (Bishop._*_
      (Exp.embed (Exp.inverseFactorial (suc even)))
      (Power.powerDerivative (suc even) point))

cosineAlgebraicDerivedTerm : Bishop.ℝ → Nat → Bishop.ℝ
cosineAlgebraicDerivedTerm point index =
  let odd = Estimates.oddExponent index
  in
  Bishop._*_
    (Terms.alternatingSign (suc index))
    (Bishop._*_
      (Exp.embed (Exp.inverseFactorial (suc odd)))
      (Power.powerDerivative (suc odd) point))

sineFiniteTermDerivativeIsCosineTerm :
  ∀ point index →
  Bishop._≃_
    (sineAlgebraicDerivedTerm point index)
    (Terms.cosineSignedTerm point index)
sineFiniteTermDerivativeIsCosineTerm point index =
  let
    even = Estimates.evenExponent index
    nextCoefficient = Exp.embed (Exp.inverseFactorial (suc even))
    power = Bishop.pow point even
  in
  BishopP.≃-trans
    (BishopP.*-cong
      BishopP.≃-refl
      (BishopP.*-cong
        BishopP.≃-refl
        (Power.powerDerivativeNatScale even point)))
    (BishopP.≃-trans
      (BishopP.*-cong
        BishopP.≃-refl
        (coefficientTimesScaledPower
          even nextCoefficient power))
      (BishopP.*-cong
        BishopP.≃-refl
        (BishopP.*-cong
          (Coefficient.scaledInverseFactorialSuccessor even)
          BishopP.≃-refl)))

cosineFiniteTermDerivativeIsNegativeSineTerm :
  ∀ point index →
  Bishop._≃_
    (cosineAlgebraicDerivedTerm point index)
    (Bishop.-_ (Terms.sineSignedTerm point index))
cosineFiniteTermDerivativeIsNegativeSineTerm point index =
  let
    odd = Estimates.oddExponent index
    sign = Terms.alternatingSign index
    nextCoefficient = Exp.embed (Exp.inverseFactorial (suc odd))
    coefficient = Exp.embed (Exp.inverseFactorial odd)
    power = Bishop.pow point odd
    signedRest = Bishop._*_ coefficient power
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-cong
      BishopP.≃-refl
      (BishopP.*-cong
        BishopP.≃-refl
        (Power.powerDerivativeNatScale odd point)))
    (BishopP.≃-trans
      (BishopP.*-cong
        BishopP.≃-refl
        (coefficientTimesScaledPower
          odd nextCoefficient power))
      (BishopP.≃-trans
        (BishopP.*-cong
          BishopP.≃-refl
          (BishopP.*-cong
            (Coefficient.scaledInverseFactorialSuccessor odd)
            BishopP.≃-refl))
        (BishopP.≃-trans
          (BishopP.*-cong
            (alternatingSignSuccessor index)
            BishopP.≃-refl)
          (solve 2
            (λ s rest → (⊝ s) ⊗ rest ⊜ ⊝ (s ⊗ rest))
            BishopP.≃-refl
            sign signedRest))))

record FiniteTrigDerivativeStatus : Set where
  field
    powerDerivativeOwned : Bool
    inverseFactorialDerivativeCoefficientOwned : Bool
    sineFiniteTermDerivativeOwned : Bool
    cosineFiniteTermDerivativeOwned : Bool

    powerDerivativeOwnedIsTrue : powerDerivativeOwned ≡ true
    inverseFactorialDerivativeCoefficientOwnedIsTrue :
      inverseFactorialDerivativeCoefficientOwned ≡ true
    sineFiniteTermDerivativeOwnedIsTrue : sineFiniteTermDerivativeOwned ≡ true
    cosineFiniteTermDerivativeOwnedIsTrue : cosineFiniteTermDerivativeOwned ≡ true

open FiniteTrigDerivativeStatus public

canonicalFiniteTrigDerivativeStatus : FiniteTrigDerivativeStatus
canonicalFiniteTrigDerivativeStatus = record
  { powerDerivativeOwned = true
  ; inverseFactorialDerivativeCoefficientOwned = true
  ; sineFiniteTermDerivativeOwned = true
  ; cosineFiniteTermDerivativeOwned = true
  ; powerDerivativeOwnedIsTrue = refl
  ; inverseFactorialDerivativeCoefficientOwnedIsTrue = refl
  ; sineFiniteTermDerivativeOwnedIsTrue = refl
  ; cosineFiniteTermDerivativeOwnedIsTrue = refl
  }
