module DASHI.Analysis.BishopConcreteTrigAnalyticTermDerivativeExact where

open import Agda.Builtin.Nat using (Nat; suc)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopConcreteSineCosineFiniteTermDerivativeExact as Finite
import DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact as Power
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms

------------------------------------------------------------------------
-- LITERAL SIGNED TRIG TERMS ARE ANALYTICALLY DIFFERENTIABLE
--
-- Each term is a constant scalar multiple of a power.  The Bishop factor
-- derivative already owns the power derivative and constant-scalar rule.
-- Index arithmetic then transports the resulting analytic derivative value to
-- the already-owned algebraic derivative normal forms.
------------------------------------------------------------------------

sineRawDerivative : Bishop.ℝ → Nat → Bishop.ℝ
sineRawDerivative point index =
  let exponent = Estimates.oddExponent index
  in
  Bishop._*_
    (Terms.alternatingSign index)
    (Bishop._*_
      (Exp.embed (Exp.inverseFactorial exponent))
      (Power.powerDerivative exponent point))

cosineRawDerivative : Bishop.ℝ → Nat → Bishop.ℝ
cosineRawDerivative point index =
  let exponent = Estimates.evenExponent (suc index)
  in
  Bishop._*_
    (Terms.alternatingSign (suc index))
    (Bishop._*_
      (Exp.embed (Exp.inverseFactorial exponent))
      (Power.powerDerivative exponent point))

sineRawIsAlgebraic :
  ∀ point index →
  Bishop._≃_
    (sineRawDerivative point index)
    (Finite.sineAlgebraicDerivedTerm point index)
sineRawIsAlgebraic point index
  rewrite Finite.oddIsSuccessorEven index =
  BishopP.≃-refl

cosineRawIsAlgebraic :
  ∀ point index →
  Bishop._≃_
    (cosineRawDerivative point index)
    (Finite.cosineAlgebraicDerivedTerm point index)
cosineRawIsAlgebraic point index
  rewrite Finite.evenSuccessorIsSuccessorOdd index =
  BishopP.≃-refl

sineTermRawDerivative :
  ∀ point index →
  Factor.BishopFactorDerivativeAt
    (λ value → Terms.sineSignedTerm value index)
    point
    (sineRawDerivative point index)
sineTermRawDerivative point index =
  let
    exponent = Estimates.oddExponent index
    coefficient = Exp.embed (Exp.inverseFactorial exponent)
    signed = Terms.alternatingSign index
  in
  Factor.factorDerivativeScale signed
    (Factor.factorDerivativeScale coefficient
      (Factor.powerFactorDerivative exponent point))

cosineSuccessorTermRawDerivative :
  ∀ point index →
  Factor.BishopFactorDerivativeAt
    (λ value → Terms.cosineSignedTerm value (suc index))
    point
    (cosineRawDerivative point index)
cosineSuccessorTermRawDerivative point index =
  let
    exponent = Estimates.evenExponent (suc index)
    coefficient = Exp.embed (Exp.inverseFactorial exponent)
    signed = Terms.alternatingSign (suc index)
  in
  Factor.factorDerivativeScale signed
    (Factor.factorDerivativeScale coefficient
      (Factor.powerFactorDerivative exponent point))

sineTermAnalyticDerivative :
  ∀ point index →
  Factor.BishopFactorDerivativeAt
    (λ value → Terms.sineSignedTerm value index)
    point
    (Finite.sineAlgebraicDerivedTerm point index)
sineTermAnalyticDerivative point index =
  Factor.factorDerivativeCongruence
    (λ _ → BishopP.≃-refl)
    (sineRawIsAlgebraic point index)
    (sineTermRawDerivative point index)

cosineSuccessorTermAnalyticDerivative :
  ∀ point index →
  Factor.BishopFactorDerivativeAt
    (λ value → Terms.cosineSignedTerm value (suc index))
    point
    (Finite.cosineAlgebraicDerivedTerm point index)
cosineSuccessorTermAnalyticDerivative point index =
  Factor.factorDerivativeCongruence
    (λ _ → BishopP.≃-refl)
    (cosineRawIsAlgebraic point index)
    (cosineSuccessorTermRawDerivative point index)

------------------------------------------------------------------------
-- The normal forms were already proved equal to cosine and minus-sine terms.
-- This file supplies the previously missing analytic interpretation.
------------------------------------------------------------------------

sineTermAnalyticDerivativeIsCosineTerm :
  ∀ point index →
  Factor.BishopFactorDerivativeAt
    (λ value → Terms.sineSignedTerm value index)
    point
    (Terms.cosineSignedTerm point index)
sineTermAnalyticDerivativeIsCosineTerm point index =
  Factor.factorDerivativeCongruence
    (λ _ → BishopP.≃-refl)
    (Finite.sineFiniteTermDerivativeIsCosineTerm point index)
    (sineTermAnalyticDerivative point index)

cosineSuccessorTermAnalyticDerivativeIsNegativeSine :
  ∀ point index →
  Factor.BishopFactorDerivativeAt
    (λ value → Terms.cosineSignedTerm value (suc index))
    point
    (Bishop.-_ (Terms.sineSignedTerm point index))
cosineSuccessorTermAnalyticDerivativeIsNegativeSine point index =
  Factor.factorDerivativeCongruence
    (λ _ → BishopP.≃-refl)
    (Finite.cosineFiniteTermDerivativeIsNegativeSineTerm point index)
    (cosineSuccessorTermAnalyticDerivative point index)

record Status : Set where
  field
    sineTermAnalyticDerivativeOwned : Bool
    cosineSuccessorTermAnalyticDerivativeOwned : Bool
    algebraicAnalyticWeldClosed : Bool

    sineTermAnalyticDerivativeOwnedIsTrue : sineTermAnalyticDerivativeOwned ≡ true
    cosineSuccessorTermAnalyticDerivativeOwnedIsTrue :
      cosineSuccessorTermAnalyticDerivativeOwned ≡ true
    algebraicAnalyticWeldClosedIsTrue : algebraicAnalyticWeldClosed ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { sineTermAnalyticDerivativeOwned = true
  ; cosineSuccessorTermAnalyticDerivativeOwned = true
  ; algebraicAnalyticWeldClosed = true
  ; sineTermAnalyticDerivativeOwnedIsTrue = refl
  ; cosineSuccessorTermAnalyticDerivativeOwnedIsTrue = refl
  ; algebraicAnalyticWeldClosedIsTrue = refl
  }
