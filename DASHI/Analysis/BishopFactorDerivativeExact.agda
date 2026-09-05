module DASHI.Analysis.BishopFactorDerivativeExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as Bishop
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as PowerFactor
import DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact as Power

------------------------------------------------------------------------
-- BISHOP FACTORISATION DERIVATIVE
--
-- A derivative receipt is division-free.  It owns an exact first-order
-- factorisation
--
--   f(x+h) - f(x) ~= h q(h)
--
-- and requires q(h_j) -> d for every Bishop sequence h_j -> 0.  Thus no
-- nonzero-side-condition on h and no quotient by h are needed.
------------------------------------------------------------------------

record BishopFactorDerivativeAt
    (f : Bishop.ℝ → Bishop.ℝ)
    (point derivativeValue : Bishop.ℝ) : Set where
  field
    quotient : Bishop.ℝ → Bishop.ℝ

    incrementFactorisation : ∀ h →
      Bishop._≃_
        (Bishop._-_
          (f (Bishop._+_ point h))
          (f point))
        (Bishop._*_ h (quotient h))

    quotientConvergesOnNullSequences :
      ∀ {perturbation : Nat → Bishop.ℝ} →
      BishopSequence._ConvergesTo_ perturbation Bishop.0ℝ →
      BishopSequence._ConvergesTo_
        (λ index → quotient (perturbation index))
        derivativeValue

open BishopFactorDerivativeAt public

------------------------------------------------------------------------
-- Basic derivative algebra.
------------------------------------------------------------------------

factorDerivativeZero :
  ∀ point →
  BishopFactorDerivativeAt
    (λ _ → Bishop.0ℝ)
    point Bishop.0ℝ
factorDerivativeZero point = record
  { quotient = λ _ → Bishop.0ℝ
  ; incrementFactorisation = λ h →
      let open BishopP.ℝ-Solver
      in solve 1
        (λ h′ → Κ 0ℚᵘ ⊖ Κ 0ℚᵘ ⊜ h′ ⊗ Κ 0ℚᵘ)
        BishopP.≃-refl h
  ; quotientConvergesOnNullSequences = λ perturbationConverges →
      PowerFactor.constantConverges Bishop.0ℝ
  }

factorDerivativeScale :
  ∀ {f point derivativeValue} →
  (coefficient : Bishop.ℝ) →
  BishopFactorDerivativeAt f point derivativeValue →
  BishopFactorDerivativeAt
    (λ x → Bishop._*_ coefficient (f x))
    point
    (Bishop._*_ coefficient derivativeValue)
factorDerivativeScale {f} {point} {derivativeValue} coefficient D = record
  { quotient = λ h → Bishop._*_ coefficient (quotient D h)
  ; incrementFactorisation = λ h →
      let
        open BishopP.ℝ-Solver
        functionDifference =
          Bishop._-_
            (f (Bishop._+_ point h))
            (f point)
      in
      BishopP.≃-trans
        (solve 3
          (λ c fh fx → c ⊗ fh ⊖ c ⊗ fx ⊜ c ⊗ (fh ⊖ fx))
          BishopP.≃-refl
          coefficient
          (f (Bishop._+_ point h))
          (f point))
        (BishopP.≃-trans
          (BishopP.*-cong
            BishopP.≃-refl
            (incrementFactorisation D h))
          (solve 3
            (λ c h′ q → c ⊗ (h′ ⊗ q) ⊜ h′ ⊗ (c ⊗ q))
            BishopP.≃-refl
            coefficient h (quotient D h)))
  ; quotientConvergesOnNullSequences = λ {perturbation} perturbationConverges →
      BishopSequence.xₙyₙ→x₀y₀
        (coefficient , PowerFactor.constantConverges coefficient)
        (derivativeValue ,
          quotientConvergesOnNullSequences D perturbationConverges)
  }

factorDerivativeAdd :
  ∀ {f g point df dg} →
  BishopFactorDerivativeAt f point df →
  BishopFactorDerivativeAt g point dg →
  BishopFactorDerivativeAt
    (λ x → Bishop._+_ (f x) (g x))
    point
    (Bishop._+_ df dg)
factorDerivativeAdd {f} {g} {point} {df} {dg} F G = record
  { quotient = λ h → Bishop._+_ (quotient F h) (quotient G h)
  ; incrementFactorisation = λ h →
      let open BishopP.ℝ-Solver in
      BishopP.≃-trans
        (solve 4
          (λ fh gh fx gx →
            (fh ⊕ gh) ⊖ (fx ⊕ gx)
            ⊜ (fh ⊖ fx) ⊕ (gh ⊖ gx))
          BishopP.≃-refl
          (f (Bishop._+_ point h))
          (g (Bishop._+_ point h))
          (f point)
          (g point))
        (BishopP.≃-trans
          (BishopP.+-cong
            (incrementFactorisation F h)
            (incrementFactorisation G h))
          (solve 3
            (λ h′ qf qg →
              (h′ ⊗ qf) ⊕ (h′ ⊗ qg)
              ⊜ h′ ⊗ (qf ⊕ qg))
            BishopP.≃-refl
            h (quotient F h) (quotient G h)))
  ; quotientConvergesOnNullSequences = λ {perturbation} perturbationConverges →
      BishopSequence.xₙ+yₙ→x₀+y₀
        (df , quotientConvergesOnNullSequences F perturbationConverges)
        (dg , quotientConvergesOnNullSequences G perturbationConverges)
  }

factorDerivativeCongruence :
  ∀ {f g point df dg} →
  (functionEquivalent : ∀ x → Bishop._≃_ (f x) (g x)) →
  Bishop._≃_ df dg →
  BishopFactorDerivativeAt g point dg →
  BishopFactorDerivativeAt f point df
factorDerivativeCongruence {f} {g} {point} {df} {dg}
    functionEquivalent derivativeEquivalent G = record
  { quotient = quotient G
  ; incrementFactorisation = λ h →
      BishopP.≃-trans
        (BishopP.+-cong
          (functionEquivalent (Bishop._+_ point h))
          (BishopP.-‿cong (functionEquivalent point)))
        (incrementFactorisation G h)
  ; quotientConvergesOnNullSequences = λ perturbationConverges →
      BishopSequence.xₙ→x∧x≃y⇒xₙ→y
        (quotientConvergesOnNullSequences G perturbationConverges)
        (BishopP.≃-symm derivativeEquivalent)
  }

------------------------------------------------------------------------
-- Powers are analytic in the factorisation sense.
------------------------------------------------------------------------

powerDifferenceQuotientAtZeroIsDerivative :
  ∀ n x →
  Bishop._≃_
    (PowerFactor.powerDifferenceQuotient x Bishop.0ℝ n)
    (Power.powerDerivative n x)
powerDifferenceQuotientAtZeroIsDerivative zero x = BishopP.≃-refl
powerDifferenceQuotientAtZeroIsDerivative (suc n) x =
  BishopP.≃-symm
    (PowerFactor.powerDerivativeIsDifferenceQuotientAtZero x n)

powerFactorDerivative :
  ∀ n x →
  BishopFactorDerivativeAt
    (λ value → Bishop.pow value n)
    x
    (Power.powerDerivative n x)
powerFactorDerivative n x = record
  { quotient = PowerFactor.powerDifferenceQuotient x
  ; incrementFactorisation = λ h →
      PowerFactor.powerDifferenceFactorisation x h n
  ; quotientConvergesOnNullSequences = λ perturbationConverges →
      BishopSequence.xₙ→x∧x≃y⇒xₙ→y
        (PowerFactor.powerDifferenceQuotientConvergesAtZero
          x n perturbationConverges)
        (powerDifferenceQuotientAtZeroIsDerivative n x)
  }

record Status : Set where
  field
    divisionFreeDerivativeSemanticsOwned : Bool
    zeroRuleOwned : Bool
    additionRuleOwned : Bool
    scalarRuleOwned : Bool
    setoidCongruenceOwned : Bool
    powerAnalyticDerivativeOwned : Bool

    divisionFreeDerivativeSemanticsOwnedIsTrue : divisionFreeDerivativeSemanticsOwned ≡ true
    zeroRuleOwnedIsTrue : zeroRuleOwned ≡ true
    additionRuleOwnedIsTrue : additionRuleOwned ≡ true
    scalarRuleOwnedIsTrue : scalarRuleOwned ≡ true
    setoidCongruenceOwnedIsTrue : setoidCongruenceOwned ≡ true
    powerAnalyticDerivativeOwnedIsTrue : powerAnalyticDerivativeOwned ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { divisionFreeDerivativeSemanticsOwned = true
  ; zeroRuleOwned = true
  ; additionRuleOwned = true
  ; scalarRuleOwned = true
  ; setoidCongruenceOwned = true
  ; powerAnalyticDerivativeOwned = true
  ; divisionFreeDerivativeSemanticsOwnedIsTrue = refl
  ; zeroRuleOwnedIsTrue = refl
  ; additionRuleOwnedIsTrue = refl
  ; scalarRuleOwnedIsTrue = refl
  ; setoidCongruenceOwnedIsTrue = refl
  ; powerAnalyticDerivativeOwnedIsTrue = refl
  }
