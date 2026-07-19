module DASHI.Physics.YangMills.BalabanSU2AdjointAnalyticFunctionalCalculus where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using (zeroR; oneR)
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus using
  ( ReducedAdjointOperator; reducedAd; identityCoefficient; linearCoefficient
  ; quadraticCoefficient; reducedAdjointExt; applyReducedAdjoint
  ; identityReducedAdjoint; composeReducedAdjoint
  ; applyIdentityReducedAdjoint; applyReducedComposition )

record AnalyticAdCoefficients : Set where
  constructor analyticCoefficients
  field
    valueAtZero : ℝ
    oddCoefficient : ℝ
    quadraticCoefficientValue : ℝ
open AnalyticAdCoefficients public

analyticAdReduction : AnalyticAdCoefficients → ReducedAdjointOperator
analyticAdReduction c =
  reducedAd (valueAtZero c) (oddCoefficient c) (quadraticCoefficientValue c)

dexpReducedClosedForm : ℝ → ℝ → ReducedAdjointOperator
dexpReducedClosedForm b c = reducedAd oneR b c

inverseDexpReducedClosedForm : ℝ → ℝ → ReducedAdjointOperator
inverseDexpReducedClosedForm b c = reducedAd oneR b c

reducedCoefficientClosure :
  ∀ {operator : ReducedAdjointOperator} →
  identityCoefficient operator ≡ oneR →
  linearCoefficient operator ≡ zeroR →
  quadraticCoefficient operator ≡ zeroR →
  operator ≡ identityReducedAdjoint
reducedCoefficientClosure a b c = reducedAdjointExt a b c

inverseDexpActsLeft :
  ∀ Y dexp inverseDexp →
  composeReducedAdjoint Y inverseDexp dexp ≡ identityReducedAdjoint →
  ∀ X → applyReducedAdjoint Y inverseDexp (applyReducedAdjoint Y dexp X) ≡ X
inverseDexpActsLeft Y dexp inverseDexp closed X =
  trans (applyReducedComposition Y inverseDexp dexp X)
    (trans (cong (λ op → applyReducedAdjoint Y op X) closed)
      (applyIdentityReducedAdjoint Y X))

inverseDexpActsRight :
  ∀ Y dexp inverseDexp →
  composeReducedAdjoint Y dexp inverseDexp ≡ identityReducedAdjoint →
  ∀ X → applyReducedAdjoint Y dexp (applyReducedAdjoint Y inverseDexp X) ≡ X
inverseDexpActsRight Y dexp inverseDexp closed X =
  trans (applyReducedComposition Y dexp inverseDexp X)
    (trans (cong (λ op → applyReducedAdjoint Y op X) closed)
      (applyIdentityReducedAdjoint Y X))

coefficientRemovableAtZero :
  ∀ left right →
  valueAtZero left ≡ valueAtZero right →
  oddCoefficient left ≡ oddCoefficient right →
  quadraticCoefficientValue left ≡ quadraticCoefficientValue right →
  analyticAdReduction left ≡ analyticAdReduction right
coefficientRemovableAtZero left right a b c = reducedAdjointExt a b c

record CoefficientDerivativeBounds : Set₁ where
  field
    radius : ℝ
    identityDerivativeBound : ℝ
    oddDerivativeBound : ℝ
    quadraticDerivativeBound : ℝ
open CoefficientDerivativeBounds public
