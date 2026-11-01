module DASHI.Physics.ClaySupportingResidenceTimeAlgebra where

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat using (_≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; *-monoʳ-≤; *-comm; *-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
open ≡-Reasoning

residenceAlgebraLemma :
  (measureE lambda N2 C : Nat) →
  (integratedDanger : Nat) →
  (lambda * measureE ≤ integratedDanger) →
  (N2 * integratedDanger ≤ C) →
  (measureE * (lambda * N2) ≤ C)
residenceAlgebraLemma measureE lambda N2 C integratedDanger hyp1 hyp2 =
  let
    eq : measureE * (lambda * N2) ≡ N2 * (lambda * measureE)
    eq = begin
      measureE * (lambda * N2)
        ≡⟨ sym (*-assoc measureE lambda N2) ⟩
      (measureE * lambda) * N2
        ≡⟨ cong (λ w → w * N2) (*-comm measureE lambda) ⟩
      (lambda * measureE) * N2
        ≡⟨ *-comm (lambda * measureE) N2 ⟩
      N2 * (lambda * measureE)
        ∎

    step1 : N2 * (lambda * measureE) ≤ N2 * integratedDanger
    step1 = *-monoʳ-≤ N2 hyp1

    step2 : N2 * (lambda * measureE) ≤ C
    step2 = ≤-trans step1 hyp2
  in
  Relation.Binary.PropositionalEquality.subst (λ w → w ≤ C) (sym eq) step2
