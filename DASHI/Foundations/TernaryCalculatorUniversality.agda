module DASHI.Foundations.TernaryCalculatorUniversality where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.ElementaryCalculator
open import DASHI.Foundations.ElementaryCalculatorSemantics
open import DASHI.Foundations.ElementaryCalculatorAnalyticPackage
open import DASHI.Foundations.TernaryElementaryOperatorCandidate

------------------------------------------------------------------------
-- Exact composition theorem: the only missing mathematical input is an actual
-- TernaryRepresentsEML witness for the selected ternary operator/model.

compileCalculatorTernary :
  ∀ {TM : TernaryModel} {EM : ExpLogSubModel} →
  TernaryRepresentsEML TM EM →
  CalculatorExpr →
  TernaryExpr
compileCalculatorTernary R t =
  translate R (compileCalculator t)

compileCalculatorTernary-correct :
  ∀ {TM : TernaryModel} {EM : ExpLogSubModel} →
  (R : TernaryRepresentsEML TM EM) →
  (P : CalculatorAnalyticPackage EM) →
  ∀ (ρ : Env EM) (ρT : TEnv TM) →
  (compatible : ∀ x → ρT x ≡ embedCarrier R (ρ x)) →
  ∀ t →
  CalculatorDomain P ρ t →
  evalTernary TM ρT (compileCalculatorTernary R t)
  ≡ embedCarrier R
      (evalSemanticCalculator (calculatorSemantics P) ρ t)
compileCalculatorTernary-correct R P ρ ρT compatible t domainProof =
  trans
    (translate-correct R ρ ρT compatible (compileCalculator t))
    (congEmbed
      (calculatorCompiledHasMeaning P ρ t domainProof))
  where
    congEmbed :
      ∀ {x y} →
      x ≡ y →
      embedCarrier R x ≡ embedCarrier R y
    congEmbed refl = refl

record ConstantFreeTernaryCalculatorReceipt
  (TM : TernaryModel)
  (EM : ExpLogSubModel) : Set₁ where
  field
    ternaryRepresentsEML : TernaryRepresentsEML TM EM
    calculatorAnalyticPackage : CalculatorAnalyticPackage EM
    compileT : CalculatorExpr → TernaryExpr
    compileTIsCanonical :
      ∀ t →
      compileT t
      ≡ compileCalculatorTernary ternaryRepresentsEML t

open ConstantFreeTernaryCalculatorReceipt public

canonicalConstantFreeTernaryCalculatorReceipt :
  ∀ {TM : TernaryModel} {EM : ExpLogSubModel} →
  (R : TernaryRepresentsEML TM EM) →
  (P : CalculatorAnalyticPackage EM) →
  ConstantFreeTernaryCalculatorReceipt TM EM
canonicalConstantFreeTernaryCalculatorReceipt R P =
  record
    { ternaryRepresentsEML = R
    ; calculatorAnalyticPackage = P
    ; compileT = compileCalculatorTernary R
    ; compileTIsCanonical = λ _ → refl
    }
