module DASHI.Foundations.TernaryCalculatorSmokeModel where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.EMLConcreteSmokeModel
open import DASHI.Foundations.ElementaryCalculator
open import DASHI.Foundations.ElementaryCalculatorSemantics
open import DASHI.Foundations.ElementaryCalculatorSmokeModel
open import DASHI.Foundations.TernaryElementaryOperatorCandidate
open import DASHI.Foundations.TernaryWitnessIndependentRepresentation
open import DASHI.Foundations.TernaryCalculatorUniversality

------------------------------------------------------------------------
-- Concrete singleton ternary model exercising the complete structural
-- composition.  It is a regression model only, not evidence for the analytic
-- Odrzywolek ternary candidate.

smokeTernaryModel : TernaryModel
smokeTernaryModel =
  record
    { CarrierT = Singleton
    ; ternary = λ _ _ _ → singleton
    }

smokeTernaryContexts :
  TernaryEMLContexts smokeTernaryModel smokeModel
smokeTernaryContexts =
  record
    { embedCarrierC = λ _ → singleton
    ; unitTreeC = varT zero
    ; variableTreeC = varT
    ; emlContextC = λ left right → nodeT left right left
    ; unitTreeCorrectC =
        λ ρ ρT compatible → compatible zero
    ; variableTreeCorrectC =
        λ ρ ρT compatible x → compatible x
    ; emlContextCorrectC =
        λ ρT left right x y leftCorrect rightCorrect → refl
    }

smokeTernaryRepresentsEML :
  TernaryRepresentsEML smokeTernaryModel smokeModel
smokeTernaryRepresentsEML =
  contextsGiveTernaryRepresentation smokeTernaryContexts

smokeTernaryEnvironment : TEnv smokeTernaryModel
smokeTernaryEnvironment _ = singleton

smokeEnvironmentCompatibility :
  ∀ (ρ : Env smokeModel) x →
  smokeTernaryEnvironment x
  ≡ embedCarrier smokeTernaryRepresentsEML (ρ x)
smokeEnvironmentCompatibility ρ x = refl

smokeTernaryCalculatorCorrect :
  ∀ (ρ : Env smokeModel) t →
  evalTernary
    smokeTernaryModel
    smokeTernaryEnvironment
    (compileCalculatorTernary smokeTernaryRepresentsEML t)
  ≡ embedCarrier smokeTernaryRepresentsEML
      (evalSemanticCalculator smokeCalculatorSemantics ρ t)
smokeTernaryCalculatorCorrect ρ t =
  compileCalculatorTernary-correct
    smokeTernaryRepresentsEML
    smokeCalculatorAnalyticPackage
    ρ
    smokeTernaryEnvironment
    (smokeEnvironmentCompatibility ρ)
    t
    top
