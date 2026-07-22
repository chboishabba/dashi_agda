module DASHI.Foundations.ElementaryCalculatorAnalyticPackage where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.EMLAnalyticDomain
open import DASHI.Foundations.ElementaryCalculator

------------------------------------------------------------------------
-- Final binary universality package for one selected analytic semantics.
--
-- The package simultaneously carries EML compiler laws, compiler-introduced
-- definedness, independent calculator meaning, and a domain proof for each
-- admitted expression/environment pair.

record CalculatorAnalyticPackage (M : ExpLogSubModel) : Set₁ where
  field
    emlAnalyticPackage : AnalyticEMLCompilerPackage M
    calculatorMeaning : CalculatorMeaning M

    CalculatorDomain : Env M → CalculatorExpr → Set

    calculatorSourceDefined :
      ∀ ρ t →
      CalculatorDomain ρ t →
      DefinedCalculator
        M
        (admissibility emlAnalyticPackage)
        ρ
        t

open CalculatorAnalyticPackage public

calculatorCompiledDefined :
  ∀ {M : ExpLogSubModel} →
  (P : CalculatorAnalyticPackage M) →
  ∀ ρ t →
  CalculatorDomain P ρ t →
  DefinedEML
    M
    (admissibility (emlAnalyticPackage P))
    ρ
    (compileCalculator t)
calculatorCompiledDefined P ρ t domainProof =
  compileEML-preserves-defined
    (compilerDefinedness (emlAnalyticPackage P))
    ρ
    (calculatorSourceDefined P ρ t domainProof)

calculatorCompiledHasMeaning :
  ∀ {M : ExpLogSubModel} →
  (P : CalculatorAnalyticPackage M) →
  ∀ ρ t →
  evalEML M ρ (compileCalculator t)
  ≡ meaning (calculatorMeaning P) ρ t
calculatorCompiledHasMeaning P =
  calculatorMeaningCompiles
    (laws (emlAnalyticPackage P))
    (calculatorMeaning P)

record CalculatorUniversalityReceipt (M : ExpLogSubModel) : Set₁ where
  field
    analyticPackage : CalculatorAnalyticPackage M
    singleComputationalNode : Set
    completeTableOneSyntax : Set
    branchAndDefinednessTracked : Set

open CalculatorUniversalityReceipt public
