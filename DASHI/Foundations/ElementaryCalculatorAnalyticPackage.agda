module DASHI.Foundations.ElementaryCalculatorAnalyticPackage where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.EMLAnalyticDomain
open import DASHI.Foundations.ElementaryCalculator
open import DASHI.Foundations.ElementaryCalculatorSemantics

------------------------------------------------------------------------
-- Final binary universality package for one selected analytic semantics.
--
-- The package simultaneously carries branch/domain-sensitive EML laws, an
-- independent named calculator semantics, its primitive lowering laws, and an
-- expression-indexed proof that both source and compiled trees are defined.

record CalculatorAnalyticPackage (M : ExpLogSubModel) : Set₁ where
  field
    emlAnalyticPackage : AnalyticEMLCompilerPackage M

    calculatorSemantics : CalculatorSemanticModel M
    calculatorPrimitiveLaws :
      CalculatorPrimitiveLaws M calculatorSemantics

    CalculatorDomain : Env M → CalculatorExpr → Set

    calculatorCompilationDefined :
      ∀ ρ t →
      CalculatorDomain ρ t →
      CompilationDefined
        M
        (admissibility emlAnalyticPackage)
        ρ
        (lowerCalculator t)

open CalculatorAnalyticPackage public

calculatorSourceDefined :
  ∀ {M : ExpLogSubModel} →
  (P : CalculatorAnalyticPackage M) →
  ∀ ρ t →
  CalculatorDomain P ρ t →
  DefinedCalculator
    M
    (admissibility (emlAnalyticPackage P))
    ρ
    t
calculatorSourceDefined P ρ t domainProof =
  sourceDefinedFromCompilation
    (calculatorCompilationDefined P ρ t domainProof)

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
  compiledDefinedFromCompilation
    (calculatorCompilationDefined P ρ t domainProof)

calculatorCompiledHasMeaning :
  ∀ {M : ExpLogSubModel} →
  (P : CalculatorAnalyticPackage M) →
  ∀ ρ t →
  CalculatorDomain P ρ t →
  evalEML M ρ (compileCalculator t)
  ≡ evalSemanticCalculator (calculatorSemantics P) ρ t
calculatorCompiledHasMeaning P ρ t domainProof
  rewrite analyticCompileCorrect
            (emlAnalyticPackage P)
            ρ
            (calculatorCompilationDefined P ρ t domainProof) =
  lowerCalculator-semantics
    (calculatorPrimitiveLaws P)
    ρ
    t

record CalculatorUniversalityReceipt (M : ExpLogSubModel) : Set₁ where
  field
    analyticPackage : CalculatorAnalyticPackage M

    singleComputationalNode : Bool
    completeTableOneSyntax : Bool
    branchAndDefinednessTracked : Bool

    singleComputationalNodeIsTrue :
      singleComputationalNode ≡ true
    completeTableOneSyntaxIsTrue :
      completeTableOneSyntax ≡ true
    branchAndDefinednessTrackedIsTrue :
      branchAndDefinednessTracked ≡ true

open CalculatorUniversalityReceipt public
