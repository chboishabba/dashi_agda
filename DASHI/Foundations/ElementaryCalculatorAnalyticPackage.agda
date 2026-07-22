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
-- The package simultaneously carries branch/domain-sensitive EML laws,
-- compiler-introduced definedness, an independent named calculator semantics,
-- its primitive lowering laws, and a domain proof for every admitted
-- expression/environment pair.

record CalculatorAnalyticPackage (M : ExpLogSubModel) : Set₁ where
  field
    emlAnalyticPackage : AnalyticEMLCompilerPackage M

    calculatorSemantics : CalculatorSemanticModel M
    calculatorPrimitiveLaws :
      CalculatorPrimitiveLaws M calculatorSemantics

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
  CalculatorDomain P ρ t →
  evalEML M ρ (compileCalculator t)
  ≡ evalSemanticCalculator (calculatorSemantics P) ρ t
calculatorCompiledHasMeaning P ρ t domainProof
  rewrite analyticCompileCorrect
            (emlAnalyticPackage P)
            ρ
            (calculatorSourceDefined P ρ t domainProof) =
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
