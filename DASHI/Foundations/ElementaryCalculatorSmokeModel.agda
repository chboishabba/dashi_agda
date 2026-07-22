module DASHI.Foundations.ElementaryCalculatorSmokeModel where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.EMLAnalyticDomain
open import DASHI.Foundations.EMLConcreteSmokeModel
open import DASHI.Foundations.ElementaryCalculator
open import DASHI.Foundations.ElementaryCalculatorSemantics
open import DASHI.Foundations.ElementaryCalculatorAnalyticPackage

------------------------------------------------------------------------
-- Concrete structured semantics over the singleton smoke carrier.  This is
-- deliberately mathematically degenerate, but it exercises all 36 calculator
-- constructors, their primitive-law record, definedness transport, and final
-- EML receipt without adding analytic authority.

smokeCalculatorSemantics : CalculatorSemanticModel smokeModel
smokeCalculatorSemantics =
  record
    { integerS = λ _ → singleton
    ; rationalS = λ _ → singleton
    ; piS = singleton
    ; eS = singleton
    ; iS = singleton
    ; minusOneS = singleton
    ; oneS = singleton
    ; twoS = singleton
    ; expS = λ _ → singleton
    ; logS = λ _ → singleton
    ; inverseS = λ _ → singleton
    ; halfS = λ _ → singleton
    ; negateS = λ _ → singleton
    ; sqrtS = λ _ → singleton
    ; squareS = λ _ → singleton
    ; sigmoidS = λ _ → singleton
    ; sinS = λ _ → singleton
    ; cosS = λ _ → singleton
    ; tanS = λ _ → singleton
    ; arcSinS = λ _ → singleton
    ; arcCosS = λ _ → singleton
    ; arcTanS = λ _ → singleton
    ; sinhS = λ _ → singleton
    ; coshS = λ _ → singleton
    ; tanhS = λ _ → singleton
    ; arcSinhS = λ _ → singleton
    ; arcCoshS = λ _ → singleton
    ; arcTanhS = λ _ → singleton
    ; addS = λ _ _ → singleton
    ; subtractS = λ _ _ → singleton
    ; multiplyS = λ _ _ → singleton
    ; divideS = λ _ _ → singleton
    ; logBaseS = λ _ _ → singleton
    ; powerS = λ _ _ → singleton
    ; averageS = λ _ _ → singleton
    ; hypotenuseS = λ _ _ → singleton
    }

smokeCalculatorPrimitiveLaws :
  CalculatorPrimitiveLaws smokeModel smokeCalculatorSemantics
smokeCalculatorPrimitiveLaws =
  record
    { integerLaw = λ _ → refl
    ; rationalLaw = λ _ → refl
    ; piLaw = refl
    ; eLaw = refl
    ; iLaw = refl
    ; minusOneLaw = refl
    ; oneLaw = refl
    ; twoLaw = refl
    ; expLaw = λ _ → refl
    ; logLaw = λ _ → refl
    ; inverseLaw = λ _ → refl
    ; halfLaw = λ _ → refl
    ; negateLaw = λ _ → refl
    ; sqrtLaw = λ _ → refl
    ; squareLaw = λ _ → refl
    ; sigmoidLaw = λ _ → refl
    ; sinLaw = λ _ → refl
    ; cosLaw = λ _ → refl
    ; tanLaw = λ _ → refl
    ; arcSinLaw = λ _ → refl
    ; arcCosLaw = λ _ → refl
    ; arcTanLaw = λ _ → refl
    ; sinhLaw = λ _ → refl
    ; coshLaw = λ _ → refl
    ; tanhLaw = λ _ → refl
    ; arcSinhLaw = λ _ → refl
    ; arcCoshLaw = λ _ → refl
    ; arcTanhLaw = λ _ → refl
    ; addLaw = λ _ _ → refl
    ; subtractLaw = λ _ _ → refl
    ; multiplyLaw = λ _ _ → refl
    ; divideLaw = λ _ _ → refl
    ; logBaseLaw = λ _ _ → refl
    ; powerLaw = λ _ _ → refl
    ; averageLaw = λ _ _ → refl
    ; hypotenuseLaw = λ _ _ → refl
    }

allSourceDefined :
  ∀ ρ t →
  DefinedSource smokeModel smokeAdmissibility ρ t
allSourceDefined ρ oneE = oneDefined
allSourceDefined ρ (varE x) = varDefined x
allSourceDefined ρ (expE t) =
  expDefined (allSourceDefined ρ t) top
allSourceDefined ρ (logE t) =
  logDefined (allSourceDefined ρ t) top
allSourceDefined ρ (subE s t) =
  subDefined
    (allSourceDefined ρ s)
    (allSourceDefined ρ t)
    top

smokeCalculatorAnalyticPackage :
  CalculatorAnalyticPackage smokeModel
smokeCalculatorAnalyticPackage =
  record
    { emlAnalyticPackage = smokeAnalyticPackage
    ; calculatorSemantics = smokeCalculatorSemantics
    ; calculatorPrimitiveLaws = smokeCalculatorPrimitiveLaws
    ; CalculatorDomain = λ _ _ → Top
    ; calculatorSourceDefined =
        λ ρ t _ → allSourceDefined ρ (lowerCalculator t)
    }

smokeCalculatorUniversalityReceipt :
  CalculatorUniversalityReceipt smokeModel
smokeCalculatorUniversalityReceipt =
  record
    { analyticPackage = smokeCalculatorAnalyticPackage
    ; singleComputationalNode = true
    ; completeTableOneSyntax = true
    ; branchAndDefinednessTracked = true
    ; singleComputationalNodeIsTrue = refl
    ; completeTableOneSyntaxIsTrue = refl
    ; branchAndDefinednessTrackedIsTrue = refl
    }

smokeStructuredCompileCorrect :
  ∀ ρ t →
  evalEML smokeModel ρ (compileCalculator t)
  ≡ evalSemanticCalculator smokeCalculatorSemantics ρ t
smokeStructuredCompileCorrect =
  calculatorCompiledHasMeaning smokeCalculatorAnalyticPackage
