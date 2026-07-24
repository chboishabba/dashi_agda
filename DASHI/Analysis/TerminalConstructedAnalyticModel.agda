module DASHI.Analysis.TerminalConstructedAnalyticModel where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex
open import DASHI.Analysis.PrincipalComplexLog

------------------------------------------------------------------------
-- Exact terminal model.
--
-- This is a fully constructed, postulate-free inhabitant used to exercise the
-- complete analysis/EML/qutrit dependency graph.  Its carrier has one point, so
-- it is deliberately not promoted as the ordinary real or complex numbers.

terminalReal : ConstructedOrderedCompleteReal
terminalReal =
  record
    { Real = ⊤
    ; zero = tt
    ; one = tt
    ; _+_ = λ _ _ → tt
    ; _-_ = λ _ _ → tt
    ; _*_ = λ _ _ → tt
    ; neg = λ _ → tt
    ; abs = λ _ → tt
    ; _≤_ = λ _ _ → ⊤
    ; _<_ = λ _ _ → ⊤
    ; addAssoc = λ _ _ _ → refl
    ; addComm = λ _ _ → refl
    ; addZeroLeft = λ _ → refl
    ; addZeroRight = λ _ → refl
    ; mulAssoc = λ _ _ _ → refl
    ; mulComm = λ _ _ → refl
    ; mulOneLeft = λ _ → refl
    ; mulOneRight = λ _ → refl
    ; distribLeft = λ _ _ _ → refl
    ; distribRight = λ _ _ _ → refl
    ; subSelf = λ _ → refl
    ; Sequence = Nat → ⊤
    ; sequenceAt = λ s n → s n
    ; IsCauchy = λ _ → ⊤
    ; ConvergesTo = λ _ _ → ⊤
    ; cauchyLimit = λ _ _ → tt , tt
    }

terminalSeries : ConstructedSeries terminalReal
terminalSeries =
  record
    { term = λ _ → tt
    ; partialSums = λ _ → tt
    ; partialSumsMatch = λ _ → refl
    ; cauchy = tt
    ; sum = tt
    ; sumsTo = tt
    }

terminalExponential : ConstructedRealExponential terminalReal
terminalExponential =
  record
    { factorial = λ _ → tt
    ; power = λ _ _ → tt
    ; exponentialSeries = λ _ → terminalSeries
    ; exp = λ _ → tt
    ; expIsSeriesSum = λ _ → refl
    ; expZero = refl
    ; expAdd = λ _ _ → refl
    ; Positive = λ _ → ⊤
    ; onePositive = tt
    ; expPositive = λ _ → tt
    ; expInjective = λ { {tt} {tt} _ → refl }
    ; expStrictMonotone = λ _ → tt
    ; expOntoPositive = λ _ _ → tt , refl
    }

terminalLogarithm :
  ConstructedRealLogarithm terminalReal terminalExponential
terminalLogarithm =
  record
    { log = λ _ _ → tt
    ; expLog = λ _ _ → refl
    ; logExp = λ _ → refl
    ; logOne = refl
    ; positiveMul = λ _ _ → tt
    ; logMul = λ _ _ _ _ → refl
    }

terminalRealTranscendentalPackage : ConstructedRealTranscendentalPackage
terminalRealTranscendentalPackage =
  record
    { real = terminalReal
    ; exponential = terminalExponential
    ; logarithm = terminalLogarithm
    }

terminalComplexAlgebraLaws : ComplexAlgebraLaws terminalReal
terminalComplexAlgebraLaws =
  record
    { negInvolutive = λ _ → refl
    ; negZero = refl
    ; subZeroRight = λ _ → refl
    ; zeroSub = λ _ → refl
    }

terminalComplexExponential :
  ConstructedComplexExponential terminalReal terminalExponential
terminalComplexExponential =
  record
    { sin = λ _ → tt
    ; cos = λ _ → tt
    ; pi = tt
    ; expC = λ _ → complex tt tt
    ; expCartesian = λ _ _ → refl
    }

terminalComplexPackage : ConstructedComplexPackage
terminalComplexPackage =
  record
    { realPackage = terminalRealTranscendentalPackage
    ; algebraLaws = terminalComplexAlgebraLaws
    ; complexExponential = terminalComplexExponential
    }

terminalPrincipalLog : PrincipalComplexLogBranch terminalComplexPackage
terminalPrincipalLog =
  record
    { Domain = λ _ → ⊤
    ; PrincipalStrip = λ _ → ⊤
    ; NotOnNonPositiveRealAxis = λ _ → ⊤
    ; domainImpliesCutAvoidance = λ _ → tt
    ; argument = λ _ _ → tt
    ; principalArgumentLower = λ _ _ → tt
    ; principalArgumentUpper = λ _ _ → tt
    ; logC = λ _ _ → complex tt tt
    ; expLog = λ { (complex tt tt) _ → refl }
    ; expInDomain = λ _ _ → tt
    ; logExp = λ { (complex tt tt) _ → refl }
    ; principalSqrt = λ _ _ → complex tt tt
    ; sqrtSquare = λ { (complex tt tt) _ → refl }
    ; minusOne = complex tt tt
    ; minusOneInDomain = tt
    ; sqrtMinusOneIsPositiveI = refl
    ; logMinusOneIsIPi = refl
    }

terminalPrincipalComplexAnalyticPackage : PrincipalComplexAnalyticPackage
terminalPrincipalComplexAnalyticPackage =
  record
    { complexPackage = terminalComplexPackage
    ; principalLog = terminalPrincipalLog
    }
