module DASHI.Foundations.ElementarySingleOperatorExtendedRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.ElementaryCalculator
open import DASHI.Foundations.ElementaryCalculatorSemantics
open import DASHI.Foundations.EMLConcreteSmokeModel
open import DASHI.Foundations.ElementaryCalculatorSmokeModel
open import DASHI.Foundations.TernaryElementarySearchCertificate
open import DASHI.Foundations.DivergenceComparisonPackage
open import DASHI.Algebra.Quantum.TernaryCircuit

------------------------------------------------------------------------
-- Calculator lowering shapes.

zeroLoweringShape :
  lowerCalculator (integer (integerLiteral positiveLiteral zero))
  ≡ zeroK
zeroLoweringShape = refl

oneLoweringShape :
  lowerCalculator constantOne ≡ oneE
oneLoweringShape = refl

eLoweringShape :
  lowerCalculator constantE ≡ expE oneE
eLoweringShape = refl

iLoweringShape :
  lowerCalculator constantI ≡ sqrtK minusOneK
iLoweringShape = refl

additionLoweringShape :
  lowerCalculator
    (calcAdd (variable zero) constantOne)
  ≡ addK (varE zero) oneE
additionLoweringShape = refl

multiplicationLoweringShape :
  lowerCalculator
    (calcMultiply (variable zero) constantTwo)
  ≡ mulK (varE zero) twoK
multiplicationLoweringShape = refl

smokeCalculatorCorrect :
  ∀ ρ t →
  evalEML smokeModel ρ (compileCalculator t)
  ≡ evalCalculator smokeModel ρ t
smokeCalculatorCorrect = compileCalculator-correct smokeLaws

smokeStructuredCalculatorCorrect :
  ∀ ρ t →
  evalEML smokeModel ρ (compileCalculator t)
  ≡ evalSemanticCalculator smokeCalculatorSemantics ρ t
smokeStructuredCalculatorCorrect = smokeStructuredCompileCorrect

------------------------------------------------------------------------
-- Search and qutrit wiring.

diagonalCandidateStatusShape :
  status (diagonalUnitSearchCandidate zero)
  ≡ symbolicCandidate
diagonalCandidateStatusShape = refl

qutritCycleRegression :
  cycleQutrit (cycleQutrit (cycleQutrit qNeg)) ≡ qNeg
qutritCycleRegression = refl

qutritTritRoundtripRegression :
  tritToBasis (basisToTrit qPos) ≡ qPos
qutritTritRoundtripRegression = refl

qutritCircuitReverseRegression :
  runCircuit
    (reverseCircuit (applyThen cycleGate halt))
    (runCircuit (applyThen cycleGate halt) qNeg)
  ≡ qNeg
qutritCircuitReverseRegression =
  reverseCircuitLeft (applyThen cycleGate halt) qNeg

defaultOptimizationMetric :
  defaultDivergenceForRole optimizationLoss ≡ squaredHellinger
defaultOptimizationMetric = refl

defaultCertificateMetric :
  defaultDivergenceForRole failClosedCertificate ≡ totalVariation
defaultCertificateMetric = refl
