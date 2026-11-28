module DASHI.Mathematics.Complexity.PNPVirtualPaidEdgeBudgetNoGoExact where

-- Reuse the literal same-machine virtual run, not an idealized interpreter.
-- This is a no-go for positive per-source-edge charging of length-padded
-- candidates on the full guarded Cook quotation, NOT a lower bound for SAT.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (_≤_; z≤n)
import Data.Nat.Properties as N
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)

import DASHI.Mathematics.Complexity.PNotEqualsNPVirtualQuotationFrontierExact as V
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinBitCodeWidthLowerExact as Width
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.PNotEqualsNPCodedLiteralSelfQuotationPositiveBudgetNoGoExact as Literal

PaidEdges :
  ∀ {SourceState SourceSymbol sourceMachine description targetPresentation generator
      sourceSteps sourceStart sourceFinish targetStart targetFinish}
    {sourceRun : Run.StandardExactRun sourceMachine sourceSteps sourceStart sourceFinish} →
  V.VirtualRunSimulation {SourceState} {SourceSymbol} {sourceMachine}
    description {targetPresentation} generator sourceRun targetStart targetFinish → Set
PaidEdges V.virtualRunDone = ⊤
PaidEdges (V.virtualRunStep edge rest) =
  (suc zero ≤ V.virtualStepTotal edge) × PaidEdges rest

paidSourceStepsBelowTarget :
  ∀ {SourceState SourceSymbol sourceMachine description targetPresentation generator
      sourceSteps sourceStart sourceFinish targetStart targetFinish}
    {sourceRun : Run.StandardExactRun sourceMachine sourceSteps sourceStart sourceFinish}
    (simulation : V.VirtualRunSimulation {SourceState} {SourceSymbol} {sourceMachine}
      description {targetPresentation} generator sourceRun targetStart targetFinish) →
  PaidEdges simulation → sourceSteps ≤ V.virtualRunTargetSteps simulation
paidSourceStepsBelowTarget V.virtualRunDone paid = z≤n
paidSourceStepsBelowTarget (V.virtualRunStep edge rest) (positive , paid) =
  N.+-mono-≤ positive (paidSourceStepsBelowTarget rest paid)

ownCookDoubleBudgetBelowBits :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate}
    (fixed : Fixed.FixedStandardOppositeMachine code) →
  2 * Fixed.steps fixed ≤ Binary.formulaBitCodeLength (Fixed.fixedCookFormula fixed)
ownCookDoubleBudgetBelowBits fixed =
  N.≤-trans
    (N.m≤n+m (2 * Fixed.steps fixed) (Input.initialInputCellCount (Fixed.input fixed)))
    (Width.guardedColsBelowCookFormulaBitCode
      (Fixed.stateCoverage fixed) (Fixed.symbolCoverage fixed)
      (Fixed.nonemptyRules fixed) (Fixed.input fixed) (Fixed.steps fixed))

-- If the candidate actually uses at least the bit-code length steps on
-- its own quotation, and the target pays at least that many steps, even
-- zero setup/query/suffix overhead cannot fit a positive budget.
lengthPaidClockForcesZero :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate}
    (fixed : Fixed.FixedStandardOppositeMachine code)
    (sourceSteps targetSteps : Nat) →
  Binary.formulaBitCodeLength (Fixed.fixedCookFormula fixed) ≤ sourceSteps →
  sourceSteps ≤ targetSteps →
  targetSteps ≤ Fixed.steps fixed →
  Fixed.steps fixed ≡ zero
lengthPaidClockForcesZero fixed sourceSteps targetSteps codePaid sourcePaid fits =
  Literal.doubleLeSelfForcesZero (Fixed.steps fixed)
    (N.≤-trans (ownCookDoubleBudgetBelowBits fixed)
      (N.≤-trans codePaid (N.≤-trans sourcePaid fits)))
