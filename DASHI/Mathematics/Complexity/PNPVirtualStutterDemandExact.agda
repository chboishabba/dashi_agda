module DASHI.Mathematics.Complexity.PNPVirtualStutterDemandExact where

-- Quantify precisely what a shortcut must save on the original virtual
-- run. A zero-cost edge must leave the actual target configuration equal.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as N
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
import DASHI.Mathematics.Complexity.PNotEqualsNPVirtualQuotationFrontierExact as V
import DASHI.Mathematics.Complexity.GuardedCookFormulaDescriptionExact as Description
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.StandardMachineSimulationExact as Tools
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.PNPVirtualPaidEdgeBudgetNoGoExact as Paid
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Fixed
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary

module Count {SourceState SourceSymbol : Set}
    {sourceMachine : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {description : Description.GuardedCookFormulaDescription} {targetPresentation : Presented.FinitePresentedStandardTM}
    (generator : V.UniversalGuardedCookBitGenerator targetPresentation) where

  Sim : ∀ {n x y} → Run.StandardExactRun sourceMachine n x y →
    Standard.StandardConfiguration (Presented.finitePresentedStandardMachine targetPresentation) →
    Standard.StandardConfiguration (Presented.finitePresentedStandardMachine targetPresentation) → Set₂
  Sim = V.VirtualRunSimulation description generator

  zeros : ∀ {n x y a b} {run : Run.StandardExactRun sourceMachine n x y} →
    Sim run a b → Nat
  zeros V.virtualRunDone = zero
  zeros (V.virtualRunStep e rest) with V.virtualStepTotal e
  ... | zero = suc (zeros rest)
  ... | suc k = zeros rest

  positive : ∀ {n x y a b} {run : Run.StandardExactRun sourceMachine n x y} →
    Sim run a b → Nat
  positive V.virtualRunDone = zero
  positive (V.virtualRunStep e rest) with V.virtualStepTotal e
  ... | zero = positive rest
  ... | suc k = suc (positive rest)

  partition : ∀ {n x y a b} {run : Run.StandardExactRun sourceMachine n x y}
    (s : Sim run a b) → zeros s + positive s ≡ n
  partition V.virtualRunDone = refl
  partition (V.virtualRunStep e rest) with V.virtualStepTotal e
  ... | zero = cong suc (partition rest)
  ... | suc k rewrite N.+-suc (zeros rest) (positive rest) =
    cong suc (partition rest)

  positiveBelowCost : ∀ {n x y a b} {run : Run.StandardExactRun sourceMachine n x y}
    (s : Sim run a b) → positive s ≤ V.virtualRunTargetSteps s
  positiveBelowCost V.virtualRunDone = z≤n
  positiveBelowCost (V.virtualRunStep e rest) with V.virtualStepTotal e
  ... | zero = positiveBelowCost rest
  ... | suc k = N.+-mono-≤ (s≤s z≤n) (positiveBelowCost rest)

  sourceBelowZeroPlusCost : ∀ {n x y a b} {run : Run.StandardExactRun sourceMachine n x y}
    (s : Sim run a b) → n ≤ zeros s + V.virtualRunTargetSteps s
  sourceBelowZeroPlusCost s =
    subst (λ k → k ≤ zeros s + V.virtualRunTargetSteps s) (partition s)
      (N.+-mono-≤ N.≤-refl (positiveBelowCost s))

  -- Zero target execution cannot change the complete target configuration.
  zeroRunSame : ∀ {a b} →
    Run.StandardExactRun (Presented.finitePresentedStandardMachine targetPresentation)
      zero a b → a ≡ b
  zeroRunSame Run.standardRunDone = refl

  zeroStepSame : ∀ {x y a b}
    (e : V.VirtualStepSimulation {sourceMachine = sourceMachine}
      description generator x y a b) →
    V.virtualStepTotal e ≡ zero → a ≡ b
  zeroStepSame e h = zeroRunSame (Tools.transportRunSteps h (V.virtualStepRun e))

  zeroStepKeySame : ∀ {K : Set} {x y a b}
    (key : Standard.StandardConfiguration
      (Presented.finitePresentedStandardMachine targetPresentation) → K)
    (e : V.VirtualStepSimulation {sourceMachine = sourceMachine}
      description generator x y a b) →
    V.virtualStepTotal e ≡ zero → key a ≡ key b
  zeroStepKeySame key e h = cong key (zeroStepSame e h)

-- If an original length-padded candidate is simulated by edge receipts
-- within its own horizon, at least the excess must be zero-charge source
-- edges. This is a necessary condition, not an inhabited shortcut.
module Padded {cost : PR.PolynomialCostModel Cook.BooleanFormula}
  {candidate : Direct.PolynomialSATDeciderCandidate cost}
  {code : Actual.CandidateCodeRealization candidate}
  (fixed : Fixed.FixedStandardOppositeMachine code)
  {SourceState SourceSymbol : Set}
  {sourceMachine : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
  {description : Description.GuardedCookFormulaDescription} {targetPresentation : Presented.FinitePresentedStandardTM}
  (generator : V.UniversalGuardedCookBitGenerator targetPresentation) where

  module C = Count {sourceMachine = sourceMachine} {description} generator

  requiredZeroMass : ∀ {n x y a b} {run : Run.StandardExactRun sourceMachine n x y}
    (s : C.Sim run a b) →
    Binary.formulaBitCodeLength (Fixed.fixedCookFormula fixed) ≤ n →
    V.virtualRunTargetSteps s ≤ Fixed.steps fixed →
    2 * Fixed.steps fixed ≤ C.zeros s + Fixed.steps fixed
  requiredZeroMass s padded fits =
    N.≤-trans (Paid.ownCookDoubleBudgetBelowBits fixed)
      (N.≤-trans padded
        (N.≤-trans (C.sourceBelowZeroPlusCost s)
          (N.+-mono-≤ N.≤-refl fits)))

-- A source quotient may justify a genuine zero edge only after proving
-- source-to-target representation and future consumer congruence; simply
-- counting a compact bit seek or an arithmetic block as one edge cannot.
