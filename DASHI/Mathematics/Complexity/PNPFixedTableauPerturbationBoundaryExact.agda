module DASHI.Mathematics.Complexity.PNPFixedTableauPerturbationBoundaryExact where

-- Reuse actual standard-run uniqueness, not a new abstract transition
-- model. A changed hidden tableau window is not necessarily a legal
-- perturbation on the same original program/input/horizon.
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPCandidateActualSelfInstantiationBoundaryExact as Actual
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Code
import DASHI.Mathematics.Complexity.PNotEqualsNPFixedStandardOppositeQuotationExact as Fixed
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local

module OnFixed
    {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {code : Actual.CandidateCodeRealization candidate}
    (f : Fixed.FixedStandardOppositeMachine code) where

  machine = Presented.finitePresentedStandardMachine (Fixed.presentation f)
  start = Language.guardedStandardStart (Fixed.input f) (Fixed.steps f)

  Endpoint : Set
  Endpoint = Standard.StandardConfiguration machine

  ExactRun : Endpoint → Set
  ExactRun z = Run.StandardExactRun machine (Fixed.steps f) start z

  terminal : Endpoint → Bool
  terminal z = Local.decideEqual
    (Presented.finiteState (Fixed.presentation f))
    (Standard.state z)
    (Presented.acceptingState (Fixed.presentation f))

  sameOriginalEndpoint : ∀ {x y : Endpoint} →
    ExactRun x → ExactRun y → x ≡ y
  sameOriginalEndpoint = Code.standardExactRunUniqueFinish

  sameOriginalTerminal : ∀ {x y : Endpoint} →
    ExactRun x → ExactRun y → terminal x ≡ terminal y
  sameOriginalTerminal p q = cong terminal (sameOriginalEndpoint p q)

  noLegalOppositePerturbation : ∀ {x y : Endpoint} →
    ExactRun x → ExactRun y → (terminal x ≡ terminal y → ⊥) → ⊥
  noLegalOppositePerturbation p q different =
    different (sameOriginalTerminal p q)

-- This does not rule out two DIFFERENT valid quoted source formulas
-- with equal actual candidate transcript and opposite SAT truth.
-- That requires a genuine paired-source producer, not merely an
-- unread bit in a represented tableau or an arithmetic stutter bound.
