module DASHI.Cognition.ReflexivePresentationFamily where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)

import Base369 as Base
import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.FibreBraidReasoning as Reasoning
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Cognition.ResidualPhaseGeometry as Residual

------------------------------------------------------------------------
-- One hidden reflexive state, many non-equivalent presentations.
------------------------------------------------------------------------

record PresentationFamily : Set₁ where
  field
    Hidden : Set
    Chart : Set
    Surface : Chart → Set
    project :
      (chart : Chart) →
      Hidden →
      Surface chart

open PresentationFamily public

asResidualProjection :
  (P : PresentationFamily) →
  (chart : Chart P) →
  Residual.Projection (Hidden P) (Surface P chart)
asResidualProjection P chart =
  record { observe = project P chart }

FibreAtChart :
  (P : PresentationFamily) →
  (chart : Chart P) →
  Surface P chart →
  Set
FibreAtChart P chart visible =
  Residual.Fibre (asResidualProjection P chart) visible

data BinaryOrientation : Set where
  toward : BinaryOrientation
  away : BinaryOrientation

data ProcessStage : Set where
  inactiveStage : ProcessStage
  evaluatingStage : ProcessStage
  committedStage : ProcessStage

data PsychologicalChart : Set where
  binaryChart : PsychologicalChart
  balancedTernaryChart : PsychologicalChart
  unbalancedTernaryChart : PsychologicalChart
  naryChart : PsychologicalChart
  continuousChart : PsychologicalChart
  waveChart : PsychologicalChart
  fullFibreChart : PsychologicalChart

record PsychologicalHiddenState : Set where
  constructor psychologicalHiddenState
  field
    reasoningState : Reasoning.ReasoningState
    avoidedValue : Base.TriTruth
    rememberedValue : Phase.PhaseEnrichedTrit
    expectedValue : Phase.PhaseEnrichedTrit
    contextDepth : Nat
    salience : Nat
    confidence : Nat
    wavePhase : Phase.Phase3
    activeAttractorCount : Nat

open PsychologicalHiddenState public

PsychologicalSurface : PsychologicalChart → Set
PsychologicalSurface binaryChart = BinaryOrientation
PsychologicalSurface balancedTernaryChart = BT.Trit
PsychologicalSurface unbalancedTernaryChart = ProcessStage
PsychologicalSurface naryChart = Nat
PsychologicalSurface continuousChart = Nat
PsychologicalSurface waveChart = Phase.Phase3
PsychologicalSurface fullFibreChart = PsychologicalHiddenState

binaryProjection : PsychologicalHiddenState → BinaryOrientation
binaryProjection state with Reasoning.desiredValue (reasoningState state)
... | Base.tri-high = toward
... | Base.tri-mid = away
... | Base.tri-low = away

balancedProjection : PsychologicalHiddenState → BT.Trit
balancedProjection state = Phase.observeTrit (rememberedValue state)

unbalancedProjection : PsychologicalHiddenState → ProcessStage
unbalancedProjection state with contextDepth state
... | zero = inactiveStage
... | suc zero = evaluatingStage
... | suc (suc _) = committedStage

psychologicalProjection :
  (chart : PsychologicalChart) →
  PsychologicalHiddenState →
  PsychologicalSurface chart
psychologicalProjection binaryChart = binaryProjection
psychologicalProjection balancedTernaryChart = balancedProjection
psychologicalProjection unbalancedTernaryChart = unbalancedProjection
psychologicalProjection naryChart = activeAttractorCount
psychologicalProjection continuousChart = salience
psychologicalProjection waveChart = wavePhase
psychologicalProjection fullFibreChart state = state

psychologicalPresentationFamily : PresentationFamily
psychologicalPresentationFamily =
  record
    { Hidden = PsychologicalHiddenState
    ; Chart = PsychologicalChart
    ; Surface = PsychologicalSurface
    ; project = psychologicalProjection
    }

------------------------------------------------------------------------
-- Public balanced zero is a fibre, not an atomic psychology.
------------------------------------------------------------------------

data BalancedZeroClass : Set where
  noActivationZero : BalancedZeroClass
  equalAttractionRepulsionZero : BalancedZeroClass
  undecidedAppraisalZero : BalancedZeroClass
  attentionalObservationZero : BalancedZeroClass
  phaseCancellationZero : BalancedZeroClass
  feltCompelledDissociationZero : BalancedZeroClass
  incompatibleExpectationZero : BalancedZeroClass
  insufficientEvidenceZero : BalancedZeroClass
  rapidOscillationZero : BalancedZeroClass

record BalancedZeroWitness : Set where
  constructor balancedZeroWitness
  field
    hiddenState : PsychologicalHiddenState
    zeroClass : BalancedZeroClass
    projectsToZero : balancedProjection hiddenState ≡ BT.zero

open BalancedZeroWitness public

canonicalHiddenState : PsychologicalHiddenState
canonicalHiddenState =
  psychologicalHiddenState
    Reasoning.initialReasoningState
    Base.tri-low
    Phase.balancedOpposition
    Phase.positiveDominant
    2
    4
    3
    Phase.phase0
    2

canonicalBalancedZero : BalancedZeroWitness
canonicalBalancedZero =
  balancedZeroWitness
    canonicalHiddenState
    equalAttractionRepulsionZero
    refl
