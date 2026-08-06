module DASHI.Physics.Foundations.FiniteHistoryFunctionalExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Histories are primitive admissible objects.  They need not arise from one
-- deterministic update function.

data Configuration : Set where
  configurationA : Configuration
  configurationB : Configuration
  configurationC : Configuration

History3 : Set
History3 = Configuration × (Configuration × Configuration)

historyABC : History3
historyABC = configurationA , (configurationB , configurationC)

historyACB : History3
historyACB = configurationA , (configurationC , configurationB)

data Admissibility : Set where
  admissibleHistory : Admissibility
  forbiddenHistory : Admissibility

classifyHistory : History3 → Admissibility
classifyHistory (configurationA , (configurationB , configurationC)) =
  admissibleHistory
classifyHistory (configurationA , (configurationC , configurationB)) =
  admissibleHistory
classifyHistory (configurationA , (configurationA , configurationA)) =
  admissibleHistory
classifyHistory history = forbiddenHistory

nondeterministicHistoriesShareInitialState :
  classifyHistory historyABC ≡ admissibleHistory
  ×
  classifyHistory historyACB ≡ admissibleHistory
nondeterministicHistoriesShareInitialState = refl , refl

------------------------------------------------------------------------
-- One reversible deterministic subsystem is represented separately.

reversibleStep : Configuration → Configuration
reversibleStep configurationA = configurationB
reversibleStep configurationB = configurationA
reversibleStep configurationC = configurationC

reversibleStepInvolutive :
  (configuration : Configuration) →
  reversibleStep (reversibleStep configuration) ≡ configuration
reversibleStepInvolutive configurationA = refl
reversibleStepInvolutive configurationB = refl
reversibleStepInvolutive configurationC = refl

------------------------------------------------------------------------
-- Action is a functional of a complete history, not merely of its initial
-- state.  Two histories with the same initial configuration can differ.

historyAction : History3 → Nat
historyAction (configurationA , (configurationB , configurationC)) = 2
historyAction (configurationA , (configurationC , configurationB)) = 4
historyAction (configurationA , (configurationA , configurationA)) = 1
historyAction history = 6

sameInitialStateDifferentAction :
  historyAction historyABC ≡ 2
  ×
  historyAction historyACB ≡ 4
sameInitialStateDifferentAction = refl , refl

------------------------------------------------------------------------
-- Amplitude and probability are distinct carriers.  A phase label does not
-- become a probability until an additional observation rule is supplied.

data PhaseLabel : Set where
  phaseZero : PhaseLabel
  phaseQuarter : PhaseLabel
  phaseHalf : PhaseLabel
  phaseThreeQuarter : PhaseLabel

data ProbabilityWeight : Set where
  probabilityZero : ProbabilityWeight
  probabilityHalf : ProbabilityWeight
  probabilityOne : ProbabilityWeight

amplitudePhase : History3 → PhaseLabel
amplitudePhase history with historyAction history
... | 1 = phaseQuarter
... | 2 = phaseHalf
... | 4 = phaseZero
... | n = phaseThreeQuarter

observedProbability : History3 → ProbabilityWeight
observedProbability
  (configurationA , (configurationB , configurationC)) =
  probabilityHalf
observedProbability
  (configurationA , (configurationC , configurationB)) =
  probabilityHalf
observedProbability history = probabilityZero

interferingPhaseLabelsCanShareProbability :
  observedProbability historyABC ≡ observedProbability historyACB
interferingPhaseLabelsCanShareProbability = refl

------------------------------------------------------------------------
-- Discrete stationary-path witness.  The middle candidate has smaller action
-- than both declared neighbouring variations.

data PathVariation : Set where
  leftVariation : PathVariation
  stationaryVariation : PathVariation
  rightVariation : PathVariation

variationAction : PathVariation → Nat
variationAction leftVariation = 4
variationAction stationaryVariation = 2
variationAction rightVariation = 5

stationaryCandidateBeatsLeft :
  variationAction leftVariation
  ≡
  variationAction stationaryVariation + 2
stationaryCandidateBeatsLeft = refl

stationaryCandidateBeatsRight :
  variationAction rightVariation
  ≡
  variationAction stationaryVariation + 3
stationaryCandidateBeatsRight = refl

------------------------------------------------------------------------
-- Two-boundary ensemble and conditional pruning.

data InitialBoundary : Set where
  initialA : InitialBoundary

data FinalBoundary : Set where
  finalB : FinalBoundary
  finalC : FinalBoundary

data BoundaryCompatibility : Set where
  compatible : BoundaryCompatibility
  incompatible : BoundaryCompatibility

compatibleWithBoundaries :
  InitialBoundary → FinalBoundary → History3 → BoundaryCompatibility
compatibleWithBoundaries
  initialA
  finalC
  (configurationA , (configurationB , configurationC)) =
  compatible
compatibleWithBoundaries
  initialA
  finalB
  (configurationA , (configurationC , configurationB)) =
  compatible
compatibleWithBoundaries initial final history = incompatible

prunedHistory : FinalBoundary → History3
prunedHistory finalC = historyABC
prunedHistory finalB = historyACB

pruningSelectsCompatibleHistory :
  (final : FinalBoundary) →
  compatibleWithBoundaries initialA final (prunedHistory final)
  ≡
  compatible
pruningSelectsCompatibleHistory finalB = refl
pruningSelectsCompatibleHistory finalC = refl

------------------------------------------------------------------------
-- Charge conjugation and history reversal remain distinct maps.

chargeConjugation : Configuration → Configuration
chargeConjugation configurationA = configurationC
chargeConjugation configurationB = configurationB
chargeConjugation configurationC = configurationA

reverseOrder : History3 → History3
reverseOrder (first , (middle , last)) = last , (middle , first)

conjugateHistory : History3 → History3
conjugateHistory (first , (middle , last)) =
  chargeConjugation first ,
  (chargeConjugation middle , chargeConjugation last)

conjugationDiffersFromReversal :
  conjugateHistory historyACB ≡ reverseOrder historyACB → ⊥
conjugationDiffersFromReversal ()

record FiniteHistoryFunctionalBoundary : Set where
  constructor finiteHistoryFunctionalBoundary
  field
    everyAdmissibleHistoryComesFromOneDeterministicUpdate : Bool
    everyAdmissibleHistoryComesFromOneDeterministicUpdateIsFalse :
      everyAdmissibleHistoryComesFromOneDeterministicUpdate ≡ false

    phaseLabelIsAlreadyProbability : Bool
    phaseLabelIsAlreadyProbabilityIsFalse :
      phaseLabelIsAlreadyProbability ≡ false

    stationaryFiniteCandidateProvesContinuumClassicalLimit : Bool
    stationaryFiniteCandidateProvesContinuumClassicalLimitIsFalse :
      stationaryFiniteCandidateProvesContinuumClassicalLimit ≡ false

    futureBoundaryPruningIsControllableBackwardSignalling : Bool
    futureBoundaryPruningIsControllableBackwardSignallingIsFalse :
      futureBoundaryPruningIsControllableBackwardSignalling ≡ false

    chargeConjugationIsTimeReversal : Bool
    chargeConjugationIsTimeReversalIsFalse :
      chargeConjugationIsTimeReversal ≡ false

open FiniteHistoryFunctionalBoundary public

canonicalFiniteHistoryFunctionalBoundary : FiniteHistoryFunctionalBoundary
canonicalFiniteHistoryFunctionalBoundary =
  finiteHistoryFunctionalBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
