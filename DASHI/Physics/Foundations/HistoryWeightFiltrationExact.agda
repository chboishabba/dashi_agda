module DASHI.Physics.Foundations.HistoryWeightFiltrationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Gibbs weights, quantum phases, and MDL priors are distinct typed structures
-- on one finite history carrier.  No equality between them is available merely
-- because each assigns a number to a history.

data FiniteHistory : Set where
  historyLeft : FiniteHistory
  historyRight : FiniteHistory

record GibbsWeight : Set where
  constructor gibbsWeight
  field
    gibbsExponent : Nat

record QuantumPhase : Set where
  constructor quantumPhase
  field
    phaseIndex : Nat

record MDLPrior : Set where
  constructor mdlPrior
  field
    codeLength : Nat

open GibbsWeight public
open QuantumPhase public
open MDLPrior public

gibbsAssignment : FiniteHistory → GibbsWeight
gibbsAssignment historyLeft = gibbsWeight 2
gibbsAssignment historyRight = gibbsWeight 4

quantumAssignment : FiniteHistory → QuantumPhase
quantumAssignment historyLeft = quantumPhase 1
quantumAssignment historyRight = quantumPhase 3

mdlAssignment : FiniteHistory → MDLPrior
mdlAssignment historyLeft = mdlPrior 5
mdlAssignment historyRight = mdlPrior 2

------------------------------------------------------------------------
-- Observer filtration: later levels reveal more events, while an early
-- observer cannot query the terminal record.

data Event : Set where
  preparationEvent : Event
  intermediateEvent : Event
  terminalEvent : Event

data FiltrationLevel : Set where
  initialFiltration : FiltrationLevel
  intermediateFiltration : FiltrationLevel
  terminalFiltration : FiltrationLevel

visibleAt : FiltrationLevel → Event → Bool
visibleAt initialFiltration preparationEvent = true
visibleAt initialFiltration intermediateEvent = false
visibleAt initialFiltration terminalEvent = false
visibleAt intermediateFiltration preparationEvent = true
visibleAt intermediateFiltration intermediateEvent = true
visibleAt intermediateFiltration terminalEvent = false
visibleAt terminalFiltration preparationEvent = true
visibleAt terminalFiltration intermediateEvent = true
visibleAt terminalFiltration terminalEvent = true

initialObserverCannotAccessTerminalEvent :
  visibleAt initialFiltration terminalEvent ≡ false
initialObserverCannotAccessTerminalEvent = refl

terminalObserverCanAccessEveryDeclaredEvent :
  visibleAt terminalFiltration preparationEvent ≡ true
  ×
  (visibleAt terminalFiltration intermediateEvent ≡ true
    × visibleAt terminalFiltration terminalEvent ≡ true)
terminalObserverCanAccessEveryDeclaredEvent = refl , (refl , refl)

------------------------------------------------------------------------
-- Filtering and smoothing are two distinct estimators on the same record.

data BoundaryCondition : Set where
  leftBoundary : BoundaryCondition
  rightBoundary : BoundaryCondition

data Estimate : Set where
  estimateMinus : Estimate
  estimateZero : Estimate
  estimatePlus : Estimate

filterEstimate : Estimate
filterEstimate = estimateZero

smoothEstimate : BoundaryCondition → Estimate
smoothEstimate leftBoundary = estimateMinus
smoothEstimate rightBoundary = estimatePlus

smoothingCanDependOnFutureBoundary :
  smoothEstimate leftBoundary ≡ smoothEstimate rightBoundary → ⊥
smoothingCanDependOnFutureBoundary ()

------------------------------------------------------------------------
-- Entropy and description length are independent functionals.  This declared
-- evolution increases both, refuting any automatic identification of entropy
-- increase with decreasing MDL.

data ArrowStage : Set where
  arrowInitial : ArrowStage
  arrowFinal : ArrowStage

entropyValue : ArrowStage → Nat
entropyValue arrowInitial = 1
entropyValue arrowFinal = 2

descriptionLengthValue : ArrowStage → Nat
descriptionLengthValue arrowInitial = 5
descriptionLengthValue arrowFinal = 7

entropyIncreasesInWitness :
  entropyValue arrowFinal ≡ entropyValue arrowInitial + 1
entropyIncreasesInWitness = refl

descriptionLengthAlsoIncreasesInWitness :
  descriptionLengthValue arrowFinal
  ≡
  descriptionLengthValue arrowInitial + 2
descriptionLengthAlsoIncreasesInWitness = refl

record HistoryWeightFiltrationBoundary : Set where
  constructor historyWeightFiltrationBoundary
  field
    euclideanWeightIsQuantumAmplitude : Bool
    euclideanWeightIsQuantumAmplitudeIsFalse :
      euclideanWeightIsQuantumAmplitude ≡ false

    quantumAmplitudeIsMDLPrior : Bool
    quantumAmplitudeIsMDLPriorIsFalse :
      quantumAmplitudeIsMDLPrior ≡ false

    futureConditionedSmoothingIsPastIntervention : Bool
    futureConditionedSmoothingIsPastInterventionIsFalse :
      futureConditionedSmoothingIsPastIntervention ≡ false

    entropyIncreaseImpliesDescriptionLengthDecrease : Bool
    entropyIncreaseImpliesDescriptionLengthDecreaseIsFalse :
      entropyIncreaseImpliesDescriptionLengthDecrease ≡ false

open HistoryWeightFiltrationBoundary public

canonicalHistoryWeightFiltrationBoundary : HistoryWeightFiltrationBoundary
canonicalHistoryWeightFiltrationBoundary =
  historyWeightFiltrationBoundary false refl false refl false refl false refl
