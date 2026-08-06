module DASHI.Physics.Foundations.FiniteHistoryOrientationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- A finite history-first carrier.  The internal conjugation and reversal of
-- the order of a history are deliberately distinct operations.

data MicroState : Set where
  stateMinus : MicroState
  stateZero : MicroState
  statePlus : MicroState

internalConjugation : MicroState → MicroState
internalConjugation stateMinus = statePlus
internalConjugation stateZero = stateZero
internalConjugation statePlus = stateMinus

internalConjugationInvolutive :
  (s : MicroState) →
  internalConjugation (internalConjugation s) ≡ s
internalConjugationInvolutive stateMinus = refl
internalConjugationInvolutive stateZero = refl
internalConjugationInvolutive statePlus = refl

History2 : Set
History2 = MicroState × MicroState

reverseHistory : History2 → History2
reverseHistory (s0 , s1) =
  internalConjugation s1 , internalConjugation s0

reverseHistoryInvolutive :
  (h : History2) → reverseHistory (reverseHistory h) ≡ h
reverseHistoryInvolutive (stateMinus , stateMinus) = refl
reverseHistoryInvolutive (stateMinus , stateZero) = refl
reverseHistoryInvolutive (stateMinus , statePlus) = refl
reverseHistoryInvolutive (stateZero , stateMinus) = refl
reverseHistoryInvolutive (stateZero , stateZero) = refl
reverseHistoryInvolutive (stateZero , statePlus) = refl
reverseHistoryInvolutive (statePlus , stateMinus) = refl
reverseHistoryInvolutive (statePlus , stateZero) = refl
reverseHistoryInvolutive (statePlus , statePlus) = refl

------------------------------------------------------------------------
-- A transition-dependent action.  It is symmetric under full history
-- reversal; this is not obtained by merely negating one state coordinate.

transitionCost : MicroState → MicroState → Nat
transitionCost stateMinus stateMinus = 0
transitionCost stateMinus stateZero = 1
transitionCost stateMinus statePlus = 2
transitionCost stateZero stateMinus = 1
transitionCost stateZero stateZero = 0
transitionCost stateZero statePlus = 1
transitionCost statePlus stateMinus = 2
transitionCost statePlus stateZero = 1
transitionCost statePlus statePlus = 0

historyAction : History2 → Nat
historyAction (s0 , s1) = transitionCost s0 s1

actionTimeReversalInvariant :
  (h : History2) → historyAction (reverseHistory h) ≡ historyAction h
actionTimeReversalInvariant (stateMinus , stateMinus) = refl
actionTimeReversalInvariant (stateMinus , stateZero) = refl
actionTimeReversalInvariant (stateMinus , statePlus) = refl
actionTimeReversalInvariant (stateZero , stateMinus) = refl
actionTimeReversalInvariant (stateZero , stateZero) = refl
actionTimeReversalInvariant (stateZero , statePlus) = refl
actionTimeReversalInvariant (statePlus , stateMinus) = refl
actionTimeReversalInvariant (statePlus , stateZero) = refl
actionTimeReversalInvariant (statePlus , statePlus) = refl

------------------------------------------------------------------------
-- Filtering uses past-accessible data only.  Smoothing may additionally use a
-- declared future boundary.  The latter can change the hidden microhistory
-- without changing the recorded past observable.

data PastRecord : Set where
  recordQuiet : PastRecord
  recordActive : PastRecord

data FutureBoundary : Set where
  futureMinus : FutureBoundary
  futurePlus : FutureBoundary

filteredEstimate : PastRecord → MicroState
filteredEstimate recordQuiet = stateZero
filteredEstimate recordActive = statePlus

smoothedEstimate : PastRecord → FutureBoundary → MicroState
smoothedEstimate recordQuiet futureMinus = stateMinus
smoothedEstimate recordQuiet futurePlus = statePlus
smoothedEstimate recordActive futureMinus = stateZero
smoothedEstimate recordActive futurePlus = statePlus

data LaterChoice : Set where
  chooseMinusBoundary : LaterChoice
  choosePlusBoundary : LaterChoice

pastAccessibleOutcome : LaterChoice → PastRecord
pastAccessibleOutcome chooseMinusBoundary = recordQuiet
pastAccessibleOutcome choosePlusBoundary = recordQuiet

finiteNoBackwardSignalling :
  pastAccessibleOutcome chooseMinusBoundary
  ≡
  pastAccessibleOutcome choosePlusBoundary
finiteNoBackwardSignalling = refl

hiddenHistory : LaterChoice → History2
hiddenHistory chooseMinusBoundary = stateZero , stateMinus
hiddenHistory choosePlusBoundary = stateZero , statePlus

futureBoundaryCanChangeHiddenHistory :
  hiddenHistory chooseMinusBoundary ≡ hiddenHistory choosePlusBoundary → ⊥
futureBoundaryCanChangeHiddenHistory ()

record FiniteHistoryOrientationBoundary : Set where
  constructor finiteHistoryOrientationBoundary
  field
    historyIndexIsAutomaticallyPhysicalTime : Bool
    historyIndexIsAutomaticallyPhysicalTimeIsFalse :
      historyIndexIsAutomaticallyPhysicalTime ≡ false

    internalConjugationIsAutomaticallyTimeReversal : Bool
    internalConjugationIsAutomaticallyTimeReversalIsFalse :
      internalConjugationIsAutomaticallyTimeReversal ≡ false

    futureBoundaryDependenceImpliesOperationalBackwardsSignal : Bool
    futureBoundaryDependenceImpliesOperationalBackwardsSignalIsFalse :
      futureBoundaryDependenceImpliesOperationalBackwardsSignal ≡ false

    finiteActionSymmetryProvesContinuumMicrocausality : Bool
    finiteActionSymmetryProvesContinuumMicrocausalityIsFalse :
      finiteActionSymmetryProvesContinuumMicrocausality ≡ false

open FiniteHistoryOrientationBoundary public

canonicalFiniteHistoryOrientationBoundary :
  FiniteHistoryOrientationBoundary
canonicalFiniteHistoryOrientationBoundary =
  finiteHistoryOrientationBoundary
    false refl
    false refl
    false refl
    false refl
