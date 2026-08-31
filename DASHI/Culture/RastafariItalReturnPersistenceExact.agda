module DASHI.Culture.RastafariItalReturnPersistenceExact where

open import DASHI.Core.Prelude

import DASHI.Core.TrajectoryResidueExact as Trajectory
import DASHI.Culture.RastafariItalReturnFlowCircularityExact as Return

------------------------------------------------------------------------
-- ITAL RETURN-FLOW TEMPORAL PERSISTENCE
--
-- One successful return/reuse event is not a theorem of durable circularity.
-- This owner reuses the generic trajectory-residue core to distinguish an
-- isolated cycle from a practice whose history leaves a retained residue that
-- remains available to later situated states.
------------------------------------------------------------------------

data PracticeState : Set where
  beforeReturn
  oneCycleCompleted
  repeatedCyclePractice
  interruptedPractice
  : PracticeState

data PracticeStep : PracticeState → PracticeState → Set where
  firstCycle : PracticeStep beforeReturn oneCycleCompleted
  repeatCycle : PracticeStep oneCycleCompleted repeatedCyclePractice
  continueCycle : PracticeStep repeatedCyclePractice repeatedCyclePractice
  interruptAfterFirst : PracticeStep oneCycleCompleted interruptedPractice

data PersistenceClass : Set where
  oneOffReturn
  repeatedReturn
  historyRetainingPractice
  resilientPracticeClaim
  regenerativePersistenceClaim
  : PersistenceClass

practiceResidue : PracticeState → Trajectory.ResidueFlag
practiceResidue beforeReturn = Trajectory.residueAbsent
practiceResidue oneCycleCompleted = Trajectory.residuePresent
practiceResidue repeatedCyclePractice = Trajectory.residuePresent
practiceResidue interruptedPractice = Trajectory.residuePresent

returnHistoryIsNotErased : Trajectory.NoResidueErasure PracticeStep practiceResidue
returnHistoryIsNotErased firstCycle present = present
returnHistoryIsNotErased repeatCycle present = present
returnHistoryIsNotErased continueCycle present = present
returnHistoryIsNotErased interruptAfterFirst present = present

firstReturnDepositsHistory :
  Trajectory.ResidueDeposition PracticeStep practiceResidue
firstReturnDepositsHistory =
  Trajectory.residueDeposition
    beforeReturn
    oneCycleCompleted
    (Trajectory.traceStep firstCycle Trajectory.traceRefl)
    refl
    refl

completedCycleCannotReverseToHistoryFreeState :
  Trajectory.Trace PracticeStep oneCycleCompleted beforeReturn → ⊥
completedCycleCannotReverseToHistoryFreeState =
  Trajectory.presentResidueBlocksTraceToAbsent
    returnHistoryIsNotErased
    refl
    refl

------------------------------------------------------------------------
-- Stronger labels require stronger evidence.
------------------------------------------------------------------------

data OneCycleProvesPersistence : Set where

data RepeatedCycleProvesResilience : Set where

data PersistentPracticeProvesRegeneration : Set where

data RetainedHistoryIdentifiesCulturalTradition : Set where

oneCycleDoesNotProvePersistence : OneCycleProvesPersistence → ⊥
oneCycleDoesNotProvePersistence ()

repeatedCycleDoesNotProveResilience : RepeatedCycleProvesResilience → ⊥
repeatedCycleDoesNotProveResilience ()

persistentPracticeDoesNotProveRegeneration :
  PersistentPracticeProvesRegeneration → ⊥
persistentPracticeDoesNotProveRegeneration ()

retainedHistoryDoesNotIdentifyCulturalTradition :
  RetainedHistoryIdentifiesCulturalTradition → ⊥
retainedHistoryDoesNotIdentifyCulturalTradition ()

------------------------------------------------------------------------
-- Preserve the circularity-class distinction from the merged Ital owner.
------------------------------------------------------------------------

closedCycleStillDoesNotProveRegeneration :
  Return.measuredClosedCycle ≡ Return.regenerativeClaim → ⊥
closedCycleStillDoesNotProveRegeneration =
  Return.measuredClosedCycleIsNotRegenerativeClaim

record ItalReturnPersistenceBoundary : Set where
  constructor italReturnPersistenceBoundary
  field
    oneCycleMeansPersistentPractice : Bool
    oneCycleMeansPersistentPracticeIsFalse :
      oneCycleMeansPersistentPractice ≡ false

    repeatedCycleMeansResilience : Bool
    repeatedCycleMeansResilienceIsFalse :
      repeatedCycleMeansResilience ≡ false

    persistenceMeansRegeneration : Bool
    persistenceMeansRegenerationIsFalse :
      persistenceMeansRegeneration ≡ false

    pathHistoryCanRemainRelevant : Bool
    pathHistoryCanRemainRelevantIsTrue :
      pathHistoryCanRemainRelevant ≡ true

canonicalItalReturnPersistenceBoundary : ItalReturnPersistenceBoundary
canonicalItalReturnPersistenceBoundary =
  italReturnPersistenceBoundary false refl false refl false refl true refl
