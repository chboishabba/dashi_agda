module DASHI.Physics.Closure.MonsterC3Native369ConsumerSufficiencyValidation where

open import DASHI.Core.Prelude
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Physics.Closure.MonsterC3Native369ConsumerSufficiencyExact as S

phaseIsSufficientForPhaseConsumer :
  Consumer.ConsumerSufficient S.phaseObserver S.phaseConsumer
phaseIsSufficientForPhaseConsumer = S.phaseObserverSufficientForPhase

phaseInsufficientForFineState :
  Consumer.ConsumerSufficient S.phaseObserver S.fineStateConsumer → ⊥
phaseInsufficientForFineState = S.phaseObserverNotSufficientForFineState

phaseInsufficientForWeight :
  Consumer.ConsumerSufficient S.phaseObserver S.weightConsumer → ⊥
phaseInsufficientForWeight = S.phaseObserverNotSufficientForWeight

phaseInsufficientForMultiplicity :
  Consumer.ConsumerSufficient S.phaseObserver S.multiplicityConsumer → ⊥
phaseInsufficientForMultiplicity = S.phaseObserverNotSufficientForMultiplicity

native369SufficientForFineState :
  Consumer.ConsumerSufficient S.native369Observer S.fineStateConsumer
native369SufficientForFineState = S.native369ObserverSufficientForFineState
