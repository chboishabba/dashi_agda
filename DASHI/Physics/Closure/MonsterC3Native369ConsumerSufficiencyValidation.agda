module DASHI.Physics.Closure.MonsterC3Native369ConsumerSufficiencyValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Closure.MonsterC3Native369ConsumerSufficiencyExact as S

phaseIsSufficientForPhaseConsumer :
  S.Consumer.ConsumerSufficient S.phaseObserver S.phaseConsumer
phaseIsSufficientForPhaseConsumer = S.phaseObserverSufficientForPhase

phaseInsufficientForFineState :
  S.Consumer.ConsumerSufficient S.phaseObserver S.fineStateConsumer → ⊥
phaseInsufficientForFineState = S.phaseObserverNotSufficientForFineState

phaseInsufficientForWeight :
  S.Consumer.ConsumerSufficient S.phaseObserver S.weightConsumer → ⊥
phaseInsufficientForWeight = S.phaseObserverNotSufficientForWeight

phaseInsufficientForMultiplicity :
  S.Consumer.ConsumerSufficient S.phaseObserver S.multiplicityConsumer → ⊥
phaseInsufficientForMultiplicity = S.phaseObserverNotSufficientForMultiplicity

native369SufficientForFineState :
  S.Consumer.ConsumerSufficient S.native369Observer S.fineStateConsumer
native369SufficientForFineState = S.native369ObserverSufficientForFineState
