module DASHI.Core.SituatedActionabilityFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- SITUATED ACTIONABILITY FIBRE
--
-- Generic owner for cases where a coarse proposal/signal/forecast is observed
-- inside a richer situated fibre.  Permission/actionability may additionally
-- depend on liquidity, crowding, uncertainty, history, risk, authority or any
-- other application-specific coordinates.
------------------------------------------------------------------------

record SituatedActionabilityFibre : Set₁ where
  field
    SituatedState : Set
    Signal : Set
    Context : Set
    Actionability : Set

    signalOf : SituatedState → Signal
    contextOf : SituatedState → Context
    actionabilityOf : SituatedState → Actionability

    fibreReading : String

open SituatedActionabilityFibre public

signalFibre :
  (fibre : SituatedActionabilityFibre) →
  Signal fibre → Set
signalFibre fibre signal =
  Observer.ObservationFibre (signalOf fibre) signal

record SameSignalDifferentActionability
    (fibre : SituatedActionabilityFibre) : Set where
  field
    leftState rightState : SituatedState fibre
    sameSignal : signalOf fibre leftState ≡ signalOf fibre rightState
    actionabilityDiffers :
      actionabilityOf fibre leftState ≡ actionabilityOf fibre rightState → ⊥

open SameSignalDifferentActionability public

signalActionabilityNonFactorability :
  ∀ {fibre : SituatedActionabilityFibre} →
  SameSignalDifferentActionability fibre →
  NF.NonFactorabilityWitness
    (signalOf fibre)
    (actionabilityOf fibre)
signalActionabilityNonFactorability witness =
  NF.nonFactorabilityWitness
    (leftState witness)
    (rightState witness)
    (sameSignal witness)
    (actionabilityDiffers witness)

signalOnlyActionabilityDecoderImpossible :
  ∀ {fibre : SituatedActionabilityFibre} →
  SameSignalDifferentActionability fibre →
  NF.FactorsThrough
    (signalOf fibre)
    (actionabilityOf fibre) →
  ⊥
signalOnlyActionabilityDecoderImpossible witness =
  NF.witnessRulesOutEveryFlatFactorisation
    (signalActionabilityNonFactorability witness)

contextRefinedObserver :
  (fibre : SituatedActionabilityFibre) →
  SituatedState fibre → Signal fibre × Context fibre
contextRefinedObserver fibre =
  Observer.pairObserver (signalOf fibre) (contextOf fibre)

record ContextEssentialForActionability
    (fibre : SituatedActionabilityFibre) : Set where
  field
    contextLeft contextRight : SituatedState fibre
    contextSameSignal :
      signalOf fibre contextLeft ≡ signalOf fibre contextRight
    contextActuallyDiffers :
      contextOf fibre contextLeft ≡ contextOf fibre contextRight → ⊥
    contextActionabilityDiffers :
      actionabilityOf fibre contextLeft ≡ actionabilityOf fibre contextRight → ⊥

open ContextEssentialForActionability public

contextEssentialGivesStrictObserverRefinement :
  ∀ {fibre : SituatedActionabilityFibre} →
  ContextEssentialForActionability fibre →
  Observer.StrictRefinement
    (signalOf fibre)
    (contextRefinedObserver fibre)
contextEssentialGivesStrictObserverRefinement {fibre} witness =
  Observer.strictPairRefinement
    (signalOf fibre)
    (contextOf fibre)
    (contextLeft witness)
    (contextRight witness)
    (contextSameSignal witness)
    (contextActuallyDiffers witness)

------------------------------------------------------------------------
-- Finite regression.
------------------------------------------------------------------------

data DemoState : Set where clean crowded : DemoState
data DemoSignal : Set where favourable : DemoSignal
data DemoContext : Set where liquid thin : DemoContext
data DemoActionability : Set where available unavailable : DemoActionability

demoFibre : SituatedActionabilityFibre
demoFibre = record
  { SituatedState = DemoState
  ; Signal = DemoSignal
  ; Context = DemoContext
  ; Actionability = DemoActionability
  ; signalOf = λ _ → favourable
  ; contextOf = λ { clean → liquid ; crowded → thin }
  ; actionabilityOf = λ { clean → available ; crowded → unavailable }
  ; fibreReading = "Equal coarse signal can inhabit distinct contextual fibres with different realized actionability."
  }

demoWitness : SameSignalDifferentActionability demoFibre
demoWitness = record
  { leftState = clean
  ; rightState = crowded
  ; sameSignal = refl
  ; actionabilityDiffers = λ ()
  }

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data SignalImpliesActionabilityPermission : Set where

data SameSignalImpliesSameContextPermission : Set where

data ContextDifferenceAlwaysChangesActionabilityPermission : Set where

signalDoesNotAutoPromoteToActionability :
  SignalImpliesActionabilityPermission → ⊥
signalDoesNotAutoPromoteToActionability ()

sameSignalDoesNotAutoPromoteToSameContext :
  SameSignalImpliesSameContextPermission → ⊥
sameSignalDoesNotAutoPromoteToSameContext ()

contextDifferenceDoesNotUniversallyForceActionabilityChange :
  ContextDifferenceAlwaysChangesActionabilityPermission → ⊥
contextDifferenceDoesNotUniversallyForceActionabilityChange ()
