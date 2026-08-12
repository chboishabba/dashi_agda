module DASHI.Core.PluralConsumerProjectionSafety where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- Plural-consumer projection safety.
--
-- Dynamic safety in DASHI is consumer-relative.  This module packages a family
-- of projections over one fine state/action system and makes the universal
-- obligation explicit: safety for one consumer cannot be promoted to safety
-- for every other authorised consumer.
------------------------------------------------------------------------

record ConsumerProjectionFamily
    (State Action Consumer Observation : Set) : Set₁ where
  constructor consumerProjectionFamily
  field
    system : Dependency.DependentActionSystem State Action
    project : Consumer → State → Observation

open ConsumerProjectionFamily public

record PluralDynamicSafety
    {State Action Consumer Observation : Set}
    (family : ConsumerProjectionFamily State Action Consumer Observation) : Set₁ where
  constructor pluralDynamicSafety
  field
    safeFor :
      (consumer : Consumer) →
      Dynamic.DynamicConsumerSafety
        (system family)
        (project family consumer)

open PluralDynamicSafety public

record ConsumerSafetyAsymmetry
    {State Action Consumer Observation : Set}
    (family : ConsumerProjectionFamily State Action Consumer Observation)
    (safeConsumer unsafeConsumer : Consumer) : Set₁ where
  constructor consumerSafetyAsymmetry
  field
    safeConsumerWitness :
      Dynamic.DynamicConsumerSafety
        (system family)
        (project family safeConsumer)
    unsafeConsumerDefect :
      Dynamic.TerminalisationDefect
        (system family)
        (project family unsafeConsumer)

open ConsumerSafetyAsymmetry public

asymmetryContradictsPluralSafety :
  ∀ {State Action Consumer Observation}
    {family : ConsumerProjectionFamily State Action Consumer Observation}
    {safeConsumer unsafeConsumer : Consumer} →
  ConsumerSafetyAsymmetry family safeConsumer unsafeConsumer →
  PluralDynamicSafety family →
  ⊥
asymmetryContradictsPluralSafety asymmetry plural =
  Dynamic.terminalisationDefectContradictsSafety
    (safeFor plural _)
    (unsafeConsumerDefect asymmetry)

------------------------------------------------------------------------
-- Concrete finite countermodel.
--
-- The bounded consumer observes a constant surface and is therefore safe under
-- every admissible trace.  A future-sensitive consumer collapses two current
-- states which diverge after the same admissible action.  Hence consumer-local
-- safety cannot be promoted to plural safety.
------------------------------------------------------------------------

data DemoState : Set where
  leftNow rightNow leftAfter rightAfter : DemoState

data DemoAction : Set where
  advance : DemoAction

data DemoPrecondition : DemoState → DemoAction → Set where
  leftReady : DemoPrecondition leftNow advance
  rightReady : DemoPrecondition rightNow advance

data DemoPostcondition : DemoState → DemoAction → DemoState → Set where
  leftMoves : DemoPostcondition leftNow advance leftAfter
  rightMoves : DemoPostcondition rightNow advance rightAfter

demoActionLabel : DemoAction → String
demoActionLabel advance = "advance one shared admissible step"

demoSystem : Dependency.DependentActionSystem DemoState DemoAction
demoSystem = record
  { Precondition = DemoPrecondition
  ; Postcondition = DemoPostcondition
  ; actionLabel = demoActionLabel
  }

leftAdvance : Dependency.AdmissibleAction demoSystem leftNow advance
leftAdvance = record
  { precondition = leftReady
  ; after = leftAfter
  ; postcondition = leftMoves
  ; dependencyReceipt = "left state follows the shared advance action"
  }

rightAdvance : Dependency.AdmissibleAction demoSystem rightNow advance
rightAdvance = record
  { precondition = rightReady
  ; after = rightAfter
  ; postcondition = rightMoves
  ; dependencyReceipt = "right state follows the shared advance action"
  }

leftAdvanceExecution :
  Reachability.Executes demoSystem (advance ∷ []) leftNow leftAfter
leftAdvanceExecution =
  Reachability.executesCons leftAdvance Reachability.executesNil

rightAdvanceExecution :
  Reachability.Executes demoSystem (advance ∷ []) rightNow rightAfter
rightAdvanceExecution =
  Reachability.executesCons rightAdvance Reachability.executesNil


data DemoConsumer : Set where
  boundedConsumer futureSensitiveConsumer : DemoConsumer

demoProject : DemoConsumer → DemoState → Bool
demoProject boundedConsumer _ = false
demoProject futureSensitiveConsumer leftNow = false
demoProject futureSensitiveConsumer rightNow = false
demoProject futureSensitiveConsumer leftAfter = false
demoProject futureSensitiveConsumer rightAfter = true

canonicalDemoProjectionFamily :
  ConsumerProjectionFamily DemoState DemoAction DemoConsumer Bool
canonicalDemoProjectionFamily =
  consumerProjectionFamily demoSystem demoProject

boundedConsumerIsDynamicallySafe :
  Dynamic.DynamicConsumerSafety demoSystem (demoProject boundedConsumer)
boundedConsumerIsDynamicallySafe =
  Dynamic.dynamicConsumerSafety
    (λ sameCurrent leftExecution rightExecution → refl)

futureSensitiveConsumerHasDefect :
  Dynamic.TerminalisationDefect
    demoSystem
    (demoProject futureSensitiveConsumer)
futureSensitiveConsumerHasDefect =
  Dynamic.terminalisationDefect
    (advance ∷ [])
    leftNow
    rightNow
    leftAfter
    rightAfter
    refl
    leftAdvanceExecution
    rightAdvanceExecution
    (λ ())

canonicalConsumerSafetyAsymmetry :
  ConsumerSafetyAsymmetry
    canonicalDemoProjectionFamily
    boundedConsumer
    futureSensitiveConsumer
canonicalConsumerSafetyAsymmetry =
  consumerSafetyAsymmetry
    boundedConsumerIsDynamicallySafe
    futureSensitiveConsumerHasDefect

boundedSafetyDoesNotYieldPluralSafety :
  PluralDynamicSafety canonicalDemoProjectionFamily → ⊥
boundedSafetyDoesNotYieldPluralSafety =
  asymmetryContradictsPluralSafety canonicalConsumerSafetyAsymmetry
