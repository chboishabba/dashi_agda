module DASHI.Biology.ParentalFearDynamicQuotientBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Biology.ParentalFearSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- Source calibration:
-- Justen O'Connor and Alice Brown (2013),
-- "A qualitative study of 'fear' as a regulator of children's independent
-- physical activity in the suburbs", Health & Place 24, 157-164.
-- DOI: 10.1016/j.healthplace.2013.09.002.
--
-- Source-supported structural premise:
-- parental fear/independence judgements are repeatedly renegotiated as child
-- capability, social support, trust, communication, surveillance, and other
-- context changes. Parent action can therefore participate in the context of
-- subsequent decisions rather than merely terminate a static classification.
--
-- DASHI extension:
-- This finite transition system is synthetic. It demonstrates, using the
-- repository's existing DynamicalQuotientSafety owner, that a coarse current
-- fear label can identify two states that diverge after the same admissible
-- support step. It is not an empirical transition table claimed by the paper.
------------------------------------------------------------------------

data DynamicFearState : Set where
  capabilityContextNow : DynamicFearState
  networkContextNow : DynamicFearState
  capabilitySupportedAfter : DynamicFearState
  networkStillConstrainedAfter : DynamicFearState

data SharedSupportAction : Set where
  provideGenericSupport : SharedSupportAction

data SupportPrecondition : DynamicFearState → SharedSupportAction → Set where
  capabilitySupportReady :
    SupportPrecondition capabilityContextNow provideGenericSupport
  networkSupportReady :
    SupportPrecondition networkContextNow provideGenericSupport

data SupportPostcondition :
    DynamicFearState → SharedSupportAction → DynamicFearState → Set where
  capabilitySupportChangesState :
    SupportPostcondition
      capabilityContextNow
      provideGenericSupport
      capabilitySupportedAfter
  networkConstraintPersists :
    SupportPostcondition
      networkContextNow
      provideGenericSupport
      networkStillConstrainedAfter

supportActionLabel : SharedSupportAction → String
supportActionLabel provideGenericSupport =
  "apply one shared coarse support action"

parentalFearSupportSystem :
  Dependency.DependentActionSystem DynamicFearState SharedSupportAction
parentalFearSupportSystem = record
  { Precondition = SupportPrecondition
  ; Postcondition = SupportPostcondition
  ; actionLabel = supportActionLabel
  }

capabilitySupportAction :
  Dependency.AdmissibleAction
    parentalFearSupportSystem
    capabilityContextNow
    provideGenericSupport
capabilitySupportAction = record
  { precondition = capabilitySupportReady
  ; after = capabilitySupportedAfter
  ; postcondition = capabilitySupportChangesState
  ; dependencyReceipt =
      "synthetic DASHI transition calibrated by source-reported capability/skill mediation"
  }

networkSupportAction :
  Dependency.AdmissibleAction
    parentalFearSupportSystem
    networkContextNow
    provideGenericSupport
networkSupportAction = record
  { precondition = networkSupportReady
  ; after = networkStillConstrainedAfter
  ; postcondition = networkConstraintPersists
  ; dependencyReceipt =
      "synthetic DASHI transition calibrated by source-reported social-network mediation"
  }

capabilitySupportExecution :
  Reachability.Executes
    parentalFearSupportSystem
    (provideGenericSupport ∷ [])
    capabilityContextNow
    capabilitySupportedAfter
capabilitySupportExecution =
  Reachability.executesCons capabilitySupportAction Reachability.executesNil

networkSupportExecution :
  Reachability.Executes
    parentalFearSupportSystem
    (provideGenericSupport ∷ [])
    networkContextNow
    networkStillConstrainedAfter
networkSupportExecution =
  Reachability.executesCons networkSupportAction Reachability.executesNil

------------------------------------------------------------------------
-- Same current coarse fear, different future mobility-relevant observation.
------------------------------------------------------------------------

data DynamicFearObservation : Set where
  elevatedNow : DynamicFearObservation
  mobilityConstraintReduced : DynamicFearObservation
  mobilityConstraintPersists : DynamicFearObservation

coarseDynamicFearObserver : DynamicFearState → DynamicFearObservation
coarseDynamicFearObserver capabilityContextNow = elevatedNow
coarseDynamicFearObserver networkContextNow = elevatedNow
coarseDynamicFearObserver capabilitySupportedAfter = mobilityConstraintReduced
coarseDynamicFearObserver networkStillConstrainedAfter = mobilityConstraintPersists

sameCurrentCoarseFear :
  coarseDynamicFearObserver capabilityContextNow
  ≡ coarseDynamicFearObserver networkContextNow
sameCurrentCoarseFear = refl

futureMobilityObservationsDiffer :
  coarseDynamicFearObserver capabilitySupportedAfter
  ≡ coarseDynamicFearObserver networkStillConstrainedAfter →
  ⊥
futureMobilityObservationsDiffer ()

parentalFearCoarseDynamicDefect :
  Dynamic.TerminalisationDefect
    parentalFearSupportSystem
    coarseDynamicFearObserver
parentalFearCoarseDynamicDefect =
  Dynamic.terminalisationDefect
    (provideGenericSupport ∷ [])
    capabilityContextNow
    networkContextNow
    capabilitySupportedAfter
    networkStillConstrainedAfter
    sameCurrentCoarseFear
    capabilitySupportExecution
    networkSupportExecution
    futureMobilityObservationsDiffer

coarseFearNotDynamicallySafeForThisLanguage :
  Dynamic.DynamicConsumerSafety
    parentalFearSupportSystem
    coarseDynamicFearObserver →
  ⊥
coarseFearNotDynamicallySafeForThisLanguage safety =
  Dynamic.terminalisationDefectContradictsSafety
    safety
    parentalFearCoarseDynamicDefect

record ParentalFearDynamicQuotientBridge : Set₁ where
  constructor mkParentalFearDynamicQuotientBridge
  field
    attribution : Attribution.ParentalFearSourceAttribution
    attributionIsCanonical :
      attribution ≡ Attribution.canonicalParentalFearSourceAttribution
    typedAdmissibleTransitionSystemConstructed : Bool
    typedAdmissibleTransitionSystemConstructedIsTrue :
      typedAdmissibleTransitionSystemConstructed ≡ true
    sameCurrentFearCanHaveDifferentFutureObservation : Bool
    sameCurrentFearCanHaveDifferentFutureObservationIsTrue :
      sameCurrentFearCanHaveDifferentFutureObservation ≡ true
    terminalisationDefectConstructed : Bool
    terminalisationDefectConstructedIsTrue :
      terminalisationDefectConstructed ≡ true
    coarseDynamicSafetyBlockedForDeclaredLanguage : Bool
    coarseDynamicSafetyBlockedForDeclaredLanguageIsTrue :
      coarseDynamicSafetyBlockedForDeclaredLanguage ≡ true
    transitionTableIsSyntheticNotEmpirical : Bool
    transitionTableIsSyntheticNotEmpiricalIsTrue :
      transitionTableIsSyntheticNotEmpirical ≡ true
    dynamicSafetyIsConsumerLanguageRelative : Bool
    dynamicSafetyIsConsumerLanguageRelativeIsTrue :
      dynamicSafetyIsConsumerLanguageRelative ≡ true
    reading : String

open ParentalFearDynamicQuotientBridge public

canonicalParentalFearDynamicQuotientBridge :
  ParentalFearDynamicQuotientBridge
canonicalParentalFearDynamicQuotientBridge =
  mkParentalFearDynamicQuotientBridge
    Attribution.canonicalParentalFearSourceAttribution refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    "DASHI extension: a coarse fear quotient can be statically colliding and dynamically unsafe for a declared future mobility language. Two states with equal current fear labels execute the same admissible support action yet separate in their future mobility-relevant observation. This finite transition table is synthetic; the source motivates renegotiated feedback and heterogeneous mediation, not these exact transitions."
