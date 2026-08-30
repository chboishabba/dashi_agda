module DASHI.Core.ContextIndexedGovernedObservationRegression where

------------------------------------------------------------------------
-- FINITE REGRESSION: SAME SURFACE, DIFFERENT REQUIRED GOVERNANCE BY CONTEXT
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.ContextIndexedGovernedObservationExact as Contextual

data DemoState : Set where
  openState restrictedState : DemoState

data DemoSurface : Set where
  samePublicValue : DemoSurface

data DemoContext : Set where
  publicReading disclosureUse authorisedAction : DemoContext

data DemoQuery : Set where
  inspectQuery useQuery actQuery : DemoQuery

data DemoAxis : Set where
  valueAxis verificationAxis provenanceAxis permissionAxis authorityAxis obligationAxis
  : DemoAxis

data DemoOutcome : Set where
  sameOutcome restrictedOutcome openOutcome : DemoOutcome

data Never : Set where

observe : DemoState → DemoSurface
observe openState = samePublicValue
observe restrictedState = samePublicValue

Outcome : DemoAxis → Set
Outcome axis = DemoOutcome

consume : (axis : DemoAxis) → DemoState → Outcome axis
consume valueAxis state = sameOutcome
consume verificationAxis state = sameOutcome
consume provenanceAxis openState = openOutcome
consume provenanceAxis restrictedState = restrictedOutcome
consume permissionAxis openState = openOutcome
consume permissionAxis restrictedState = restrictedOutcome
consume authorityAxis openState = openOutcome
consume authorityAxis restrictedState = restrictedOutcome
consume obligationAxis openState = openOutcome
consume obligationAxis restrictedState = restrictedOutcome

Active : DemoContext → DemoQuery → DemoAxis → Set
Active publicReading inspectQuery valueAxis = ⊤
Active publicReading inspectQuery verificationAxis = ⊤
Active disclosureUse useQuery valueAxis = ⊤
Active disclosureUse useQuery verificationAxis = ⊤
Active disclosureUse useQuery provenanceAxis = ⊤
Active disclosureUse useQuery permissionAxis = ⊤
Active authorisedAction actQuery valueAxis = ⊤
Active authorisedAction actQuery verificationAxis = ⊤
Active authorisedAction actQuery provenanceAxis = ⊤
Active authorisedAction actQuery permissionAxis = ⊤
Active authorisedAction actQuery authorityAxis = ⊤
Active authorisedAction actQuery obligationAxis = ⊤
Active _ _ _ = Never

demoFamily :
  Contextual.ContextIndexedGovernedFamily
    DemoState DemoContext DemoQuery DemoSurface observe
demoFamily =
  Contextual.context-indexed-governed-family DemoAxis Outcome Active consume

constantAxisSafe :
  (axis : DemoAxis) →
  ((state : DemoState) → consume axis state ≡ sameOutcome) →
  Consumer.ConsumerSufficient observe (consume axis)
constantAxisSafe axis constant left right same =
  trans (constant left) (sym (constant right))

publicReadingSafe :
  Contextual.GovernedSafeFor demoFamily publicReading inspectQuery
publicReadingSafe valueAxis tt =
  constantAxisSafe valueAxis (λ { openState → refl ; restrictedState → refl })
publicReadingSafe verificationAxis tt =
  constantAxisSafe verificationAxis (λ { openState → refl ; restrictedState → refl })
publicReadingSafe provenanceAxis ()
publicReadingSafe permissionAxis ()
publicReadingSafe authorityAxis ()
publicReadingSafe obligationAxis ()

permissionCollision :
  Consumer.ConsumerRelevantCollision observe (consume permissionAxis)
permissionCollision =
  Consumer.consumer-relevant-collision openState restrictedState refl (λ ())

disclosurePermissionDefect :
  Contextual.ActiveGovernedCollision demoFamily disclosureUse useQuery
disclosurePermissionDefect =
  Contextual.active-governed-collision permissionAxis tt permissionCollision

disclosureUseNotSafe :
  Contextual.GovernedSafeFor demoFamily disclosureUse useQuery → ⊥
disclosureUseNotSafe =
  Contextual.activeGovernedCollisionBlocksSafety disclosurePermissionDefect

authorityCollision :
  Consumer.ConsumerRelevantCollision observe (consume authorityAxis)
authorityCollision =
  Consumer.consumer-relevant-collision openState restrictedState refl (λ ())

authorisedActionDefect :
  Contextual.ActiveGovernedCollision demoFamily authorisedAction actQuery
authorisedActionDefect =
  Contextual.active-governed-collision authorityAxis tt authorityCollision

authorisedActionNotSafe :
  Contextual.GovernedSafeFor demoFamily authorisedAction actQuery → ⊥
authorisedActionNotSafe =
  Contextual.activeGovernedCollisionBlocksSafety authorisedActionDefect

publicRequirementsIncludedInDisclosure :
  Contextual.RequirementIncluded
    demoFamily publicReading inspectQuery disclosureUse useQuery
publicRequirementsIncludedInDisclosure valueAxis tt = tt
publicRequirementsIncludedInDisclosure verificationAxis tt = tt
publicRequirementsIncludedInDisclosure provenanceAxis ()
publicRequirementsIncludedInDisclosure permissionAxis ()
publicRequirementsIncludedInDisclosure authorityAxis ()
publicRequirementsIncludedInDisclosure obligationAxis ()

record ContextIndexedGovernedRegressionBoundary : Set where
  field
    sameSurfaceCanBeSafeForPublicReading : Bool
    sameSurfaceCanFailDisclosureSafety : Bool
    sameSurfaceCanFailAuthoritySensitiveAction : Bool
    inactiveGovernedAxisIsNotFailure : Bool
    requirementRankCanIncreaseWithUseContext : Bool

canonicalContextIndexedGovernedRegressionBoundary :
  ContextIndexedGovernedRegressionBoundary
canonicalContextIndexedGovernedRegressionBoundary = record
  { sameSurfaceCanBeSafeForPublicReading = true
  ; sameSurfaceCanFailDisclosureSafety = true
  ; sameSurfaceCanFailAuthoritySensitiveAction = true
  ; inactiveGovernedAxisIsNotFailure = true
  ; requirementRankCanIncreaseWithUseContext = true
  }
