module DASHI.Core.ContextGovernedSafetyTransportRegression where

------------------------------------------------------------------------
-- FINITE REGRESSION: A CONTEXT CHANGE MAY ACTIVATE A NEW GOVERNED AXIS.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.ContextIndexedGovernedObservationExact as Governed
import DASHI.Core.ContextGovernedSafetyTransportExact as Transport

------------------------------------------------------------------------
-- One public surface; reading requires value only, disclosure additionally
-- requires permission.  The public surface is safe for reading but not for the
-- stronger disclosure context.
------------------------------------------------------------------------

data State : Set where restrictedState openState : State
data Surface : Set where sameSurface : Surface
data Context : Set where readingContext disclosureContext : Context
data Query : Set where useQuery : Query
data Axis : Set where valueAxis permissionAxis : Axis
data ValueOutcome : Set where sameValue : ValueOutcome
data PermissionOutcome : Set where restrictedPermission openPermission : PermissionOutcome

data Never : Set where

observe : State → Surface
observe restrictedState = sameSurface
observe openState = sameSurface

Outcome : Axis → Set
Outcome valueAxis = ValueOutcome
Outcome permissionAxis = PermissionOutcome

Active : Context → Query → Axis → Set
Active readingContext useQuery valueAxis = ⊤
Active readingContext useQuery permissionAxis = Never
Active disclosureContext useQuery valueAxis = ⊤
Active disclosureContext useQuery permissionAxis = ⊤

consume : (axis : Axis) → State → Outcome axis
consume valueAxis state = sameValue
consume permissionAxis restrictedState = restrictedPermission
consume permissionAxis openState = openPermission

family : Governed.ContextIndexedGovernedFamily State Context Query Surface observe
family = Governed.context-indexed-governed-family Axis Outcome Active consume

readingSafe : Governed.GovernedSafeFor family readingContext useQuery
readingSafe valueAxis tt left right same = refl
readingSafe permissionAxis ()

permissionCollision :
  Consumer.ConsumerRelevantCollision observe (consume permissionAxis)
permissionCollision =
  Consumer.consumer-relevant-collision restrictedState openState refl (λ ())

newPermissionRequirement :
  Transport.NewlyActivatedGovernedAxis
    family readingContext useQuery disclosureContext useQuery
newPermissionRequirement =
  Transport.newly-activated-governed-axis
    permissionAxis
    (λ ())
    tt
    permissionCollision

disclosureNotSafe :
  Governed.GovernedSafeFor family disclosureContext useQuery → ⊥
disclosureNotSafe =
  Transport.newlyActivatedCollisionBlocksTargetSafety newPermissionRequirement

-- Requirement transport exists in the safe direction: every reading
-- requirement is inherited by disclosure.  Therefore safety of disclosure
-- would imply safety of reading, but not conversely.
readingRequirementsIncludedInDisclosure :
  Governed.RequirementIncluded
    family readingContext useQuery disclosureContext useQuery
readingRequirementsIncludedInDisclosure valueAxis tt = tt
readingRequirementsIncludedInDisclosure permissionAxis ()

disclosureSafetyWouldImplyReadingSafety :
  Governed.GovernedSafeFor family disclosureContext useQuery →
  Governed.GovernedSafeFor family readingContext useQuery
disclosureSafetyWouldImplyReadingSafety =
  Governed.strongerRequirementSafetyImpliesWeaker
    readingRequirementsIncludedInDisclosure

record ContextGovernedSafetyTransportRegressionBoundary : Set where
  field
    sameSurfaceCanBeSafeBeforeNewAxisActivation : Bool
    newlyActivatedPermissionCanBreakSafety : Bool
    weakerSafetyImpliesStrongerSafety : Bool
    strongerSafetyImpliesWeakerUnderRequirementInclusion : Bool

canonicalContextGovernedSafetyTransportRegressionBoundary :
  ContextGovernedSafetyTransportRegressionBoundary
canonicalContextGovernedSafetyTransportRegressionBoundary = record
  { sameSurfaceCanBeSafeBeforeNewAxisActivation = true
  ; newlyActivatedPermissionCanBreakSafety = true
  ; weakerSafetyImpliesStrongerSafety = false
  ; strongerSafetyImpliesWeakerUnderRequirementInclusion = true
  }
