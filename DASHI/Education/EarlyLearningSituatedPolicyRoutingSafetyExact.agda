module DASHI.Education.EarlyLearningSituatedPolicyRoutingSafetyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.PolicyRelativeProjectionSafety as Policy
import DASHI.Core.TypedDependencyCore as Dependency

------------------------------------------------------------------------
-- UNIVERSAL ENTITLEMENT CAN BE SAFE AS A RIGHT AND TOO COARSE AS A ROUTER
--
-- This is a finite structural countermodel, not an empirical assignment of
-- real families to routes.  Two situated states share the same public
-- entitlement observation.  A policy that must choose one action from that
-- observation therefore chooses the same support action for both.  The action
-- leaves different route-fit observations afterwards.
--
-- The point is carrier sufficiency: a universal right does not contain enough
-- information to prescribe one uniform support architecture.
------------------------------------------------------------------------

data SituatedPolicyState : Set where
  contextANow contextBNow contextAAfter contextBAfter : SituatedPolicyState

data SupportAction : Set where
  uniformSupportAction : SupportAction

data SupportPrecondition : SituatedPolicyState → SupportAction → Set where
  contextAReady : SupportPrecondition contextANow uniformSupportAction
  contextBReady : SupportPrecondition contextBNow uniformSupportAction

data SupportPostcondition : SituatedPolicyState → SupportAction → SituatedPolicyState → Set where
  contextAReceivesUniform :
    SupportPostcondition contextANow uniformSupportAction contextAAfter
  contextBReceivesUniform :
    SupportPostcondition contextBNow uniformSupportAction contextBAfter

supportActionLabel : SupportAction → String
supportActionLabel uniformSupportAction =
  "one support architecture selected from the coarse entitlement surface"

supportSystem :
  Dependency.DependentActionSystem SituatedPolicyState SupportAction
supportSystem = record
  { Precondition = SupportPrecondition
  ; Postcondition = SupportPostcondition
  ; actionLabel = supportActionLabel
  }

------------------------------------------------------------------------
-- Current public observations agree.  After the same support action, the
-- declared route-fit observation differs.  Bool is only a finite theorem
-- witness and is not an empirical developmental score.
------------------------------------------------------------------------

entitlementRouteFitObservation : SituatedPolicyState → Bool
entitlementRouteFitObservation contextANow = false
entitlementRouteFitObservation contextBNow = false
entitlementRouteFitObservation contextAAfter = true
entitlementRouteFitObservation contextBAfter = false

coarseEntitlementPolicy : Policy.CoarseInterventionPolicy Bool SupportAction
coarseEntitlementPolicy =
  Policy.coarseInterventionPolicy (λ _ → uniformSupportAction)

contextAAdmissible :
  Dependency.AdmissibleAction supportSystem contextANow uniformSupportAction
contextAAdmissible = record
  { precondition = contextAReady
  ; after = contextAAfter
  ; postcondition = contextAReceivesUniform
  ; dependencyReceipt = "context A receives the coarse-policy support action"
  }

contextBAdmissible :
  Dependency.AdmissibleAction supportSystem contextBNow uniformSupportAction
contextBAdmissible = record
  { precondition = contextBReady
  ; after = contextBAfter
  ; postcondition = contextBReceivesUniform
  ; dependencyReceipt = "context B receives the same coarse-policy support action"
  }

contextAExecution :
  Reachability.Executes supportSystem
    (uniformSupportAction ∷ []) contextANow contextAAfter
contextAExecution =
  Reachability.executesCons contextAAdmissible Reachability.executesNil

contextBExecution :
  Reachability.Executes supportSystem
    (uniformSupportAction ∷ []) contextBNow contextBAfter
contextBExecution =
  Reachability.executesCons contextBAdmissible Reachability.executesNil

uniformSupportExposesSituatedDefect :
  Policy.PolicyExposedQuotientDefect
    supportSystem entitlementRouteFitObservation coarseEntitlementPolicy
uniformSupportExposesSituatedDefect = record
  { left = contextANow
  ; right = contextBNow
  ; leftAfter = contextAAfter
  ; rightAfter = contextBAfter
  ; selectedAction = uniformSupportAction
  ; sameCurrentObservation = refl
  ; leftPolicySelectsAction = refl
  ; rightPolicySelectsAction = refl
  ; leftExecution = contextAExecution
  ; rightExecution = contextBExecution
  ; selectedFutureObservationsDiffer = λ ()
  }

coarseEntitlementPolicyCannotCarrySituatedRoutingSafety :
  Policy.PolicyRelativeSafety
    supportSystem entitlementRouteFitObservation coarseEntitlementPolicy → ⊥
coarseEntitlementPolicyCannotCarrySituatedRoutingSafety safety =
  Policy.policyDefectContradictsPolicySafety
    safety uniformSupportExposesSituatedDefect

------------------------------------------------------------------------
-- This theorem does NOT invalidate the entitlement itself.  It rejects only
-- using that coarse rights surface as the complete action-routing carrier.
------------------------------------------------------------------------

data EntitlementFailureFromRoutingDefectPermission : Set where

routingDefectCannotRefuteUniversalEntitlement :
  EntitlementFailureFromRoutingDefectPermission → ⊥
routingDefectCannotRefuteUniversalEntitlement ()

record SituatedPolicyRoutingBoundary : Set where
  constructor situatedPolicyRoutingBoundary
  field
    universalEntitlementCanBeRetained : Bool
    universalEntitlementCanBeRetainedIsTrue : universalEntitlementCanBeRetained ≡ true
    entitlementAloneIsCompleteSituatedRouter : Bool
    entitlementAloneIsCompleteSituatedRouterIsFalse :
      entitlementAloneIsCompleteSituatedRouter ≡ false
    routingNeedsFinerSituatedCarrier : Bool
    routingNeedsFinerSituatedCarrierIsTrue : routingNeedsFinerSituatedCarrier ≡ true

canonicalSituatedPolicyRoutingBoundary : SituatedPolicyRoutingBoundary
canonicalSituatedPolicyRoutingBoundary =
  situatedPolicyRoutingBoundary true refl false refl true refl
