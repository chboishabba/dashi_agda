module DASHI.Governance.OperationalLegibilityJusticeSafetyExact where

------------------------------------------------------------------------
-- OPERATIONAL LEGIBILITY -> CLASSIFICATION -> INTERVENTION SAFETY
--
-- InstitutionalTechniqueTransferCore already owns the domain-neutral loop
--   traces -> entity resolution -> relations -> classification -> intervention.
-- PolicyRelativeProjectionSafety already owns the theorem that a coarse policy
-- is unsafe when equal current observations receive the same selected action
-- and diverge after that action.  This module welds the two exact carriers.
--
-- No claim of technique transfer, vendor conduct, policing practice or live
-- institutional wrongdoing is manufactured here.  Those remain evidence-gated
-- by the imported technique-transfer boundary.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.PolicyRelativeProjectionSafety as Policy
import DASHI.Governance.InstitutionalTechniqueTransferCore as Technique

resolveDemoEntity : List Policy.DemoState → Policy.DemoState
resolveDemoEntity [] = Policy.leftNow
resolveDemoEntity (state ∷ rest) = state

canonicalOperationalLegibilitySystem : Technique.OperationalLegibilitySystem
canonicalOperationalLegibilitySystem = record
  { Trace = Policy.DemoState
  ; Entity = Policy.DemoState
  ; Relation = ⊤
  ; Classification = Bool
  ; Intervention = Policy.DemoAction
  ; resolveEntity = resolveDemoEntity
  ; inferRelations = λ entity traces → []
  ; classify = λ entity relations → Policy.demoProject entity
  ; intervene = λ entity classification → Policy.reveal
  }

canonicalClosedOperationalLoop :
  Technique.ClosedOperationalLoop canonicalOperationalLegibilitySystem
canonicalClosedOperationalLoop = record
  { traces = Policy.leftNow ∷ []
  ; entity = Policy.leftNow
  ; relations = []
  ; classification = false
  ; intervention = Policy.reveal
  ; entityResolved = refl
  ; relationsInferred = refl
  ; classificationProduced = refl
  ; interventionProduced = refl
  }

revealPolicy : Policy.CoarseInterventionPolicy Bool Policy.DemoAction
revealPolicy = Policy.coarseInterventionPolicy (λ observation → Policy.reveal)

revealPolicyDefect :
  Policy.PolicyExposedQuotientDefect
    Policy.demoSystem
    Policy.demoProject
    revealPolicy
revealPolicyDefect =
  Policy.policyExposedQuotientDefect
    Policy.leftNow
    Policy.rightNow
    Policy.leftRevealed
    Policy.rightRevealed
    Policy.reveal
    refl
    refl
    refl
    (Reachability.executesCons
      Policy.leftRevealAdmissible
      Reachability.executesNil)
    (Reachability.executesCons
      Policy.rightRevealAdmissible
      Reachability.executesNil)
    (λ ())

record OperationalLegibilityJusticeDefect : Set₁ where
  constructor operationalLegibilityJusticeDefect
  field
    operationalLoop :
      Technique.ClosedOperationalLoop canonicalOperationalLegibilitySystem
    policyDefect :
      Policy.PolicyExposedQuotientDefect
        Policy.demoSystem
        Policy.demoProject
        revealPolicy

open OperationalLegibilityJusticeDefect public

canonicalOperationalLegibilityJusticeDefect :
  OperationalLegibilityJusticeDefect
canonicalOperationalLegibilityJusticeDefect =
  operationalLegibilityJusticeDefect
    canonicalClosedOperationalLoop
    revealPolicyDefect

unsafeLegibilityProjectionBlocksSafeOperationalInterventionLoop :
  Policy.PolicyRelativeSafety
    Policy.demoSystem
    Policy.demoProject
    revealPolicy →
  ⊥
unsafeLegibilityProjectionBlocksSafeOperationalInterventionLoop safety =
  Policy.policyDefectContradictsPolicySafety safety revealPolicyDefect

record OperationalLegibilityJusticeBoundary : Set where
  constructor operationalLegibilityJusticeBoundary
  field
    operationalClassificationEqualsPerson : Bool
    classificationAloneEstablishesSafeIntervention : Bool
    policySelectedActionStillRequiresDynamicSafety : Bool
    analogousTechniqueProvesTechniqueTransfer : Bool
    liveInstitutionalApplicationRequiresEvidence : Bool

canonicalOperationalLegibilityJusticeBoundary :
  OperationalLegibilityJusticeBoundary
canonicalOperationalLegibilityJusticeBoundary =
  operationalLegibilityJusticeBoundary false false true false true
