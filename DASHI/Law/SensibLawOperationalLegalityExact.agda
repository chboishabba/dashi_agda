module DASHI.Law.SensibLawOperationalLegalityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- OPERATIONAL LEGALITY / ENFORCEMENT SEPARATION
--
-- Formal rule state and operational constraint are distinct coordinates.
-- Non-enforcement, tolerance, regularisation or material support never by
-- themselves establish intent, agreement, formal authorisation or lawfulness.
------------------------------------------------------------------------

data EnforcementWorld : Set where
  prohibitionEffectivelyEnforced : EnforcementWorld
  prohibitionOperationallyUnenforced : EnforcementWorld

data FormalRuleSurface : Set where
  formallyProhibited : FormalRuleSurface

data PreventionQuery : Set where
  effectivePreventionQuery : PreventionQuery

data PreventionAnswer : Set where
  effectivelyPrevented : PreventionAnswer
  notEffectivelyPrevented : PreventionAnswer

formalRuleSurface : EnforcementWorld → FormalRuleSurface
formalRuleSurface world = formallyProhibited

preventionAnswer : PreventionQuery → EnforcementWorld → PreventionAnswer
preventionAnswer effectivePreventionQuery prohibitionEffectivelyEnforced = effectivelyPrevented
preventionAnswer effectivePreventionQuery prohibitionOperationallyUnenforced = notEffectivelyPrevented

preventionSemantics :
  Query.QuerySemantics EnforcementWorld PreventionQuery PreventionAnswer
preventionSemantics = Query.querySemantics preventionAnswer

EffectivePreventionQueryAdequacyDefect : Set₁
EffectivePreventionQueryAdequacyDefect =
  Query.QueryAdequacyDefect
    formalRuleSurface
    preventionSemantics
    effectivePreventionQuery

effectivePreventionQueryAdequacyDefect : EffectivePreventionQueryAdequacyDefect
effectivePreventionQueryAdequacyDefect =
  Query.queryAdequacyDefect
    prohibitionEffectivelyEnforced
    prohibitionOperationallyUnenforced
    refl
    (λ ())

EffectivePreventionQueryAdequate : Set₁
EffectivePreventionQueryAdequate =
  Query.AdequateFor
    formalRuleSurface
    preventionSemantics
    effectivePreventionQuery

effectivePreventionNotAdequate : EffectivePreventionQueryAdequate → ⊥
effectivePreventionNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation
    effectivePreventionQueryAdequacyDefect

------------------------------------------------------------------------
-- Explicit enforcement coordinates.  These are descriptive state coordinates,
-- not inferences of motive or culpability.
------------------------------------------------------------------------

data DetectionState : Set where
  detectionPresent detectionAbsent : DetectionState

data InvestigationState : Set where
  investigationPresent investigationAbsent : InvestigationState

data ProsecutionState : Set where
  prosecutionPresent prosecutionAbsent : ProsecutionState

data SanctionState : Set where
  sanctionPresent sanctionAbsent : SanctionState

data NonInterventionState : Set where
  interventionOccurred nonInterventionOccurred : NonInterventionState

data RegularisationState : Set where
  regularised notRegularised : RegularisationState

data MaterialSupportState : Set where
  materialSupportPresent materialSupportAbsent : MaterialSupportState

data OperationalConstraintState : Set where
  operationallyConstrained operationallyUnconstrained : OperationalConstraintState

record EnforcementRegime : Set where
  constructor enforcementRegime
  field
    detection : DetectionState
    investigation : InvestigationState
    prosecution : ProsecutionState
    sanction : SanctionState
    nonIntervention : NonInterventionState
    regularisation : RegularisationState
    materialSupport : MaterialSupportState
    operationalConstraint : OperationalConstraintState

open EnforcementRegime public

------------------------------------------------------------------------
-- Non-promotion boundary.
------------------------------------------------------------------------

record OperationalLegalityBoundary : Set where
  constructor operationalLegalityBoundary
  field
    formalProhibitionAutomaticallyEffectivePrevention : Bool
    nonProsecutionAutomaticallyLawful : Bool
    toleratedConductAutomaticallyFormallyAuthorised : Bool
    regularisedConductAutomaticallyJustified : Bool
    nonEnforcementAutomaticallyEstablishesIntent : Bool
    nonEnforcementAutomaticallyEstablishesAgreement : Bool
    materialSupportAutomaticallyFormalAuthorisation : Bool
    formalRuleAndOperationalConstraintAreSeparate : Bool

open OperationalLegalityBoundary public

canonicalOperationalLegalityBoundary : OperationalLegalityBoundary
canonicalOperationalLegalityBoundary =
  operationalLegalityBoundary
    false
    false
    false
    false
    false
    false
    false
    true
