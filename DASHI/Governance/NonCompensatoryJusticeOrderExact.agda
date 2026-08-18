module DASHI.Governance.NonCompensatoryJusticeOrderExact where

------------------------------------------------------------------------
-- NON-COMPENSATORY JUSTICE ORDER
--
-- Justice is not collapsed to one scalar balance.  A repair on one invariant
-- does not erase a violation on another invariant unless the application
-- supplies an explicit compensation relation permitting that substitution.
--
-- This cross-pollinates the repository's coordinatewise contestability/access
-- discipline: aggregate surplus does not repair a failed protected coordinate.
-- The mathematical compensation relation below is a DASHI construction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.SituatedInverseJusticeFibreExact as Justice
import DASHI.Governance.TransitionResidual as Transition

------------------------------------------------------------------------
-- Compensation is typed and directional.  The default exact policy permits a
-- repair to compensate only the same invariant; applications may define a
-- different policy, but must carry that authority explicitly.
------------------------------------------------------------------------

record CompensationPolicy : Set₁ where
  constructor compensationPolicy
  field
    Compensates :
      Transition.ConstitutionalInvariant →
      Transition.ConstitutionalInvariant →
      Set

open CompensationPolicy public

data SameInvariantCompensates :
  Transition.ConstitutionalInvariant →
  Transition.ConstitutionalInvariant →
  Set where
  sameInvariantCompensates :
    ∀ {invariant} → SameInvariantCompensates invariant invariant

sameInvariantCompensationPolicy : CompensationPolicy
sameInvariantCompensationPolicy = compensationPolicy SameInvariantCompensates

record NonCompensatoryJusticeNegative
    {beforeBase afterBase : Justice.SituatedJusticeBase}
    {before : Justice.JusticeFibre beforeBase}
    {after : Justice.JusticeFibre afterBase}
    (transition : Justice.JusticeTransition before after)
    (policy : CompensationPolicy) : Set₁ where
  constructor nonCompensatoryJusticeNegative
  field
    violatedInvariant : Transition.ConstitutionalInvariant
    createsViolation :
      Justice.CreatedPositiveViolation transition violatedInvariant
    noPermittedCompensatingRepair :
      (repairInvariant : Transition.ConstitutionalInvariant) →
      Justice.RepairedPositiveViolation transition repairInvariant →
      Compensates policy repairInvariant violatedInvariant →
      ⊥

open NonCompensatoryJusticeNegative public

------------------------------------------------------------------------
-- Exact countermodel: rights become positively violated while justice/review
-- is repaired.  The repair is real, but it is not a rights repair and therefore
-- cannot erase the newly created rights violation under same-coordinate policy.
------------------------------------------------------------------------

mixedBeforeValidation :
  Transition.ConstitutionalInvariant → Transition.GovernanceValidation
mixedBeforeValidation Transition.rightsInvariant = Transition.satisfied
mixedBeforeValidation Transition.justiceAndReviewInvariant =
  Transition.positivelyViolated
mixedBeforeValidation invariant = Transition.satisfied

mixedAfterValidation :
  Transition.ConstitutionalInvariant → Transition.GovernanceValidation
mixedAfterValidation Transition.rightsInvariant = Transition.positivelyViolated
mixedAfterValidation Transition.justiceAndReviewInvariant = Transition.satisfied
mixedAfterValidation invariant = Transition.satisfied

mixedBeforeFibre : Justice.JusticeFibre Justice.exampleBase
mixedBeforeFibre = Justice.justiceFibre Justice.allApplicable mixedBeforeValidation

mixedAfterFibre : Justice.JusticeFibre Justice.exampleBase
mixedAfterFibre = Justice.justiceFibre Justice.allApplicable mixedAfterValidation

mixedAction : Justice.JusticeTransition mixedBeforeFibre mixedAfterFibre
mixedAction =
  Justice.justiceTransition
    "rights violation with independent justice/review repair"

mixedRightsViolationCreated :
  Justice.CreatedPositiveViolation mixedAction Transition.rightsInvariant
mixedRightsViolationCreated =
  Justice.createdPositiveViolation tt tt refl refl

mixedReviewRepair :
  Justice.RepairedPositiveViolation
    mixedAction Transition.justiceAndReviewInvariant
mixedReviewRepair =
  Justice.repairedPositiveViolation tt tt refl refl

noSameInvariantRepairCanCompensateMixedRightsViolation :
  (repairInvariant : Transition.ConstitutionalInvariant) →
  Justice.RepairedPositiveViolation mixedAction repairInvariant →
  SameInvariantCompensates repairInvariant Transition.rightsInvariant →
  ⊥
noSameInvariantRepairCanCompensateMixedRightsViolation
  .Transition.rightsInvariant repair sameInvariantCompensates with
  Justice.RepairedPositiveViolation.wasPositivelyViolated repair
... | ()

mixedActionIsNonCompensatoryInverseJustice :
  NonCompensatoryJusticeNegative mixedAction sameInvariantCompensationPolicy
mixedActionIsNonCompensatoryInverseJustice =
  nonCompensatoryJusticeNegative
    Transition.rightsInvariant
    mixedRightsViolationCreated
    noSameInvariantRepairCanCompensateMixedRightsViolation

record UnrelatedRepairCannotCancelProtectedViolationWitness : Set₁ where
  constructor unrelatedRepairCannotCancelProtectedViolationWitness
  field
    unrelatedRepairExists :
      Justice.RepairedPositiveViolation
        mixedAction Transition.justiceAndReviewInvariant
    protectedViolationPersistsUnderTypedCompensation :
      NonCompensatoryJusticeNegative
        mixedAction sameInvariantCompensationPolicy

open UnrelatedRepairCannotCancelProtectedViolationWitness public

unrelatedJusticeRepairCannotCancelProtectedViolation :
  UnrelatedRepairCannotCancelProtectedViolationWitness
unrelatedJusticeRepairCannotCancelProtectedViolation =
  unrelatedRepairCannotCancelProtectedViolationWitness
    mixedReviewRepair
    mixedActionIsNonCompensatoryInverseJustice

------------------------------------------------------------------------
-- Relationship to the original strict operator.
-- The old operator remains a sufficient special case: if there are no repairs
-- at all, then there are certainly no permitted compensating repairs.
------------------------------------------------------------------------

strictInverseJusticeImpliesNonCompensatoryInverseJustice :
  ∀ {beforeBase afterBase}
    {before : Justice.JusticeFibre beforeBase}
    {after : Justice.JusticeFibre afterBase}
    {transition : Justice.JusticeTransition before after} →
  Justice.InverseJusticeOperator transition →
  NonCompensatoryJusticeNegative transition sameInvariantCompensationPolicy
strictInverseJusticeImpliesNonCompensatoryInverseJustice strict =
  nonCompensatoryJusticeNegative
    (Justice.violatedInvariant strict)
    (Justice.createsViolation strict)
    λ candidate repair compensation →
      Justice.noOffsettingRepair strict candidate repair

record NonCompensatoryJusticeBoundary : Set where
  constructor nonCompensatoryJusticeBoundary
  field
    anyRepairAutomaticallyCancelsAnyViolation : Bool
    crossInvariantCompensationRequiresWitness : Bool
    sameInvariantRepairMayCountAsCompensation : Bool
    scalarNetBenefitDeterminesJusticeSign : Bool

canonicalNonCompensatoryJusticeBoundary : NonCompensatoryJusticeBoundary
canonicalNonCompensatoryJusticeBoundary =
  nonCompensatoryJusticeBoundary false true true false
