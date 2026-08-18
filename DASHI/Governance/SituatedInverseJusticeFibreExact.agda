module DASHI.Governance.SituatedInverseJusticeFibreExact where

------------------------------------------------------------------------
-- SITUATED JUSTICE / INVERSE-JUSTICE FIBRE
--
-- This module does not identify policing, arrest, custody, protest control,
-- military/security institutions, or any named political actor with injustice
-- by label.  It supplies a typed carrier for asking whether a situated
-- institutional transition preserves, repairs, leaves unresolved, or
-- positively violates an applicable justice invariant.
--
-- Cross-pollination / source calibration:
--
-- Hanna Fenichel Pitkin, The Concept of Representation (1967).
-- Book; no DOI assigned.  Used only through the existing DASHI authority/
-- mandate grammar: possession of force is not itself a source of legitimate
-- representative authority, while mandate is scoped, recallable and reviewable.
--
-- Kimberle Williams Crenshaw,
-- "Mapping the Margins: Intersectionality, Identity Politics, and Violence
-- against Women of Color", Stanford Law Review 43(6), 1991.
-- DOI: 10.2307/1229039.
-- Used only through the existing DASHI situated-axis and non-factorability
-- carriers; no claim is made that the finite axis bundle exhausts Crenshaw.
--
-- Washington State Access to Justice Board,
-- "Washington State Access to Justice Technology Principles",
-- Washington Law Review 79(1), 2004.  No DOI listed in the repository source
-- record.  Used only through the existing distinction between formal and
-- practically usable contestability.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as Intersectional
import DASHI.Governance.AsymmetricLegibilityContestabilityExact as Legibility
import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.ContestabilityAccessCostExact as Contestability
import DASHI.Governance.DependentAuthorityCoercionKernel as Coercion
import DASHI.Governance.MultidimensionalContestabilityAccessExact as Access
import DASHI.Governance.SituatedConstituency as Situated
import DASHI.Governance.TransitionResidual as Transition

------------------------------------------------------------------------
-- Justice is a fibre over an already-situated governance relation.
-- We deliberately reuse Transition.ConstitutionalInvariant rather than
-- replacing it with a new scalar justice score.
------------------------------------------------------------------------

record SituatedJusticeBase : Set where
  constructor situatedJusticeBase
  field
    constituency : Situated.SituatedConstituency
    institutionLabel : String
    coerciveRelation : Coercion.AuthorityRelation
    claimedAuthoritySource : Authority.AuthoritySource

open SituatedJusticeBase public

record JusticeFibre (base : SituatedJusticeBase) : Set₁ where
  constructor justiceFibre
  field
    applicable : Transition.ConstitutionalInvariant → Set
    validation : Transition.ConstitutionalInvariant → Transition.GovernanceValidation

open JusticeFibre public

record JusticeTransition
  {beforeBase afterBase : SituatedJusticeBase}
  (before : JusticeFibre beforeBase)
  (after : JusticeFibre afterBase) : Set₁ where
  constructor justiceTransition
  field
    institutionalAction : String

open JusticeTransition public

record CreatedPositiveViolation
  {beforeBase afterBase : SituatedJusticeBase}
  {before : JusticeFibre beforeBase}
  {after : JusticeFibre afterBase}
  (transition : JusticeTransition before after)
  (invariant : Transition.ConstitutionalInvariant) : Set where
  constructor createdPositiveViolation
  field
    applicableBefore : applicable before invariant
    applicableAfter : applicable after invariant
    wasSatisfied : validation before invariant ≡ Transition.satisfied
    becamePositivelyViolated :
      validation after invariant ≡ Transition.positivelyViolated

open CreatedPositiveViolation public

record RepairedPositiveViolation
  {beforeBase afterBase : SituatedJusticeBase}
  {before : JusticeFibre beforeBase}
  {after : JusticeFibre afterBase}
  (transition : JusticeTransition before after)
  (invariant : Transition.ConstitutionalInvariant) : Set where
  constructor repairedPositiveViolation
  field
    applicableBefore : applicable before invariant
    applicableAfter : applicable after invariant
    wasPositivelyViolated :
      validation before invariant ≡ Transition.positivelyViolated
    becameSatisfied : validation after invariant ≡ Transition.satisfied

record JusticeNegativeTransition
  {beforeBase afterBase : SituatedJusticeBase}
  {before : JusticeFibre beforeBase}
  {after : JusticeFibre afterBase}
  (transition : JusticeTransition before after) : Set₁ where
  constructor justiceNegativeTransition
  field
    violatedInvariant : Transition.ConstitutionalInvariant
    createsViolation : CreatedPositiveViolation transition violatedInvariant
    noOffsettingRepair :
      (invariant : Transition.ConstitutionalInvariant) →
      RepairedPositiveViolation transition invariant →
      ⊥

open JusticeNegativeTransition public

-- "Inverse justice" is operator-direction vocabulary: a witnessed transition
-- that creates an applicable positive justice violation and repairs none of the
-- invariants in this fibre.  It is not arithmetic reciprocality.
InverseJusticeOperator :
  ∀ {beforeBase afterBase}
    {before : JusticeFibre beforeBase}
    {after : JusticeFibre afterBase} →
  JusticeTransition before after → Set₁
InverseJusticeOperator = JusticeNegativeTransition

positiveJusticeViolationIsInverseJustice :
  ∀ {beforeBase afterBase}
    {before : JusticeFibre beforeBase}
    {after : JusticeFibre afterBase}
    {transition : JusticeTransition before after} →
  JusticeNegativeTransition transition →
  InverseJusticeOperator transition
positiveJusticeViolationIsInverseJustice negative = negative

------------------------------------------------------------------------
-- "Coppers != justice": force does not self-promote even to admissible public
-- authority, hence cannot establish justice merely by possession of force.
------------------------------------------------------------------------

record ForceAloneEstablishesJustice : Set where
  constructor forceAloneEstablishesJustice
  field
    forceIsAdmissibleAuthority :
      Authority.AdmissibleAuthoritySource Authority.possessionOfForce

open ForceAloneEstablishesJustice public

forceDoesNotEstablishJustice : ForceAloneEstablishesJustice → ⊥
forceDoesNotEstablishJustice claim =
  Authority.possessionOfForceRejected (forceIsAdmissibleAuthority claim)

------------------------------------------------------------------------
-- Concrete same-role countermodel.
-- The same institutional label and same coercive relation can occur in a
-- rights-preserving or rights-violating transition.  Therefore institutional
-- role alone does not determine justice sign.
------------------------------------------------------------------------

exampleRelation : Coercion.AuthorityRelation
exampleRelation =
  Coercion.authorityRelation
    Coercion.institutionalAuthorityRole
    Coercion.neutralCustodianRole
    5
    1
    4
    4
    1
    true

exampleBase : SituatedJusticeBase
exampleBase =
  situatedJusticeBase
    Situated.neighbourhoodConstituency
    "public security institution"
    exampleRelation
    Authority.constitutionalDelegation

allApplicable : Transition.ConstitutionalInvariant → Set
allApplicable invariant = ⊤

allSatisfied : Transition.ConstitutionalInvariant → Transition.GovernanceValidation
allSatisfied invariant = Transition.satisfied

rightsViolatedOnly :
  Transition.ConstitutionalInvariant → Transition.GovernanceValidation
rightsViolatedOnly Transition.rightsInvariant = Transition.positivelyViolated
rightsViolatedOnly invariant = Transition.satisfied

preservingFibre : JusticeFibre exampleBase
preservingFibre = justiceFibre allApplicable allSatisfied

violatingFibre : JusticeFibre exampleBase
violatingFibre = justiceFibre allApplicable rightsViolatedOnly

preservingAction : JusticeTransition preservingFibre preservingFibre
preservingAction = justiceTransition "same-role rights-preserving intervention"

violatingAction : JusticeTransition preservingFibre violatingFibre
violatingAction = justiceTransition "same-role rights-violating intervention"

rightsViolationCreated :
  CreatedPositiveViolation violatingAction Transition.rightsInvariant
rightsViolationCreated =
  createdPositiveViolation tt tt refl refl

noRepairFromAllSatisfied :
  (invariant : Transition.ConstitutionalInvariant) →
  RepairedPositiveViolation violatingAction invariant →
  ⊥
noRepairFromAllSatisfied invariant repair with
  RepairedPositiveViolation.wasPositivelyViolated repair
... | ()

violatingActionIsInverseJustice : InverseJusticeOperator violatingAction
violatingActionIsInverseJustice =
  justiceNegativeTransition
    Transition.rightsInvariant
    rightsViolationCreated
    noRepairFromAllSatisfied

preservingActionCannotCreatePositiveViolation :
  (invariant : Transition.ConstitutionalInvariant) →
  CreatedPositiveViolation preservingAction invariant →
  ⊥
preservingActionCannotCreatePositiveViolation invariant created with
  CreatedPositiveViolation.becamePositivelyViolated created
... | ()

institutionalRoleDoesNotDetermineJusticeSign :
  InverseJusticeOperator violatingAction
institutionalRoleDoesNotDetermineJusticeSign = violatingActionIsInverseJustice

------------------------------------------------------------------------
-- Intersectional integration.
-- The repository already proves a concrete non-factorability witness: two
-- situated states with one identical flat label have different relational
-- outcomes.  Any justice-sign consumer that first erases the relevant relation
-- inherits the same impossibility result.
------------------------------------------------------------------------

intersectionalFlatteningCannotDetermineJusticeSign :
  Intersectional.FactorsThrough
    Intersectional.flatProjection
    Intersectional.relationalOutcome →
  ⊥
intersectionalFlatteningCannotDetermineJusticeSign =
  Intersectional.flatReweightingCannotRepairMissingRelation

------------------------------------------------------------------------
-- Contestability is a downstream fibre component, not the definition of
-- justice.  These bridge theorems retain the already-proved access failures.
------------------------------------------------------------------------

formalContestabilityDoesNotEstablishAffordableJusticeAccess :
  Contestability.AffordableContestability
    Contestability.finiteCost
    Contestability.finiteBudget →
  ⊥
formalContestabilityDoesNotEstablishAffordableJusticeAccess =
  Contestability.formalAvailabilityDoesNotEstablishAffordability

aggregateResourcesDoNotEstablishJusticeAccess :
  Access.ResourceAccessWithin Access.bottleneckDemand Access.spreadBudget →
  ⊥
aggregateResourcesDoNotEstablishJusticeAccess =
  Access.aggregateSufficiencyDoesNotEstablishCoordinateAccess

asymmetricLegibilityCanBlockExactRecovery :
  Legibility.ExactInstitutionalViewDecoder Legibility.finiteLegibilityChannel →
  ⊥
asymmetricLegibilityCanBlockExactRecovery =
  Legibility.finiteExactDecoderImpossible

------------------------------------------------------------------------
-- Repeated justice-negative coercive transitions.
-- This is deliberately proof-carrying throughput: a run contains an explicit
-- inverse-justice witness for every transition.  Counting institutional acts
-- alone is never promoted to a justice conclusion.
------------------------------------------------------------------------

data InverseJusticeRun : Set₁ where
  emptyInverseJusticeRun : InverseJusticeRun
  extendInverseJusticeRun :
    ∀ {beforeBase afterBase}
      {before : JusticeFibre beforeBase}
      {after : JusticeFibre afterBase}
      {transition : JusticeTransition before after} →
    InverseJusticeOperator transition →
    InverseJusticeRun →
    InverseJusticeRun

repeatedNegativeCoerciveTransitionsProduceInverseJustice :
  InverseJusticeOperator violatingAction →
  InverseJusticeOperator violatingAction →
  InverseJusticeRun
repeatedNegativeCoerciveTransitionsProduceInverseJustice first second =
  extendInverseJusticeRun first
    (extendInverseJusticeRun second emptyInverseJusticeRun)

canonicalTwoStepInverseJusticeRun : InverseJusticeRun
canonicalTwoStepInverseJusticeRun =
  repeatedNegativeCoerciveTransitionsProduceInverseJustice
    violatingActionIsInverseJustice
    violatingActionIsInverseJustice

------------------------------------------------------------------------
-- No-promotion boundary for live political applications.
------------------------------------------------------------------------

record SituatedInverseJusticeBoundary : Set where
  constructor situatedInverseJusticeBoundary
  field
    institutionalRoleAloneDeterminesJustice : Bool
    possessionOfForceCreatesJustice : Bool
    arrestLabelAutomaticallyInverseJustice : Bool
    policeLabelAutomaticallyInverseJustice : Bool
    protestLabelAutomaticallyEstablishesRightsViolation : Bool
    flatSingleAxisLabelSufficesForSituatedJustice : Bool
    contestabilityExhaustsJustice : Bool
    negativeTransitionMayInstantiateInverseJustice : Bool
    empiricalRoleBindingRequiredForLiveCases : Bool

canonicalSituatedInverseJusticeBoundary : SituatedInverseJusticeBoundary
canonicalSituatedInverseJusticeBoundary =
  situatedInverseJusticeBoundary
    false
    false
    false
    false
    false
    false
    false
    true
    true

institutionalRoleAloneDoesNotDetermineJustice :
  SituatedInverseJusticeBoundary.institutionalRoleAloneDeterminesJustice
    canonicalSituatedInverseJusticeBoundary
  ≡ false
institutionalRoleAloneDoesNotDetermineJustice = refl

possessionOfForceDoesNotCreateJustice :
  SituatedInverseJusticeBoundary.possessionOfForceCreatesJustice
    canonicalSituatedInverseJusticeBoundary
  ≡ false
possessionOfForceDoesNotCreateJustice = refl
