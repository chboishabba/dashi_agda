module DASHI.Governance.SituatedInverseJusticeFibreExact where

------------------------------------------------------------------------
-- SITUATED JUSTICE / INVERSE-JUSTICE FIBRE
--
-- This module does not identify policing, arrest, custody, protest control,
-- military/security institutions, extremist association, or any named live
-- political actor with injustice by label.  It supplies a typed carrier for
-- asking whether a situated institutional transition preserves, repairs,
-- leaves unresolved, or positively violates an applicable justice invariant.
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
import DASHI.Governance.CouncilDelegationGraph as Council
import DASHI.Governance.DependentAuthorityCoercionKernel as Coercion
import DASHI.Governance.MultidimensionalContestabilityAccessExact as Access
import DASHI.Governance.SituatedConstituency as Situated
import DASHI.Governance.TransitionResidual as Transition
import DASHI.Promotion.PoliticalRoleAssignmentBoundary as PoliticalRole

------------------------------------------------------------------------
-- Justice is a fibre over an already-situated governance relation.
-- We deliberately reuse Transition.ConstitutionalInvariant and its four-way
-- validation rather than replacing them with a fresh scalar justice score.
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

------------------------------------------------------------------------
-- A partial comparison on the four-way validation carrier.
-- Unknown and inapplicable states are not silently ranked against known
-- satisfied/violated states.  The relation records only justified "no worse"
-- moves and therefore preserves the repo's residual discipline.
------------------------------------------------------------------------

data ValidationNoWorse :
  Transition.GovernanceValidation →
  Transition.GovernanceValidation →
  Set where
  satisfiedStaysSatisfied :
    ValidationNoWorse Transition.satisfied Transition.satisfied
  violationRepaired :
    ValidationNoWorse Transition.positivelyViolated Transition.satisfied
  violationRetained :
    ValidationNoWorse Transition.positivelyViolated Transition.positivelyViolated
  incompleteResolvedSatisfied :
    ValidationNoWorse Transition.undeterminedAxisIncomplete Transition.satisfied
  incompleteRetained :
    ValidationNoWorse
      Transition.undeterminedAxisIncomplete
      Transition.undeterminedAxisIncomplete
  inapplicableRetained :
    ValidationNoWorse Transition.inapplicableToRole Transition.inapplicableToRole

record FibreNoWorse
  {beforeBase afterBase : SituatedJusticeBase}
  (before : JusticeFibre beforeBase)
  (after : JusticeFibre afterBase) : Set₁ where
  constructor fibreNoWorse
  field
    noWorseAt :
      (invariant : Transition.ConstitutionalInvariant) →
      applicable before invariant →
      applicable after invariant →
      ValidationNoWorse (validation before invariant) (validation after invariant)

------------------------------------------------------------------------
-- Exact positive-violation / repair witnesses.
------------------------------------------------------------------------

record CreatedPositiveViolation
  {beforeBase afterBase : SituatedJusticeBase}
  {before : JusticeFibre beforeBase}
  {after : JusticeFibre afterBase}
  (transition : JusticeTransition before after)
  (invariant : Transition.ConstitutionalInvariant) : Set where
  constructor createdPositiveViolation
  field
    violationApplicableBefore : applicable before invariant
    violationApplicableAfter : applicable after invariant
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
    repairApplicableBefore : applicable before invariant
    repairApplicableAfter : applicable after invariant
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
    {transition : JusticeTransition before after}
    {invariant : Transition.ConstitutionalInvariant} →
  CreatedPositiveViolation transition invariant →
  ((candidate : Transition.ConstitutionalInvariant) →
    RepairedPositiveViolation transition candidate → ⊥) →
  InverseJusticeOperator transition
positiveJusticeViolationIsInverseJustice {invariant = invariant} created noRepair =
  justiceNegativeTransition invariant created noRepair

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

securityInstitutionRemainsSubordinateToPeople :
  Council.SubordinationPath Council.securityInstitution Council.peopleInstitution
securityInstitutionRemainsSubordinateToPeople = Council.securityToPeoplePath

------------------------------------------------------------------------
-- Concrete same-role countermodel.
-- The same institutional label, same situated base, and same coercive relation
-- can occur in a rights-preserving or rights-violating transition.  Therefore
-- institutional role alone cannot determine justice sign.
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
  positiveJusticeViolationIsInverseJustice
    rightsViolationCreated
    noRepairFromAllSatisfied

preservingActionCannotCreatePositiveViolation :
  (invariant : Transition.ConstitutionalInvariant) →
  CreatedPositiveViolation preservingAction invariant →
  ⊥
preservingActionCannotCreatePositiveViolation invariant created with
  CreatedPositiveViolation.becamePositivelyViolated created
... | ()

preservingActionIsNotInverseJustice :
  InverseJusticeOperator preservingAction → ⊥
preservingActionIsNotInverseJustice negative =
  preservingActionCannotCreatePositiveViolation
    (violatedInvariant negative)
    (createsViolation negative)

record SameInstitutionOppositeJusticeWitness : Set₁ where
  constructor sameInstitutionOppositeJusticeWitness
  field
    preservingTransition : JusticeTransition preservingFibre preservingFibre
    violatingTransition : JusticeTransition preservingFibre violatingFibre
    preservingIsNotInverse : InverseJusticeOperator preservingTransition → ⊥
    violatingIsInverse : InverseJusticeOperator violatingTransition

institutionalRoleDoesNotDetermineJusticeSign :
  SameInstitutionOppositeJusticeWitness
institutionalRoleDoesNotDetermineJusticeSign =
  sameInstitutionOppositeJusticeWitness
    preservingAction
    violatingAction
    preservingActionIsNotInverseJustice
    violatingActionIsInverseJustice

------------------------------------------------------------------------
-- A situated custody/protest-style base can explicitly retain ethnicity,
-- coloniality, armed-power and institutional-access axes.  This is an abstract
-- carrier example only; it does not adjudicate any real death, arrest or group.
------------------------------------------------------------------------

situatedCustodyConstituency : Situated.SituatedConstituency
situatedCustodyConstituency =
  Situated.mkSituatedConstituency
    "situated custody constituency"
    "unspecified place"
    0
    "custodial / policing institution"
    (Situated.ethnicityAxis
      ∷ Situated.colonialityAxis
      ∷ Situated.armedPowerAxis
      ∷ Situated.institutionalAccessAxis
      ∷ [])
    "requires relational and institutional evaluation"

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
-- Live political labels remain evidence-gated.  This is the integration point
-- for claims such as extremist/far-right association: evidence may eventually
-- affect equal-citizenship/rights/authority invariants, but the label itself is
-- not minted by this justice fibre.
------------------------------------------------------------------------

livePoliticalRoleAssignmentRemainsBlocked :
  PoliticalRole.PoliticalRoleAssignmentBoundaryReceipt.politicalAdjudicationAuthority
    PoliticalRole.canonicalPoliticalRoleAssignmentBoundaryReceipt
  ≡ false
livePoliticalRoleAssignmentRemainsBlocked =
  PoliticalRole.canonicalNoPoliticalAdjudication

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
    extremistLabelAutomaticallyAssigned : Bool
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
