module DASHI.Governance.JusticeRequiredAxisEvidenceExact where

------------------------------------------------------------------------
-- JUSTICE / ROUTING REQUIRED-AXIS EVIDENCE
--
-- The generic support-square core separates information polarity from
-- required-axis completeness.  This module specialises that distinction to
-- situated justice and authority routing without replacing either existing
-- carrier.
--
-- Source calibration:
--
-- Nuel D. Belnap, "A Useful Four-Valued Logic", in J. Michael Dunn and
-- George Epstein (eds.), Modern Uses of Multiple-Valued Logic, 1977, pp. 5-37.
-- DOI: 10.1007/978-94-010-1161-7_2.
-- Used only for the independent support / counter-support information square.
--
-- Kimberle Williams Crenshaw,
-- "Mapping the Margins: Intersectionality, Identity Politics, and Violence
-- against Women of Color", Stanford Law Review 43(6), 1991.
-- DOI: 10.2307/1229039.
-- Used through the repo's situated/non-factorability discipline: evidence on
-- one coordinate does not erase a missing relation on another coordinate.
--
-- Hanna Fenichel Pitkin, The Concept of Representation (1967).
-- Book; no DOI assigned.  Used through AuthorityMandateCore: mandate and scope
-- are proof obligations rather than intrinsic properties of an actor label.
--
-- The evidence-grid constructions and completeness theorems below are DASHI
-- constructions and do not constitute empirical findings about a live case.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.RequiredAxisSupportSquareExact as Support
import DASHI.Governance.SituatedAuthorityRoutingExact as Routing
import DASHI.Governance.SituatedInverseJusticeFibreExact as Justice
import DASHI.Governance.TransitionResidual as Transition

------------------------------------------------------------------------
-- Justice evidence: invariant x provenance layer.
-- The square orientation is exactly
--   (supportsSatisfied, supportsViolation).
------------------------------------------------------------------------

data JusticeEvidenceAxis : Set where
  subjectAccountAxis : JusticeEvidenceAxis
  institutionalRecordAxis : JusticeEvidenceAxis
  authorityMandateAxis : JusticeEvidenceAxis
  causalChronologyAxis : JusticeEvidenceAxis
  counterfactualSafetyAxis : JusticeEvidenceAxis
  independentReviewAxis : JusticeEvidenceAxis

record JusticeEvidenceCoordinate : Set where
  constructor justiceEvidenceCoordinate
  field
    invariant : Transition.ConstitutionalInvariant
    provenanceAxis : JusticeEvidenceAxis

open JusticeEvidenceCoordinate public

record JusticeEvidenceGrid : Set₁ where
  constructor justiceEvidenceGrid
  field
    evidenceAt :
      Transition.ConstitutionalInvariant →
      JusticeEvidenceAxis →
      Support.SupportSquare
    Required :
      Transition.ConstitutionalInvariant →
      JusticeEvidenceAxis →
      Set

open JusticeEvidenceGrid public

asAxisEvidenceFamily :
  JusticeEvidenceGrid →
  Support.AxisEvidenceFamily JusticeEvidenceCoordinate
asAxisEvidenceFamily grid =
  Support.axisEvidenceFamily
    (λ coordinate →
      evidenceAt grid
        (invariant coordinate)
        (provenanceAxis coordinate))
    (λ coordinate →
      Required grid
        (invariant coordinate)
        (provenanceAxis coordinate))

ResolvedSatisfaction :
  JusticeEvidenceGrid →
  Transition.ConstitutionalInvariant →
  JusticeEvidenceAxis →
  Set
ResolvedSatisfaction grid invariantValue axis =
  Support.ResolvedPositive (evidenceAt grid invariantValue axis)

ResolvedViolation :
  JusticeEvidenceGrid →
  Transition.ConstitutionalInvariant →
  JusticeEvidenceAxis →
  Set
ResolvedViolation grid invariantValue axis =
  Support.ResolvedNegative (evidenceAt grid invariantValue axis)

record EvidenceBackedCreatedViolation
    {beforeBase afterBase : Justice.SituatedJusticeBase}
    {before : Justice.JusticeFibre beforeBase}
    {after : Justice.JusticeFibre afterBase}
    (transition : Justice.JusticeTransition before after)
    (invariantValue : Transition.ConstitutionalInvariant)
    (grid : JusticeEvidenceGrid) : Set₁ where
  constructor evidenceBackedCreatedViolation
  field
    createdViolation :
      Justice.CreatedPositiveViolation transition invariantValue
    derivationAxis : JusticeEvidenceAxis
    derivationRequired : Required grid invariantValue derivationAxis
    violationResolved :
      ResolvedViolation grid invariantValue derivationAxis

open EvidenceBackedCreatedViolation public

-- Missing evidence is not itself a positive violation derivation.
missingEvidenceCannotManufactureViolationDerivation :
  ∀ {grid invariantValue axis} →
  Support.MissingEvidence (evidenceAt grid invariantValue axis) →
  ResolvedViolation grid invariantValue axis →
  ⊥
missingEvidenceCannotManufactureViolationDerivation =
  Support.missingCannotBeResolvedNegative

-- Conflicting evidence remains distinct from a resolved violation derivation.
conflictingEvidenceCannotManufactureResolvedViolation :
  ∀ {grid invariantValue axis} →
  Support.ConflictingEvidence (evidenceAt grid invariantValue axis) →
  ResolvedViolation grid invariantValue axis →
  ⊥
conflictingEvidenceCannotManufactureResolvedViolation =
  Support.conflictingCannotBeResolvedNegative

record EvidenceBackedInverseJustice
    {beforeBase afterBase : Justice.SituatedJusticeBase}
    {before : Justice.JusticeFibre beforeBase}
    {after : Justice.JusticeFibre afterBase}
    (transition : Justice.JusticeTransition before after)
    (grid : JusticeEvidenceGrid) : Set₁ where
  constructor evidenceBackedInverseJustice
  field
    inverseJustice : Justice.InverseJusticeOperator transition
    violationEvidence :
      EvidenceBackedCreatedViolation
        transition
        (Justice.violatedInvariant inverseJustice)
        grid

open EvidenceBackedInverseJustice public

------------------------------------------------------------------------
-- Two-dimensional non-compensation witness.
-- Rights-violation evidence on the subject-account axis does not fill missing
-- authority/mandate evidence, even inside the same justice invariant family.
------------------------------------------------------------------------

demoJusticeEvidence :
  Transition.ConstitutionalInvariant →
  JusticeEvidenceAxis →
  Support.SupportSquare
demoJusticeEvidence Transition.rightsInvariant subjectAccountAxis =
  Support.supportSquare false true
demoJusticeEvidence Transition.rightsInvariant authorityMandateAxis =
  Support.supportSquare false false
demoJusticeEvidence invariantValue axis = Support.supportSquare true false

demoJusticeRequired :
  Transition.ConstitutionalInvariant →
  JusticeEvidenceAxis →
  Set
demoJusticeRequired Transition.rightsInvariant subjectAccountAxis = ⊤
demoJusticeRequired Transition.rightsInvariant authorityMandateAxis = ⊤
demoJusticeRequired invariantValue axis = ⊤

demoJusticeGrid : JusticeEvidenceGrid
demoJusticeGrid = justiceEvidenceGrid demoJusticeEvidence demoJusticeRequired

demoRightsViolationEvidence :
  ResolvedViolation demoJusticeGrid Transition.rightsInvariant subjectAccountAxis
demoRightsViolationEvidence = refl , refl

demoRightsMandateEvidenceMissing :
  Support.MissingEvidence
    (evidenceAt demoJusticeGrid Transition.rightsInvariant authorityMandateAxis)
demoRightsMandateEvidenceMissing = refl , refl

rightsViolationEvidenceDoesNotFillMissingMandateEvidence :
  ResolvedSatisfaction
    demoJusticeGrid Transition.rightsInvariant authorityMandateAxis →
  ⊥
rightsViolationEvidenceDoesNotFillMissingMandateEvidence =
  Support.missingCannotBeResolvedPositive demoRightsMandateEvidenceMissing

------------------------------------------------------------------------
-- Routing evidence: all eight route obligations are independent required axes.
------------------------------------------------------------------------

data RoutingEvidenceAxis : Set where
  sufficiencyAxis competenceAxis mandateAxis currentAuthorityAxis :
    RoutingEvidenceAxis
  subjectLegibilityAxis safetyAxis reviewabilityAxis repairCapacityAxis :
    RoutingEvidenceAxis

allRoutingAxesRequired : RoutingEvidenceAxis → Set
allRoutingAxesRequired axis = ⊤

record RouteEvidenceProfile : Set₁ where
  constructor routeEvidenceProfile
  field
    routeEvidenceAt : RoutingEvidenceAxis → Support.SupportSquare

open RouteEvidenceProfile public

routeEvidenceFamily :
  RouteEvidenceProfile →
  Support.AxisEvidenceFamily RoutingEvidenceAxis
routeEvidenceFamily profile =
  Support.axisEvidenceFamily (routeEvidenceAt profile) allRoutingAxesRequired

record EvidenceBackedAdmissibleRoute
    {Situation Route : Set}
    (system : Routing.RoutingSystem Situation Route)
    (situation : Situation)
    (route : Route)
    (profile : RouteEvidenceProfile) : Set₁ where
  constructor evidenceBackedAdmissibleRoute
  field
    admissibleRoute : Routing.AdmissibleRoute system situation route
    requiredEvidenceResolved :
      Support.RequiredAxesResolved (routeEvidenceFamily profile)

open EvidenceBackedAdmissibleRoute public

formerSupporterEvidence : RoutingEvidenceAxis → Support.SupportSquare
formerSupporterEvidence currentAuthorityAxis = Support.supportSquare false false
formerSupporterEvidence axis = Support.supportSquare true false

formerSupporterEvidenceProfile : RouteEvidenceProfile
formerSupporterEvidenceProfile = routeEvidenceProfile formerSupporterEvidence

formerSupporterHasPositiveSufficiencyEvidence :
  Support.PositiveSupportSomewhere
    (routeEvidenceFamily formerSupporterEvidenceProfile)
formerSupporterHasPositiveSufficiencyEvidence =
  Support.positiveSupportSomewhere sufficiencyAxis refl

formerSupporterMissingCurrentAuthorityEvidence :
  Support.MissingRequiredAxis
    (routeEvidenceFamily formerSupporterEvidenceProfile)
formerSupporterMissingCurrentAuthorityEvidence =
  Support.missingRequiredAxis currentAuthorityAxis tt (refl , refl)

pooledRoutingEvidenceCannotManufactureCurrentAuthority :
  Support.RequiredAxesResolved
    (routeEvidenceFamily formerSupporterEvidenceProfile) →
  ⊥
pooledRoutingEvidenceCannotManufactureCurrentAuthority =
  Support.positiveSupportOnAnotherAxisCannotFillMissingRequiredAxis
    formerSupporterHasPositiveSufficiencyEvidence
    formerSupporterMissingCurrentAuthorityEvidence

formerSupporterCannotBecomeEvidenceBackedAdmissibleRoute :
  EvidenceBackedAdmissibleRoute
    Routing.protectiveRoutingSystem
    Routing.supportedDecisionSituation
    Routing.formerSupporterRoute
    formerSupporterEvidenceProfile →
  ⊥
formerSupporterCannotBecomeEvidenceBackedAdmissibleRoute backed =
  pooledRoutingEvidenceCannotManufactureCurrentAuthority
    (requiredEvidenceResolved backed)

record JusticeRequiredAxisEvidenceBoundary : Set where
  constructor justiceRequiredAxisEvidenceBoundary
  field
    missingEvidenceCountsAsViolation : Bool
    conflictingEvidenceCountsAsResolvedViolation : Bool
    evidenceOnAnotherJusticeCoordinateFillsMissingMandate : Bool
    evidenceOnAnotherRoutingAxisFillsCurrentAuthority : Bool
    routeAdmissibilityCanBeDerivedFromPooledConfidenceAlone : Bool

canonicalJusticeRequiredAxisEvidenceBoundary :
  JusticeRequiredAxisEvidenceBoundary
canonicalJusticeRequiredAxisEvidenceBoundary =
  justiceRequiredAxisEvidenceBoundary false false false false false
