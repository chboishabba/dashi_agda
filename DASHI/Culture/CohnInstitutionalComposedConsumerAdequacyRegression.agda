module DASHI.Culture.CohnInstitutionalComposedConsumerAdequacyRegression where

open import DASHI.Core.Prelude

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Culture.CohnInstitutionalComposedConsumerAdequacyExact as Composed
import DASHI.Culture.CohnInstitutionalLeastCoordinateRepairRegression

------------------------------------------------------------------------
-- Regression contract for stagewise / composed consumer adequacy.
------------------------------------------------------------------------

evidenceSurfacePaysEvidenceQuery :
  Query.AdequateFor
    Composed.evidenceSurface
    Composed.institutionalConsumerSemantics
    Composed.evidenceQuery
evidenceSurfacePaysEvidenceQuery =
  Composed.evidenceSurfaceAdequateForEvidenceQuery

authoritySurfacePaysAuthorityQuery :
  Query.AdequateFor
    Composed.authoritySurface
    Composed.institutionalConsumerSemantics
    Composed.authorityQuery
authoritySurfacePaysAuthorityQuery =
  Composed.authoritySurfaceAdequateForAuthorityQuery

evidenceAloneDoesNotPayDecisionQuery :
  Query.AdequateFor
    Composed.evidenceSurface
    Composed.institutionalConsumerSemantics
    Composed.decisionQuery → ⊥
evidenceAloneDoesNotPayDecisionQuery =
  Composed.evidenceSurfaceNotAdequateForDecisionQuery

authorityAloneDoesNotPayDecisionQuery :
  Query.AdequateFor
    Composed.authoritySurface
    Composed.institutionalConsumerSemantics
    Composed.decisionQuery → ⊥
authorityAloneDoesNotPayDecisionQuery =
  Composed.authoritySurfaceNotAdequateForDecisionQuery

decisionJoinPaysDecisionQuery :
  Query.AdequateFor
    Composed.decisionObserver
    Composed.institutionalConsumerSemantics
    Composed.decisionQuery
decisionJoinPaysDecisionQuery =
  Composed.decisionObserverAdequateForDecisionQuery

decisionJoinDoesNotPayInterventionAudit :
  Query.AdequateFor
    Composed.decisionObserver
    Composed.institutionalConsumerSemantics
    Composed.interventionAuditQuery → ⊥
decisionJoinDoesNotPayInterventionAudit =
  Composed.decisionObserverNotAdequateForInterventionAuditQuery

fullAuditPaysInterventionAudit :
  Query.AdequateFor
    Composed.fullAuditObserver
    Composed.institutionalConsumerSemantics
    Composed.interventionAuditQuery
fullAuditPaysInterventionAudit =
  Composed.fullAuditObserverAdequateForInterventionAuditQuery

fullAuditStrictlyRefinesDecisionObserver :
  Observer.StrictRefinement
    Composed.decisionObserver
    Composed.fullAuditObserver
fullAuditStrictlyRefinesDecisionObserver =
  Composed.fullAuditStrictlyRefinesDecisionObserver

localAdequacyDoesNotPromoteToJointConsumer :
  Composed.localAdequacyAutomaticallyComposesDownstream
    Composed.canonicalInstitutionalComposedConsumerAdequacyBoundary ≡ false
localAdequacyDoesNotPromoteToJointConsumer = refl

downstreamConsumerRequiresRetest :
  Composed.downstreamConsumerRequiresFreshAdequacyTest
    Composed.canonicalInstitutionalComposedConsumerAdequacyBoundary ≡ true
downstreamConsumerRequiresRetest = refl

joinedRepairDoesNotCreateAuthority :
  Composed.joinedObserverCreatesAuthority
    Composed.canonicalInstitutionalComposedConsumerAdequacyBoundary ≡ false
joinedRepairDoesNotCreateAuthority = refl
