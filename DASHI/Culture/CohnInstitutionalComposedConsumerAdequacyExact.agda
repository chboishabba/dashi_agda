module DASHI.Culture.CohnInstitutionalComposedConsumerAdequacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Culture.CohnInstitutionalDecisionRevisionBraidExact as Revision
import DASHI.Culture.CohnInstitutionalEpistemicConsequenceCrossPollinationExact as Consequence
import DASHI.Culture.CohnInstitutionalNormReasonablenessEvidenceCrossPollinationExact as Evidence
import DASHI.Culture.IntellectualReceptionConsumerObservationDemandPreorderExact as Demand
import DASHI.Law.SensibLawInstitutionalResponsibilityExact as Responsibility
import DASHI.Reasoning.FibreRoutingJoinedObserverAdequacyExact as Joined

------------------------------------------------------------------------
-- INSTITUTIONAL COMPOSED CONSUMER ADEQUACY
--
-- Thin application of the repository's canonical query-indexed adequacy and
-- joined-observer refinement machinery.  Local adequacy is not transitive merely
-- because institutional stages are composed.  A surface that pays its own local
-- query can still erase a coordinate required by a downstream consumer.
--
-- Structural donor only: FibreRoutingJoinedObserverAdequacyExact transfers no
-- Fly biology, empirical result, historical identity, or domain authority.
------------------------------------------------------------------------

parentJoinedObserverBoundary : Joined.JoinedObserverCrossPollinationBoundary
parentJoinedObserverBoundary = Joined.canonicalJoinedObserverCrossPollinationBoundary

parentConsumerDemandBoundary :
  Demand.IntellectualReceptionConsumerObservationDemandPreorderBoundary
parentConsumerDemandBoundary =
  Demand.canonicalIntellectualReceptionConsumerObservationDemandPreorderBoundary

parentRevisionBoundary : Revision.InstitutionalDecisionRevisionBoundary
parentRevisionBoundary = Revision.canonicalInstitutionalDecisionRevisionBoundary

data InstitutionalConsumerState : Set where
  adequateAuthorisedExtreme : InstitutionalConsumerState
  adequateAuthorisedLow : InstitutionalConsumerState
  adequateUnauthorisedExtreme : InstitutionalConsumerState
  adequateUnauthorisedLow : InstitutionalConsumerState
  inadequateAuthorisedExtreme : InstitutionalConsumerState
  inadequateAuthorisedLow : InstitutionalConsumerState
  inadequateUnauthorisedExtreme : InstitutionalConsumerState
  inadequateUnauthorisedLow : InstitutionalConsumerState

evidenceSurface : InstitutionalConsumerState → Evidence.EvidenceAdequacyCode
evidenceSurface adequateAuthorisedExtreme = Evidence.evidenceAdequateForConsumer
evidenceSurface adequateAuthorisedLow = Evidence.evidenceAdequateForConsumer
evidenceSurface adequateUnauthorisedExtreme = Evidence.evidenceAdequateForConsumer
evidenceSurface adequateUnauthorisedLow = Evidence.evidenceAdequateForConsumer
evidenceSurface inadequateAuthorisedExtreme = Evidence.evidenceInadequateForConsumer
evidenceSurface inadequateAuthorisedLow = Evidence.evidenceInadequateForConsumer
evidenceSurface inadequateUnauthorisedExtreme = Evidence.evidenceInadequateForConsumer
evidenceSurface inadequateUnauthorisedLow = Evidence.evidenceInadequateForConsumer

authoritySurface : InstitutionalConsumerState → Responsibility.AuthorityState
authoritySurface adequateAuthorisedExtreme = Responsibility.authorised
authoritySurface adequateAuthorisedLow = Responsibility.authorised
authoritySurface adequateUnauthorisedExtreme = Responsibility.unauthorised
authoritySurface adequateUnauthorisedLow = Responsibility.unauthorised
authoritySurface inadequateAuthorisedExtreme = Responsibility.authorised
authoritySurface inadequateAuthorisedLow = Responsibility.authorised
authoritySurface inadequateUnauthorisedExtreme = Responsibility.unauthorised
authoritySurface inadequateUnauthorisedLow = Responsibility.unauthorised

consequenceSurface : InstitutionalConsumerState → Consequence.ConsequenceProfile
consequenceSurface adequateAuthorisedExtreme = Consequence.extremeIrreversibleProfile
consequenceSurface adequateAuthorisedLow = Consequence.lowReversibleProfile
consequenceSurface adequateUnauthorisedExtreme = Consequence.extremeIrreversibleProfile
consequenceSurface adequateUnauthorisedLow = Consequence.lowReversibleProfile
consequenceSurface inadequateAuthorisedExtreme = Consequence.extremeIrreversibleProfile
consequenceSurface inadequateAuthorisedLow = Consequence.lowReversibleProfile
consequenceSurface inadequateUnauthorisedExtreme = Consequence.extremeIrreversibleProfile
consequenceSurface inadequateUnauthorisedLow = Consequence.lowReversibleProfile

data DecisionDisposition : Set where
  decisionPaid : DecisionDisposition
  holdForEvidence : DecisionDisposition
  holdForAuthority : DecisionDisposition
  holdForEvidenceAndAuthority : DecisionDisposition

decisionFromCoordinates :
  Evidence.EvidenceAdequacyCode → Responsibility.AuthorityState → DecisionDisposition
decisionFromCoordinates Evidence.evidenceAdequateForConsumer Responsibility.authorised = decisionPaid
decisionFromCoordinates Evidence.evidenceAdequateForConsumer Responsibility.unauthorised = holdForAuthority
decisionFromCoordinates Evidence.evidenceInadequateForConsumer Responsibility.authorised = holdForEvidence
decisionFromCoordinates Evidence.evidenceInadequateForConsumer Responsibility.unauthorised = holdForEvidenceAndAuthority

decisionDisposition : InstitutionalConsumerState → DecisionDisposition
decisionDisposition state =
  decisionFromCoordinates (evidenceSurface state) (authoritySurface state)

data InstitutionalConsumerQuery : Set where
  evidenceQuery authorityQuery decisionQuery interventionAuditQuery : InstitutionalConsumerQuery

data InstitutionalConsumerAnswer : Set where
  evidenceAnswer : Evidence.EvidenceAdequacyCode → InstitutionalConsumerAnswer
  authorityAnswer : Responsibility.AuthorityState → InstitutionalConsumerAnswer
  decisionAnswer : DecisionDisposition → InstitutionalConsumerAnswer
  interventionAuditAnswer : DecisionDisposition → Consequence.ConsequenceProfile → InstitutionalConsumerAnswer

institutionalConsumerAnswer :
  InstitutionalConsumerQuery → InstitutionalConsumerState → InstitutionalConsumerAnswer
institutionalConsumerAnswer evidenceQuery state = evidenceAnswer (evidenceSurface state)
institutionalConsumerAnswer authorityQuery state = authorityAnswer (authoritySurface state)
institutionalConsumerAnswer decisionQuery state = decisionAnswer (decisionDisposition state)
institutionalConsumerAnswer interventionAuditQuery state =
  interventionAuditAnswer (decisionDisposition state) (consequenceSurface state)

institutionalConsumerSemantics :
  Query.QuerySemantics InstitutionalConsumerState InstitutionalConsumerQuery InstitutionalConsumerAnswer
institutionalConsumerSemantics = Query.querySemantics institutionalConsumerAnswer

evidenceSurfaceAdequateForEvidenceQuery :
  Query.AdequateFor evidenceSurface institutionalConsumerSemantics evidenceQuery
evidenceSurfaceAdequateForEvidenceQuery =
  Query.factorsForQuery evidenceAnswer (λ state → refl)

authoritySurfaceAdequateForAuthorityQuery :
  Query.AdequateFor authoritySurface institutionalConsumerSemantics authorityQuery
authoritySurfaceAdequateForAuthorityQuery =
  Query.factorsForQuery authorityAnswer (λ state → refl)

evidenceDecisionDefect :
  Query.QueryAdequacyDefect evidenceSurface institutionalConsumerSemantics decisionQuery
evidenceDecisionDefect =
  Query.queryAdequacyDefect adequateAuthorisedExtreme adequateUnauthorisedExtreme refl (λ ())

evidenceSurfaceNotAdequateForDecisionQuery :
  Query.AdequateFor evidenceSurface institutionalConsumerSemantics decisionQuery → ⊥
evidenceSurfaceNotAdequateForDecisionQuery =
  Query.queryAdequacyDefectBlocksFactorisation evidenceDecisionDefect

authorityDecisionDefect :
  Query.QueryAdequacyDefect authoritySurface institutionalConsumerSemantics decisionQuery
authorityDecisionDefect =
  Query.queryAdequacyDefect adequateAuthorisedExtreme inadequateAuthorisedExtreme refl (λ ())

authoritySurfaceNotAdequateForDecisionQuery :
  Query.AdequateFor authoritySurface institutionalConsumerSemantics decisionQuery → ⊥
authoritySurfaceNotAdequateForDecisionQuery =
  Query.queryAdequacyDefectBlocksFactorisation authorityDecisionDefect

decisionObserver :
  InstitutionalConsumerState → Evidence.EvidenceAdequacyCode × Responsibility.AuthorityState
decisionObserver = Observer.pairObserver evidenceSurface authoritySurface

decisionObserverAdequateForDecisionQuery :
  Query.AdequateFor decisionObserver institutionalConsumerSemantics decisionQuery
decisionObserverAdequateForDecisionQuery =
  Query.factorsForQuery
    (λ joined → decisionAnswer (decisionFromCoordinates (proj₁ joined) (proj₂ joined)))
    (λ state → refl)

decisionObserverRefinesEvidence : Observer.Refines evidenceSurface decisionObserver
decisionObserverRefinesEvidence = Observer.pairRefinesLeft evidenceSurface authoritySurface

decisionInterventionDefect :
  Query.QueryAdequacyDefect decisionObserver institutionalConsumerSemantics interventionAuditQuery
decisionInterventionDefect =
  Query.queryAdequacyDefect adequateAuthorisedExtreme adequateAuthorisedLow refl (λ ())

decisionObserverNotAdequateForInterventionAuditQuery :
  Query.AdequateFor decisionObserver institutionalConsumerSemantics interventionAuditQuery → ⊥
decisionObserverNotAdequateForInterventionAuditQuery =
  Query.queryAdequacyDefectBlocksFactorisation decisionInterventionDefect

fullAuditObserver :
  InstitutionalConsumerState →
  (Evidence.EvidenceAdequacyCode × Responsibility.AuthorityState) × Consequence.ConsequenceProfile
fullAuditObserver = Observer.pairObserver decisionObserver consequenceSurface

fullAuditObserverAdequateForInterventionAuditQuery :
  Query.AdequateFor fullAuditObserver institutionalConsumerSemantics interventionAuditQuery
fullAuditObserverAdequateForInterventionAuditQuery =
  Query.factorsForQuery
    (λ joined → interventionAuditAnswer
      (decisionFromCoordinates (proj₁ (proj₁ joined)) (proj₂ (proj₁ joined)))
      (proj₂ joined))
    (λ state → refl)

fullAuditRefinesDecisionObserver : Observer.Refines decisionObserver fullAuditObserver
fullAuditRefinesDecisionObserver = Observer.pairRefinesLeft decisionObserver consequenceSurface

fullAuditStrictlyRefinesDecisionObserver :
  Observer.StrictRefinement decisionObserver fullAuditObserver
fullAuditStrictlyRefinesDecisionObserver =
  Observer.strictPairRefinement
    decisionObserver consequenceSurface
    adequateAuthorisedExtreme adequateAuthorisedLow refl (λ ())

separateAxisAdequacyStillDoesNotImplyJointAdequacy :
  Joined.separateAxisAdequacyAutomaticallyImpliesJointAdequacy parentJoinedObserverBoundary ≡ false
separateAxisAdequacyStillDoesNotImplyJointAdequacy = refl

consumerDemandStillDoesNotRankTruth :
  Demand.demandOrderRanksTruth parentConsumerDemandBoundary ≡ false
consumerDemandStillDoesNotRankTruth = refl

record InstitutionalComposedConsumerAdequacyBoundary : Set where
  constructor institutionalComposedConsumerAdequacyBoundary
  field
    localAdequacyAutomaticallyComposesDownstream : Bool
    localAdequacyAutomaticallyComposesDownstreamIsFalse : localAdequacyAutomaticallyComposesDownstream ≡ false
    oneAxisAdequacyImpliesJointDecisionAdequacy : Bool
    oneAxisAdequacyImpliesJointDecisionAdequacyIsFalse : oneAxisAdequacyImpliesJointDecisionAdequacy ≡ false
    decisionAdequacyImpliesInterventionAuditAdequacy : Bool
    decisionAdequacyImpliesInterventionAuditAdequacyIsFalse : decisionAdequacyImpliesInterventionAuditAdequacy ≡ false
    downstreamConsumerRequiresFreshAdequacyTest : Bool
    downstreamConsumerRequiresFreshAdequacyTestIsTrue : downstreamConsumerRequiresFreshAdequacyTest ≡ true
    joinedObserverMayRepairDeclaredConsumer : Bool
    joinedObserverMayRepairDeclaredConsumerIsTrue : joinedObserverMayRepairDeclaredConsumer ≡ true
    joinedObserverCreatesAuthority : Bool
    joinedObserverCreatesAuthorityIsFalse : joinedObserverCreatesAuthority ≡ false
    consumerDemandOrderRanksTruth : Bool
    consumerDemandOrderRanksTruthIsFalse : consumerDemandOrderRanksTruth ≡ false
    structuralDonorMeansDomainIdentity : Bool
    structuralDonorMeansDomainIdentityIsFalse : structuralDonorMeansDomainIdentity ≡ false
    fullAuditObserverIsUniversalForFutureConsumers : Bool
    fullAuditObserverIsUniversalForFutureConsumersIsFalse : fullAuditObserverIsUniversalForFutureConsumers ≡ false

open InstitutionalComposedConsumerAdequacyBoundary public

canonicalInstitutionalComposedConsumerAdequacyBoundary : InstitutionalComposedConsumerAdequacyBoundary
canonicalInstitutionalComposedConsumerAdequacyBoundary =
  institutionalComposedConsumerAdequacyBoundary
    false refl false refl false refl true refl true refl false refl false refl false refl false refl
