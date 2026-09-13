module DASHI.Law.SensibLawParetoBoundSourceDemandExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)

import DASHI.Core.BoundAcquisitionDemandExact as Bound
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierProofPromotionExact as Proof
import DASHI.Cognition.PNF.SensibLawNegligenceDutyParetoProofPromotionExact as DutyProof
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual
import DASHI.Law.SensibLawParetoProofDirectedCorpusSearchBidiExact as Search
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Intent
import DASHI.Law.HerzogColonialWrongTypeElementRequirementExact as HerzogElement
import DASHI.Law.HerzogColonialWrongTypeParetoProofPromotionExact as HerzogProof

------------------------------------------------------------------------
-- SENSIBLAW SPECIALISATION OF THE GENERIC BOUND-ACQUISITION CARRIER.
------------------------------------------------------------------------

record LegalSourceAcquisition
    {Requirement : Set}
    {portfolio : List (Pareto.RequirementCandidate Requirement)}
    {selected : Pareto.RequirementCandidate Requirement}
    (promotion : Proof.FrontierPromotion portfolio selected) : Set where
  constructor legal-source-acquisition
  field
    directive : Search.CertifiedSearchDirective promotion
    residual : Residual.LegalResidualKind

open LegalSourceAcquisition public

legalSearchAlignment :
  ∀ {Requirement}
    {portfolio : List (Pareto.RequirementCandidate Requirement)}
    {selected : Pareto.RequirementCandidate Requirement} →
  (promotion : Proof.FrontierPromotion portfolio selected) →
  (residualForRequirement : Requirement → Residual.LegalResidualKind) →
  (producerForRequirement : Requirement → Intent.ProducerClass) →
  Bound.AcquisitionAlignment
    Requirement Residual.LegalResidualKind Intent.ProducerClass
    (LegalSourceAcquisition promotion)
legalSearchAlignment promotion residualForRequirement producerForRequirement =
  Bound.acquisition-alignment
    residualForRequirement
    producerForRequirement
    LegalSourceAcquisition.residual
    (λ acquisition →
      Search.CertifiedSearchDirective.producerClass
        (LegalSourceAcquisition.directive acquisition))

BoundCertifiedSearchDemand :
  ∀ {Requirement}
    {portfolio : List (Pareto.RequirementCandidate Requirement)}
    {selected : Pareto.RequirementCandidate Requirement} →
  (promotion : Proof.FrontierPromotion portfolio selected) →
  (residualForRequirement : Requirement → Residual.LegalResidualKind) →
  (producerForRequirement : Requirement → Intent.ProducerClass) →
  Residual.LegalResidualKind → Set₁
BoundCertifiedSearchDemand {selected = selected}
  promotion residualForRequirement producerForRequirement liveResidual =
  Bound.BoundAcquisitionDemand
    (legalSearchAlignment promotion residualForRequirement producerForRequirement)
    (Pareto.requirement selected)
    liveResidual

sourceRoutePaysSelectedResidual :
  ∀ {Requirement}
    {portfolio : List (Pareto.RequirementCandidate Requirement)}
    {selected : Pareto.RequirementCandidate Requirement}
    {promotion : Proof.FrontierPromotion portfolio selected}
    {residualForRequirement : Requirement → Residual.LegalResidualKind}
    {producerForRequirement : Requirement → Intent.ProducerClass}
    {liveResidual : Residual.LegalResidualKind} →
  (demand : BoundCertifiedSearchDemand promotion residualForRequirement producerForRequirement liveResidual) →
  LegalSourceAcquisition.residual (Bound.acquisition demand) ≡
  residualForRequirement (Pareto.requirement selected)
sourceRoutePaysSelectedResidual = Bound.acquisitionPaysSelectedResidual

sourceRouteUsesSelectedProducer :
  ∀ {Requirement}
    {portfolio : List (Pareto.RequirementCandidate Requirement)}
    {selected : Pareto.RequirementCandidate Requirement}
    {promotion : Proof.FrontierPromotion portfolio selected}
    {residualForRequirement : Requirement → Residual.LegalResidualKind}
    {producerForRequirement : Requirement → Intent.ProducerClass}
    {liveResidual : Residual.LegalResidualKind} →
  (demand : BoundCertifiedSearchDemand promotion residualForRequirement producerForRequirement liveResidual) →
  Search.CertifiedSearchDirective.producerClass
    (LegalSourceAcquisition.directive (Bound.acquisition demand)) ≡
  producerForRequirement (Pareto.requirement selected)
sourceRouteUsesSelectedProducer = Bound.acquisitionUsesSelectedProducer

------------------------------------------------------------------------
-- Duty-of-care maps and exact bound demands.
------------------------------------------------------------------------

dutyProducer : Climate.DutyIssue → Intent.ProducerClass
dutyProducer Climate.reasonableForeseeability = Intent.occurrenceEvidenceProducer
dutyProducer Climate.knowledge = Intent.occurrenceEvidenceProducer
dutyProducer Climate.control = Intent.occurrenceEvidenceProducer
dutyProducer Climate.vulnerability = Intent.occurrenceEvidenceProducer
dutyProducer Climate.assumptionOfResponsibility = Intent.occurrenceEvidenceProducer
dutyProducer Climate.plaintiffClassDeterminacy = Intent.doctrinalComparisonProducer
dutyProducer Climate.harmTypeDeterminacy = Intent.doctrinalComparisonProducer
dutyProducer Climate.temporalScope = Intent.temporalProducer
dutyProducer Climate.causation = Intent.occurrenceEvidenceProducer
dutyProducer Climate.scopeOfDuty = Intent.doctrinalComparisonProducer
dutyProducer Climate.statutoryCoherence = Intent.exactCitedAuthorityProducer
dutyProducer Climate.coreGovernmentPolicy = Intent.authorityTreatmentProducer
dutyProducer Climate.institutionalCompetence = Intent.authorityTreatmentProducer
dutyProducer Climate.publicAuthorityFunction = Intent.authorityTreatmentProducer
dutyProducer Climate.compensability = Intent.doctrinalComparisonProducer

corePolicyBoundSourceDemand :
  BoundCertifiedSearchDemand DutyProof.corePolicyPromotion Residual.dutyResidualKind dutyProducer
    Residual.missingInstitutionalConstraint
corePolicyBoundSourceDemand = Bound.bound-acquisition-demand
  (legal-source-acquisition Search.corePolicySearchDirective Residual.missingInstitutionalConstraint)
  refl refl refl

statutoryCoherenceBoundSourceDemand :
  BoundCertifiedSearchDemand DutyProof.statutoryCoherencePromotion Residual.dutyResidualKind dutyProducer
    Residual.missingStatutoryPredicate
statutoryCoherenceBoundSourceDemand = Bound.bound-acquisition-demand
  (legal-source-acquisition Search.statutoryCoherenceSearchDirective Residual.missingStatutoryPredicate)
  refl refl refl

------------------------------------------------------------------------
-- Herzog / colonial WrongType maps and exact bound demands.
------------------------------------------------------------------------

herzogResidual : HerzogElement.MechanismRequirementKind → Residual.LegalResidualKind
herzogResidual HerzogElement.requiresAuthorityMeaningErasure = Residual.missingRelationalFeature
herzogResidual HerzogElement.requiresOperationalPrerequisite = Residual.missingInstitutionalConstraint
herzogResidual HerzogElement.requiresSameObjectProjectionPowerIncident = Residual.missingFactualFeature

herzogProducer : HerzogElement.MechanismRequirementKind → Intent.ProducerClass
herzogProducer HerzogElement.requiresAuthorityMeaningErasure = Intent.historicalContextProducer
herzogProducer HerzogElement.requiresOperationalPrerequisite = Intent.authorityDiscoveryProducer
herzogProducer HerzogElement.requiresSameObjectProjectionPowerIncident = Intent.occurrenceEvidenceProducer

herzogAuthorityMeaningBoundSourceDemand :
  BoundCertifiedSearchDemand HerzogProof.currentAuthorityPromotion herzogResidual herzogProducer
    Residual.missingRelationalFeature
herzogAuthorityMeaningBoundSourceDemand = Bound.bound-acquisition-demand
  (legal-source-acquisition Search.herzogAuthorityMeaningSearchDirective Residual.missingRelationalFeature)
  refl refl refl

herzogPowerPrerequisiteBoundSourceDemand :
  BoundCertifiedSearchDemand HerzogProof.afterAuthorityPowerPromotion herzogResidual herzogProducer
    Residual.missingInstitutionalConstraint
herzogPowerPrerequisiteBoundSourceDemand = Bound.bound-acquisition-demand
  (legal-source-acquisition Search.herzogPowerPrerequisiteSearchDirective Residual.missingInstitutionalConstraint)
  refl refl refl

herzogIncidentWeldBoundSourceDemand :
  BoundCertifiedSearchDemand HerzogProof.afterPowerIncidentPromotion herzogResidual herzogProducer
    Residual.missingFactualFeature
herzogIncidentWeldBoundSourceDemand = Bound.bound-acquisition-demand
  (legal-source-acquisition Search.herzogIncidentWeldSearchDirective Residual.missingFactualFeature)
  refl refl refl

------------------------------------------------------------------------
-- Firewalls inherited from the generic carrier remain explicit here.
------------------------------------------------------------------------

data LooseDirectiveCountsAsBoundProgress : Set where
data BoundSourceDemandCreatesLegalAuthority : Set where
data BoundSourceForOneRequirementClosesSiblingRequirement : Set where

looseDirectiveIsNotBoundProgress : LooseDirectiveCountsAsBoundProgress → ⊥
looseDirectiveIsNotBoundProgress ()

boundDemandStillNeedsAssessment : Bound.BoundDemandAutomaticallyPaysRequirement → ⊥
boundDemandStillNeedsAssessment = Bound.bindingDoesNotPayRequirement

boundDemandDoesNotCreateAuthority : BoundSourceDemandCreatesLegalAuthority → ⊥
boundDemandDoesNotCreateAuthority ()

boundDemandDoesNotCloseSibling : BoundSourceForOneRequirementClosesSiblingRequirement → ⊥
boundDemandDoesNotCloseSibling ()
