module DASHI.Law.HerzogUniversalLegalAlgebraEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SecurityClassificationInputLineageDagExact as Lineage
import DASHI.Law.HerzogUniversalLegalEvidenceBridgeExact as Bridge
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual

------------------------------------------------------------------------
-- Herzog/security material is an evidence/provenance producer for universal
-- legal reasoning, not a second legal system and not a source of legal authority
-- merely because it was produced by police/security institutions.
------------------------------------------------------------------------

currentHerzogClassificationContentRemainsOpen :
  Search.reachable 1 Bridge.currentHerzogGraph Bridge.currentHerzogFacts
    Bridge.preActionClassificationContentEstablished ≡ false
currentHerzogClassificationContentRemainsOpen =
  Bridge.currentPreActionClassificationStillUnreachable

currentHerzogLegalQualificationRemainsOpen :
  Search.reachable 1 Bridge.currentHerzogGraph Bridge.currentHerzogFacts
    Bridge.legalQualificationOfClassification ≡ false
currentHerzogLegalQualificationRemainsOpen =
  Bridge.currentLegalQualificationStillUnreachable

classificationContentResidualRequestsFactualEvidence :
  Residual.preferredRoute
    (Bridge.lineageResidualKind Lineage.classificationContentResidual)
  ≡ Residual.obtainFactualEvidence
classificationContentResidualRequestsFactualEvidence = refl

carrierResidualRequestsProvenanceRecovery :
  Residual.preferredRoute
    (Bridge.lineageResidualKind Lineage.carrierContentResidual)
  ≡ Residual.askSituatedHolder
carrierResidualRequestsProvenanceRecovery = refl

sameIncidentStillDoesNotPayCausation :
  Bridge.SameIncidentCreatesCausalContribution → ⊥
sameIncidentStillDoesNotPayCausation = Bridge.sameIncidentDoesNotCreateCausation

causationStillDoesNotPayLegalAttribution :
  Bridge.CausalContributionCreatesLegalAttribution → ⊥
causationStillDoesNotPayLegalAttribution = Bridge.causationDoesNotCreateLegalAttribution

legalAttributionStillDoesNotPayLiability :
  Bridge.LegalAttributionAutomaticallyCreatesLiability → ⊥
legalAttributionStillDoesNotPayLiability =
  Bridge.attributionDoesNotAutomaticallyCreateLiability

data HerzogUniversalAggregateMeansKernelValidated : Set where
aggregateDoesNotClaimKernelValidation :
  HerzogUniversalAggregateMeansKernelValidated → ⊥
aggregateDoesNotClaimKernelValidation ()
