module DASHI.Culture.CohnInstitutionalDecisionRevisionBraidRegression where

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Culture.CohnInstitutionalDecisionRevisionBraidExact as Braid
import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as Expert

------------------------------------------------------------------------
-- Regression surface for the institutional decision / selective reopening braid.
--
-- The production owner is intentionally imported before implementation.  This
-- fixes the desired dependency and authority surface first.  Kernel RED/GREEN
-- certification remains separate from this source ordering.
------------------------------------------------------------------------

sourceGenealogyChangeReopensEvidenceAdequacy :
  Dependency.ReopeningObligation
    Braid.Depends
    Braid.sourceGenealogyArtifact
    Braid.evidenceAdequacyArtifact
sourceGenealogyChangeReopensEvidenceAdequacy =
  Braid.sourceGenealogyReopensEvidenceAdequacy

sourceGenealogyChangeReopensDecision :
  Dependency.ReopeningObligation
    Braid.Depends
    Braid.sourceGenealogyArtifact
    Braid.institutionalDecisionArtifact
sourceGenealogyChangeReopensDecision =
  Braid.sourceGenealogyReopensDecision

sourceGenealogyChangeReopensConsequence :
  Dependency.ReopeningObligation
    Braid.Depends
    Braid.sourceGenealogyArtifact
    Braid.consequenceArtifact
sourceGenealogyChangeReopensConsequence =
  Braid.sourceGenealogyReopensConsequence

normalityChangeReopensReasonableness :
  Dependency.ReopeningObligation
    Braid.Depends
    Braid.institutionalNormalityArtifact
    Braid.legalReasonablenessArtifact
normalityChangeReopensReasonableness =
  Braid.institutionalNormalityReopensLegalReasonableness

authorityChangeReopensDecision :
  Dependency.ReopeningObligation
    Braid.Depends
    Braid.authorityStatusArtifact
    Braid.institutionalDecisionArtifact
authorityChangeReopensDecision =
  Braid.authorityStatusReopensDecision

authorityChangeReopensConsequence :
  Dependency.ReopeningObligation
    Braid.Depends
    Braid.authorityStatusArtifact
    Braid.consequenceArtifact
authorityChangeReopensConsequence =
  Braid.authorityStatusReopensConsequence

agreementStillDoesNotCreateIndependence :
  Expert.AgreementAutomaticallyIndependentCorroboration → ⊥
agreementStillDoesNotCreateIndependence =
  Braid.agreementDoesNotCreateIndependentCorroboration

appendOnlyEvidenceMayReviseCurrentConclusion :
  Braid.appendOnlyEvidenceMayChangeCurrentConclusion
    Braid.canonicalInstitutionalDecisionRevisionBoundary ≡ true
appendOnlyEvidenceMayReviseCurrentConclusion = refl

staleDecisionIsNotRefutedDecision :
  Braid.staleDecisionEqualsRefutedDecision
    Braid.canonicalInstitutionalDecisionRevisionBoundary ≡ false
staleDecisionIsNotRefutedDecision = refl

reopeningDoesNotDeleteHistoricalEvidence :
  Braid.reopeningDeletesHistoricalEvidence
    Braid.canonicalInstitutionalDecisionRevisionBoundary ≡ false
reopeningDoesNotDeleteHistoricalEvidence = refl

evidenceAdequacyDoesNotCreateAuthority :
  Braid.evidenceAdequacyCreatesAuthority
    Braid.canonicalInstitutionalDecisionRevisionBoundary ≡ false
evidenceAdequacyDoesNotCreateAuthority = refl

consequenceSeverityDoesNotCreateEvidenceTruth :
  Braid.consequenceSeverityCreatesEvidenceTruth
    Braid.canonicalInstitutionalDecisionRevisionBoundary ≡ false
consequenceSeverityDoesNotCreateEvidenceTruth = refl
