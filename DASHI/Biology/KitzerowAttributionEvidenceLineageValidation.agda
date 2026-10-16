module DASHI.Biology.KitzerowAttributionEvidenceLineageValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.KitzerowAttributionEvidenceLineageExact as Lineage
import DASHI.Biology.KitzerowAttributionProvenanceSOTAExact as SOTA

republicationAndReportMultiplicityDoNotCreateIndependence :
  Lineage.downstreamPublicationMultiplicityCreatesIndependentEvidence Lineage.canonicalKitzerowAttributionLineageBoundary ≡ false
  × Lineage.sameProvenanceRootMayBeCountedRepeatedlyAsIndependent Lineage.canonicalKitzerowAttributionLineageBoundary ≡ false
republicationAndReportMultiplicityDoNotCreateIndependence = refl , refl

contactChronologyDoesNotCollapseIntoDerivation :
  Lineage.contactOrExposureAloneProvesDerivation Lineage.canonicalKitzerowAttributionLineageBoundary ≡ false
  × Lineage.postPublicationContactProvesPrePublicationExposure Lineage.canonicalKitzerowAttributionLineageBoundary ≡ false
  × Lineage.authenticatedPrePublicationExposureAloneProvesDerivation Lineage.canonicalKitzerowAttributionLineageBoundary ≡ false
contactChronologyDoesNotCollapseIntoDerivation = refl , (refl , refl)

plagiarismEvidenceKindsRemainDistinct :
  Lineage.citationAbsenceAloneProvesPlagiarism Lineage.canonicalKitzerowAttributionLineageBoundary ≡ false
  × Lineage.structuralSimilarityAloneProvesPlagiarism Lineage.canonicalKitzerowAttributionLineageBoundary ≡ false
  × Lineage.ideaProcessResultReuseCanBeRelevantToPlagiarism Lineage.canonicalKitzerowAttributionLineageBoundary ≡ true
  × Lineage.documentedDirectUseCanUpgradeDerivation Lineage.canonicalKitzerowAttributionLineageBoundary ≡ true
plagiarismEvidenceKindsRemainDistinct = refl , (refl , (refl , refl))

brazilPostPublicationContactCannotPayEarlierExposure :
  Lineage.brazilPostPublicationContactPaysPrePublicationExposure Lineage.canonicalBrazilDirectionalProvenance ≡ false
  × Lineage.brazilNeedsEarlierExposureOrManuscriptHistory Lineage.canonicalBrazilDirectionalProvenance ≡ true
brazilPostPublicationContactCannotPayEarlierExposure = refl , refl

originatorContactReportsRemainOneProvenanceRoot :
  Lineage.contactReportMultiplicityInflatesIndependence Lineage.canonicalKitzerowContactIndependenceReceipt ≡ false
originatorContactReportsRemainOneProvenanceRoot = refl

similarityToolsAreDiscoveryInputsNotAdjudicators :
  SOTA.similarityToolDeterminesPlagiarism SOTA.canonicalAttributionProvenanceSOTABoundary ≡ false
  × SOTA.similarityThresholdAutomaticallyAdjudicatesReuse SOTA.canonicalAttributionProvenanceSOTABoundary ≡ false
similarityToolsAreDiscoveryInputsNotAdjudicators = refl , refl

surroundingSOTAConstrainsVocabularyWithoutAdjudicatingCase :
  SOTA.oriVocabularyIncludesIdeasProcessesResultsWords SOTA.canonicalAttributionProvenanceSOTABoundary ≡ true
  × SOTA.cochraneSeparatesReportsFromStudyUnits SOTA.canonicalAttributionProvenanceSOTABoundary ≡ true
  × SOTA.w3cSeparatesDerivationRevisionQuotationRelations SOTA.canonicalAttributionProvenanceSOTABoundary ≡ true
  × SOTA.copeTreatsDocumentaryEvidenceAsInvestigationInput SOTA.canonicalAttributionProvenanceSOTABoundary ≡ true
  × SOTA.similarityToolDeterminesPlagiarism SOTA.canonicalAttributionProvenanceSOTABoundary ≡ false
  × SOTA.guidanceAutomaticallyAdjudicatesKitzerowClaim SOTA.canonicalAttributionProvenanceSOTABoundary ≡ false
  × SOTA.institutionalGuidanceCreatesLegalConclusion SOTA.canonicalAttributionProvenanceSOTABoundary ≡ false
surroundingSOTAConstrainsVocabularyWithoutAdjudicatingCase =
  refl , (refl , (refl , (refl , (refl , (refl , refl)))))
