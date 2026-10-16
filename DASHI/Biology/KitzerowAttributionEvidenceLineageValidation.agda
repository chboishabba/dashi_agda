module DASHI.Biology.KitzerowAttributionEvidenceLineageValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.KitzerowAttributionEvidenceLineageExact as Lineage

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
