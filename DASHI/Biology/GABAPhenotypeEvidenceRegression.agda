module DASHI.Biology.GABAPhenotypeEvidenceRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Biology.GABAPhenotypeEvidenceExact as Evidence
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.CandidateOnlyCore as CandidateOnlyCore

------------------------------------------------------------------------
-- Focused regression surface for the bounded GABA / phenotype evidence lane.
------------------------------------------------------------------------

sourceAtlasNonAuthorityRegression :
  Source.atlasCreatesAuthority Evidence.canonicalSourceAtlas ≡ false
sourceAtlasNonAuthorityRegression =
  Evidence.canonicalSourceAtlasDoesNotCreateAuthority

gabaCandidateBoundaryRegression :
  CandidateOnlyCore.candidateOnly Evidence.gabaVocabularyOwner ≡ true
gabaCandidateBoundaryRegression =
  Evidence.gabaVocabularyOwnerRemainsCandidateOnly

associationCausalityGateRegression :
  Evidence.AssociationIsCausalSufficiencyPermission → ⊥
associationCausalityGateRegression =
  Evidence.associationDoesNotImplyCausalSufficiency

regionalWholeBrainGateRegression :
  Evidence.RegionalDifferenceIsWholeBrainDifferencePermission → ⊥
regionalWholeBrainGateRegression =
  Evidence.regionalGABADifferenceDoesNotImplyWholeBrainDifference

groupIndividualGateRegression :
  Evidence.GroupMeanClassifiesIndividualPermission → ⊥
groupIndividualGateRegression =
  Evidence.groupMeanDoesNotClassifyIndividual

diagnosisGABAGateRegression :
  Evidence.DiagnosisDeterminesGABALevelPermission → ⊥
diagnosisGABAGateRegression =
  Evidence.diagnosisDoesNotDetermineGABALevel

thoughtEmotionGateRegression :
  Evidence.ThoughtSuppressionIsEmotionSuppressionPermission → ⊥
thoughtEmotionGateRegression =
  Evidence.thoughtSuppressionEvidenceDoesNotPromoteToEmotionSuppression

synchronyAttachmentGateRegression :
  Evidence.SynchronyDefinesAttachmentPermission → ⊥
synchronyAttachmentGateRegression =
  Evidence.noAttachmentBridgeFromSynchronyWithoutReceipt

gabaNeuroinflammationGateRegression :
  Evidence.GABADefinesNeuroinflammationPermission → ⊥
gabaNeuroinflammationGateRegression =
  Evidence.noNeuroinflammationBridgeFromGABAWithoutReceipt

autismCausalSufficiencyGateRegression :
  Evidence.AutismCausedByLowGABAPermission → ⊥
autismCausalSufficiencyGateRegression =
  Evidence.autismLowGABAAssociationDoesNotProveCausalSufficiency

adhdCausalSufficiencyGateRegression :
  Evidence.ADHDCausedByLowGABAPermission → ⊥
adhdCausalSufficiencyGateRegression =
  Evidence.adhdGABAHypothesisDoesNotProveCausalSufficiency

sensoryUniversalizationGateRegression :
  Evidence.SensoryAssociationIsGlobalSeverityLawPermission → ⊥
sensoryUniversalizationGateRegression =
  Evidence.sensoryAssociationDoesNotUniversalizeAutism

canonicalBoundaryRegression : Evidence.GABAPhenotypeBoundary
canonicalBoundaryRegression = Evidence.canonicalGABAPhenotypeBoundary
