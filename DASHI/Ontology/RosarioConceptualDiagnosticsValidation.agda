module DASHI.Ontology.RosarioConceptualDiagnosticsValidation where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Ontology.RosarioConceptualDiagnosticsExact
open import DASHI.Ontology.RosarioReportedEmpiricsExact

positiveAllYesIsAgreement :
  classifyCluster positiveEdge allYes ≡ consistentAgreement
positiveAllYesIsAgreement = refl

positiveAllNoIsFalseNegativeDisagreement :
  classifyCluster positiveEdge allNo ≡ consistentDisagreementFalseNegative
positiveAllNoIsFalseNegativeDisagreement = refl

negativeAllYesIsFalsePositiveDisagreement :
  classifyCluster negativeEdge allYes ≡ consistentDisagreementFalsePositive
negativeAllYesIsFalsePositiveDisagreement = refl

mixedResponsesRemainConceptuallyInconsistent :
  classifyCluster positiveEdge mixedYesNo ≡ conceptuallyInconsistent
mixedResponsesRemainConceptuallyInconsistent = refl

musicGenresClusterCountPinned :
  domainClusterCount musicGenres ≡ 1990
musicGenresClusterCountPinned = refl

reportedInconsistencyApproximationPinned :
  reportedInconsistentPercent ≡ 10
reportedInconsistencyApproximationPinned = refl

reportedConsistentDisagreementApproximationPinned :
  reportedConsistentDisagreementPercent ≡ 2
reportedConsistentDisagreementApproximationPinned = refl

kgIsNotAutomaticallyGroundTruth :
  KGGroundTruthPromotionPermission → ⊥
kgIsNotAutomaticallyGroundTruth = kgCannotPromoteItselfToGroundTruth

edgeAbsenceIsNotGenericNegation :
  EdgeAbsenceNegationPromotionPermission → ⊥
edgeAbsenceIsNotGenericNegation = absenceCannotBecomeNegationOutsideBenchmarkConvention

llmConsensusIsNotOntologyTruth :
  LLMConsensusTruthPermission → ⊥
llmConsensusIsNotOntologyTruth = llmConsensusCannotAssertOntologyTruth

llmHotspotIsNotEditAuthority :
  LLMHotspotEditPermission → ⊥
llmHotspotIsNotEditAuthority = llmHotspotCannotAuthorizeEdit

canonicalStatusPinsSourceBoundary :
  sourceClaimsRemainBounded canonicalRosarioConceptualDiagnosticsStatus ≡ true
canonicalStatusPinsSourceBoundary =
  sourceClaimsRemainBoundedIsTrue canonicalRosarioConceptualDiagnosticsStatus

canonicalStatusPinsBidirectionalBoundary :
  diagnosticAndRepairDirectionsSeparated canonicalRosarioConceptualDiagnosticsStatus ≡ true
canonicalStatusPinsBidirectionalBoundary =
  diagnosticAndRepairDirectionsSeparatedIsTrue canonicalRosarioConceptualDiagnosticsStatus
