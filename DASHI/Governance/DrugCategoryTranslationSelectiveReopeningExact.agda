module DASHI.Governance.DrugCategoryTranslationSelectiveReopeningExact where

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Governance.DrugCategoryMultiChartTranslationGeometryExact as Translation

------------------------------------------------------------------------
-- TRANSLATION-RESIDUAL SELECTIVE REOPENING
--
-- A translation residual reopens only certificates whose declared validity
-- depends on the lost/unresolved coordinate.  Translation loss is not global
-- invalidation and reopening is not refutation.
------------------------------------------------------------------------

data TranslationArtifact : Set where
  lexicalResidualArtifact
  useResidualArtifact
  subjectResidualArtifact
  communityResidualArtifact
  historyResidualArtifact
  legitimacyResidualArtifact
  materialResidualArtifact
  sovereigntyResidualArtifact

  stateClinicalTranslationCertificate
  clinicalLivedTranslationCertificate
  commercialTranslationCertificate
  lexicalMeaningCertificate
  clinicalSafetyCertificate
  subjectAuthorityCertificate
  historicalContinuityCertificate
  commercialBenefitCertificate
  sovereignAuthorityCertificate
  downstreamConsumerCertificate
  : TranslationArtifact

data Depends : TranslationArtifact → TranslationArtifact → Set where
  lexicalResidualReopensStateClinical :
    Depends lexicalResidualArtifact stateClinicalTranslationCertificate
  useResidualReopensStateClinical :
    Depends useResidualArtifact stateClinicalTranslationCertificate
  stateClinicalFeedsLexicalMeaning :
    Depends stateClinicalTranslationCertificate lexicalMeaningCertificate
  stateClinicalFeedsClinicalSafety :
    Depends stateClinicalTranslationCertificate clinicalSafetyCertificate

  subjectResidualReopensClinicalLived :
    Depends subjectResidualArtifact clinicalLivedTranslationCertificate
  historyResidualReopensClinicalLived :
    Depends historyResidualArtifact clinicalLivedTranslationCertificate
  clinicalLivedFeedsSubjectAuthority :
    Depends clinicalLivedTranslationCertificate subjectAuthorityCertificate
  clinicalLivedFeedsHistory :
    Depends clinicalLivedTranslationCertificate historicalContinuityCertificate

  materialResidualReopensCommercial :
    Depends materialResidualArtifact commercialTranslationCertificate
  sovereigntyResidualReopensCommercial :
    Depends sovereigntyResidualArtifact commercialTranslationCertificate
  commercialFeedsBenefit :
    Depends commercialTranslationCertificate commercialBenefitCertificate
  commercialFeedsSovereignty :
    Depends commercialTranslationCertificate sovereignAuthorityCertificate

  lexicalMeaningFeedsConsumer :
    Depends lexicalMeaningCertificate downstreamConsumerCertificate
  clinicalSafetyFeedsConsumer :
    Depends clinicalSafetyCertificate downstreamConsumerCertificate
  subjectAuthorityFeedsConsumer :
    Depends subjectAuthorityCertificate downstreamConsumerCertificate
  historicalContinuityFeedsConsumer :
    Depends historicalContinuityCertificate downstreamConsumerCertificate
  commercialBenefitFeedsConsumer :
    Depends commercialBenefitCertificate downstreamConsumerCertificate
  sovereignAuthorityFeedsConsumer :
    Depends sovereignAuthorityCertificate downstreamConsumerCertificate

subjectResidualReopensSubjectConsumer :
  Affected.ReopeningObligation
    Depends subjectResidualArtifact downstreamConsumerCertificate
subjectResidualReopensSubjectConsumer =
  Affected.obligationsCompose
    (Affected.obligationsCompose
      (Affected.oneEdgeCreatesReopeningObligation subjectResidualReopensClinicalLived)
      (Affected.oneEdgeCreatesReopeningObligation clinicalLivedFeedsSubjectAuthority))
    (Affected.oneEdgeCreatesReopeningObligation subjectAuthorityFeedsConsumer)

historyResidualReopensHistoricalConsumer :
  Affected.ReopeningObligation
    Depends historyResidualArtifact downstreamConsumerCertificate
historyResidualReopensHistoricalConsumer =
  Affected.obligationsCompose
    (Affected.obligationsCompose
      (Affected.oneEdgeCreatesReopeningObligation historyResidualReopensClinicalLived)
      (Affected.oneEdgeCreatesReopeningObligation clinicalLivedFeedsHistory))
    (Affected.oneEdgeCreatesReopeningObligation historicalContinuityFeedsConsumer)

sovereigntyResidualReopensSovereignConsumer :
  Affected.ReopeningObligation
    Depends sovereigntyResidualArtifact downstreamConsumerCertificate
sovereigntyResidualReopensSovereignConsumer =
  Affected.obligationsCompose
    (Affected.obligationsCompose
      (Affected.oneEdgeCreatesReopeningObligation sovereigntyResidualReopensCommercial)
      (Affected.oneEdgeCreatesReopeningObligation commercialFeedsSovereignty))
    (Affected.oneEdgeCreatesReopeningObligation sovereignAuthorityFeedsConsumer)

materialResidualReopensCommercialBenefitConsumer :
  Affected.ReopeningObligation
    Depends materialResidualArtifact downstreamConsumerCertificate
materialResidualReopensCommercialBenefitConsumer =
  Affected.obligationsCompose
    (Affected.obligationsCompose
      (Affected.oneEdgeCreatesReopeningObligation materialResidualReopensCommercial)
      (Affected.oneEdgeCreatesReopeningObligation commercialFeedsBenefit))
    (Affected.oneEdgeCreatesReopeningObligation commercialBenefitFeedsConsumer)

------------------------------------------------------------------------
-- Selectivity.
------------------------------------------------------------------------

clinicalFactResidualDoesNotExist : Set
clinicalFactResidualDoesNotExist = ⊥

subjectResidualDoesNotDirectlyReopenClinicalSafety :
  Depends subjectResidualArtifact clinicalSafetyCertificate → ⊥
subjectResidualDoesNotDirectlyReopenClinicalSafety ()

materialResidualDoesNotDirectlyReopenSubjectAuthority :
  Depends materialResidualArtifact subjectAuthorityCertificate → ⊥
materialResidualDoesNotDirectlyReopenSubjectAuthority ()

sovereigntyResidualDoesNotDirectlyRewriteLexicalMeaning :
  Depends sovereigntyResidualArtifact lexicalMeaningCertificate → ⊥
sovereigntyResidualDoesNotDirectlyRewriteLexicalMeaning ()

------------------------------------------------------------------------
-- BIDI reconstruction demand.
------------------------------------------------------------------------

data ReconstructionDemand : Translation.TranslationResidual → Set where
  recoverLexicalUseContext : ReconstructionDemand Translation.lexicalResidual
  recoverUsePractice : ReconstructionDemand Translation.useResidual
  recoverOriginatingSubjectPosition : ReconstructionDemand Translation.subjectResidual
  recoverAffectedCommunityVoice : ReconstructionDemand Translation.communityResidual
  recoverHistoricalClassifierPath : ReconstructionDemand Translation.historyResidual
  recoverLegitimacyBasis : ReconstructionDemand Translation.legitimacyResidual
  recoverBenefitAndExternalityRouting : ReconstructionDemand Translation.materialResidual
  recoverSovereignPermissionAuthority : ReconstructionDemand Translation.sovereigntyResidual

record TranslationReconstructionReceipt
    (residual : Translation.TranslationResidual) : Set where
  constructor translationReconstructionReceipt
  field
    demand : ReconstructionDemand residual
    sourceReference : String
    authorityReference : String
    reconstructedAsInherited : Bool
    reconstructedAsInheritedNeedsLineageProof : Bool
    reconstructedAsInheritedNeedsLineageProofIsTrue :
      reconstructedAsInheritedNeedsLineageProof ≡ true

record DrugCategoryTranslationReopeningBoundary : Set where
  constructor drugCategoryTranslationReopeningBoundary
  field
    coordinateLossCanSeedSelectiveReopening : Bool
    coordinateLossCanSeedSelectiveReopeningIsTrue :
      coordinateLossCanSeedSelectiveReopening ≡ true
    everyResidualReopensEveryCertificate : Bool
    everyResidualReopensEveryCertificateIsFalse :
      everyResidualReopensEveryCertificate ≡ false
    reconstructionDemandEqualsSuccessfulReconstruction : Bool
    reconstructionDemandEqualsSuccessfulReconstructionIsFalse :
      reconstructionDemandEqualsSuccessfulReconstruction ≡ false
    reopeningEqualsRefutation : Bool
    reopeningEqualsRefutationIsFalse : reopeningEqualsRefutation ≡ false

canonicalDrugCategoryTranslationReopeningBoundary :
  DrugCategoryTranslationReopeningBoundary
canonicalDrugCategoryTranslationReopeningBoundary =
  drugCategoryTranslationReopeningBoundary
    true refl
    false refl
    false refl
    false refl
