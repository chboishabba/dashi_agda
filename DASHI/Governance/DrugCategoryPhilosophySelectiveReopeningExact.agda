module DASHI.Governance.DrugCategoryPhilosophySelectiveReopeningExact where

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Governance.ContestedDrugCategoryAtlasBidiExact as Atlas
import DASHI.Governance.DrugCategoryPhilosophyOperatorAtlasExact as Philosophy

------------------------------------------------------------------------
-- PHILOSOPHY-SEEDED SELECTIVE REOPENING
--
-- Philosophical audits do not prove empirical claims.  They may, however,
-- identify a typed residual demand.  If an admitted category/legitimacy/history
-- certificate depends on that residual coordinate, the certificate must reopen.
------------------------------------------------------------------------

data PhilosophyCategoryArtifact : Set where
  usePracticeAuditArtifact
  ideologicalClosureAuditArtifact
  subjectPositionAuditArtifact
  materialInterestAuditArtifact
  democraticLegitimacyAuditArtifact
  historicalClosureAuditArtifact

  usePracticeResidualArtifact
  closureResidualArtifact
  subjectAuthorshipResidualArtifact
  materialBenefitResidualArtifact
  legitimacyResidualArtifact
  historicalPathResidualArtifact

  lexicalCategoryCertificate
  categoryAuthorityCertificate
  commercialReclamationCertificate
  legitimacyCertificate
  historicalClassifierCertificate
  consumerRouteCertificate
  : PhilosophyCategoryArtifact

data Depends : PhilosophyCategoryArtifact → PhilosophyCategoryArtifact → Set where
  useAuditToResidual :
    Depends usePracticeAuditArtifact usePracticeResidualArtifact
  useResidualToLexicalCategory :
    Depends usePracticeResidualArtifact lexicalCategoryCertificate
  lexicalCategoryToConsumer :
    Depends lexicalCategoryCertificate consumerRouteCertificate

  closureAuditToResidual :
    Depends ideologicalClosureAuditArtifact closureResidualArtifact
  closureResidualToHistorical :
    Depends closureResidualArtifact historicalClassifierCertificate
  historicalToConsumer :
    Depends historicalClassifierCertificate consumerRouteCertificate

  subjectAuditToResidual :
    Depends subjectPositionAuditArtifact subjectAuthorshipResidualArtifact
  subjectResidualToAuthority :
    Depends subjectAuthorshipResidualArtifact categoryAuthorityCertificate
  authorityToConsumer :
    Depends categoryAuthorityCertificate consumerRouteCertificate

  materialAuditToResidual :
    Depends materialInterestAuditArtifact materialBenefitResidualArtifact
  materialResidualToCommercial :
    Depends materialBenefitResidualArtifact commercialReclamationCertificate
  commercialToConsumer :
    Depends commercialReclamationCertificate consumerRouteCertificate

  legitimacyAuditToResidual :
    Depends democraticLegitimacyAuditArtifact legitimacyResidualArtifact
  legitimacyResidualToCertificate :
    Depends legitimacyResidualArtifact legitimacyCertificate
  legitimacyToConsumer :
    Depends legitimacyCertificate consumerRouteCertificate

  historicalAuditToResidual :
    Depends historicalClosureAuditArtifact historicalPathResidualArtifact
  historicalResidualToClassifier :
    Depends historicalPathResidualArtifact historicalClassifierCertificate

wittgensteinUseAuditReopensConsumer :
  Affected.ReopeningObligation
    Depends usePracticeAuditArtifact consumerRouteCertificate
wittgensteinUseAuditReopensConsumer =
  Affected.obligationsCompose
    (Affected.obligationsCompose
      (Affected.oneEdgeCreatesReopeningObligation useAuditToResidual)
      (Affected.oneEdgeCreatesReopeningObligation useResidualToLexicalCategory))
    (Affected.oneEdgeCreatesReopeningObligation lexicalCategoryToConsumer)

zizekClosureAuditReopensConsumer :
  Affected.ReopeningObligation
    Depends ideologicalClosureAuditArtifact consumerRouteCertificate
zizekClosureAuditReopensConsumer =
  Affected.obligationsCompose
    (Affected.obligationsCompose
      (Affected.oneEdgeCreatesReopeningObligation closureAuditToResidual)
      (Affected.oneEdgeCreatesReopeningObligation closureResidualToHistorical))
    (Affected.oneEdgeCreatesReopeningObligation historicalToConsumer)

feministSubjectAuditReopensConsumer :
  Affected.ReopeningObligation
    Depends subjectPositionAuditArtifact consumerRouteCertificate
feministSubjectAuditReopensConsumer =
  Affected.obligationsCompose
    (Affected.obligationsCompose
      (Affected.oneEdgeCreatesReopeningObligation subjectAuditToResidual)
      (Affected.oneEdgeCreatesReopeningObligation subjectResidualToAuthority))
    (Affected.oneEdgeCreatesReopeningObligation authorityToConsumer)

marxMaterialAuditReopensCommercialRoute :
  Affected.ReopeningObligation
    Depends materialInterestAuditArtifact consumerRouteCertificate
marxMaterialAuditReopensCommercialRoute =
  Affected.obligationsCompose
    (Affected.obligationsCompose
      (Affected.oneEdgeCreatesReopeningObligation materialAuditToResidual)
      (Affected.oneEdgeCreatesReopeningObligation materialResidualToCommercial))
    (Affected.oneEdgeCreatesReopeningObligation commercialToConsumer)

foucaultLegitimacyAuditReopensConsumer :
  Affected.ReopeningObligation
    Depends democraticLegitimacyAuditArtifact consumerRouteCertificate
foucaultLegitimacyAuditReopensConsumer =
  Affected.obligationsCompose
    (Affected.obligationsCompose
      (Affected.oneEdgeCreatesReopeningObligation legitimacyAuditToResidual)
      (Affected.oneEdgeCreatesReopeningObligation legitimacyResidualToCertificate))
    (Affected.oneEdgeCreatesReopeningObligation legitimacyToConsumer)

------------------------------------------------------------------------
-- Selectivity / no-promotion.
------------------------------------------------------------------------

wittgensteinUseAuditDoesNotDirectlyRewriteCommercialCertificate :
  Depends usePracticeAuditArtifact commercialReclamationCertificate → ⊥
wittgensteinUseAuditDoesNotDirectlyRewriteCommercialCertificate ()

materialAuditDoesNotDirectlyRewriteSubjectAuthority :
  Depends materialInterestAuditArtifact categoryAuthorityCertificate → ⊥
materialAuditDoesNotDirectlyRewriteSubjectAuthority ()

subjectAuditDoesNotDirectlyRewriteHistoricalClassifier :
  Depends subjectPositionAuditArtifact historicalClassifierCertificate → ⊥
subjectAuditDoesNotDirectlyRewriteHistoricalClassifier ()

record PhilosophySeededReopeningBoundary : Set where
  constructor philosophySeededReopeningBoundary
  field
    auditCanSeedTypedResidualDemand : Bool
    auditCanSeedTypedResidualDemandIsTrue :
      auditCanSeedTypedResidualDemand ≡ true
    residualDemandCanReopenAffectedCertificate : Bool
    residualDemandCanReopenAffectedCertificateIsTrue :
      residualDemandCanReopenAffectedCertificate ≡ true
    everyPhilosophicalAuditReopensEveryCategory : Bool
    everyPhilosophicalAuditReopensEveryCategoryIsFalse :
      everyPhilosophicalAuditReopensEveryCategory ≡ false
    reopeningProvesPhilosophicalInterpretation : Bool
    reopeningProvesPhilosophicalInterpretationIsFalse :
      reopeningProvesPhilosophicalInterpretation ≡ false
    reopeningSelectsReplacementCategory : Bool
    reopeningSelectsReplacementCategoryIsFalse :
      reopeningSelectsReplacementCategory ≡ false

canonicalPhilosophySeededReopeningBoundary : PhilosophySeededReopeningBoundary
canonicalPhilosophySeededReopeningBoundary =
  philosophySeededReopeningBoundary
    true refl
    true refl
    false refl
    false refl
    false refl

philosophyBoundary : Philosophy.DrugCategoryPhilosophyOperatorBoundary
philosophyBoundary = Philosophy.canonicalDrugCategoryPhilosophyOperatorBoundary

atlasBoundary : Atlas.ContestedDrugCategoryAtlasBoundary
atlasBoundary = Atlas.canonicalContestedDrugCategoryAtlasBoundary
