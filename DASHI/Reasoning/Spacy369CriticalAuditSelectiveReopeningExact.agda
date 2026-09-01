module DASHI.Reasoning.Spacy369CriticalAuditSelectiveReopeningExact where

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as Trace
import DASHI.Reasoning.SpacyNegatedCoordinationScopeSelectiveReopeningExact as ScopePath
import DASHI.Reasoning.Spacy369FeministLacanConsumerRelativeExact as Consumer
import DASHI.Reasoning.Spacy369CriticalRelationalAuditExact as Audit

------------------------------------------------------------------------
-- SELECTIVE REOPENING FROM THE MATERIALISED SPACY/369 CRITICAL AUDIT ATLAS
--
-- The audit atlas asks several backward questions of the SAME materialised
-- parser/semantic/369 object.  This owner gives those questions disjoint
-- dependency paths.  An audit can therefore reopen exactly the certificates
-- that depend on its missing coordinate without becoming an alternative parser
-- semantics or globally invalidating the shared logical result.
------------------------------------------------------------------------

data CriticalAuditArtifact : Set where
  scopeAuditArtifact
  feministSubjectAuditArtifact
  lacanianClosureAuditArtifact
  irigarayanRelationAuditArtifact
  intersectionalAuditArtifact

  scopeResidualArtifact
  subjectPositionResidualArtifact
  closureResidualArtifact
  reciprocalRelationResidualArtifact
  situatedCoordinateResidualArtifact

  semanticScopeCertificate
  subjectSensitiveConsumerCertificate
  closureInterpretationCertificate
  reciprocalRelationCertificate
  situatedConsumerCertificate

  operationalConsumerCertificate
  ordinaryLogicalEntailmentCertificate
  materialisedParserEvidenceArtifact
  : CriticalAuditArtifact

data Depends : CriticalAuditArtifact → CriticalAuditArtifact → Set where
  scopeAuditRequestsScopeResidual :
    Depends scopeAuditArtifact scopeResidualArtifact
  scopeResidualFeedsSemanticScope :
    Depends scopeResidualArtifact semanticScopeCertificate

  feministAuditRequestsSubjectPosition :
    Depends feministSubjectAuditArtifact subjectPositionResidualArtifact
  subjectPositionFeedsSubjectConsumer :
    Depends subjectPositionResidualArtifact subjectSensitiveConsumerCertificate

  lacanianAuditRequestsClosureResidual :
    Depends lacanianClosureAuditArtifact closureResidualArtifact
  closureResidualFeedsClosureInterpretation :
    Depends closureResidualArtifact closureInterpretationCertificate

  irigarayanAuditRequestsRelationResidual :
    Depends irigarayanRelationAuditArtifact reciprocalRelationResidualArtifact
  relationResidualFeedsRelationCertificate :
    Depends reciprocalRelationResidualArtifact reciprocalRelationCertificate

  intersectionalAuditRequestsSituatedCoordinate :
    Depends intersectionalAuditArtifact situatedCoordinateResidualArtifact
  situatedCoordinateFeedsSituatedConsumer :
    Depends situatedCoordinateResidualArtifact situatedConsumerCertificate

------------------------------------------------------------------------
-- Exact typed reopening obligations.
------------------------------------------------------------------------

scopeAuditReopensScopeCertificate :
  Affected.ReopeningObligation
    Depends scopeAuditArtifact semanticScopeCertificate
scopeAuditReopensScopeCertificate =
  Affected.obligationsCompose
    (Affected.oneEdgeCreatesReopeningObligation scopeAuditRequestsScopeResidual)
    (Affected.oneEdgeCreatesReopeningObligation scopeResidualFeedsSemanticScope)

feministAuditReopensSubjectSensitiveConsumer :
  Affected.ReopeningObligation
    Depends feministSubjectAuditArtifact subjectSensitiveConsumerCertificate
feministAuditReopensSubjectSensitiveConsumer =
  Affected.obligationsCompose
    (Affected.oneEdgeCreatesReopeningObligation feministAuditRequestsSubjectPosition)
    (Affected.oneEdgeCreatesReopeningObligation subjectPositionFeedsSubjectConsumer)

lacanianAuditReopensClosureInterpretationOnly :
  Affected.ReopeningObligation
    Depends lacanianClosureAuditArtifact closureInterpretationCertificate
lacanianAuditReopensClosureInterpretationOnly =
  Affected.obligationsCompose
    (Affected.oneEdgeCreatesReopeningObligation lacanianAuditRequestsClosureResidual)
    (Affected.oneEdgeCreatesReopeningObligation closureResidualFeedsClosureInterpretation)

irigarayanAuditReopensReciprocalRelationCertificate :
  Affected.ReopeningObligation
    Depends irigarayanRelationAuditArtifact reciprocalRelationCertificate
irigarayanAuditReopensReciprocalRelationCertificate =
  Affected.obligationsCompose
    (Affected.oneEdgeCreatesReopeningObligation irigarayanAuditRequestsRelationResidual)
    (Affected.oneEdgeCreatesReopeningObligation relationResidualFeedsRelationCertificate)

intersectionalAuditReopensSituatedConsumer :
  Affected.ReopeningObligation
    Depends intersectionalAuditArtifact situatedConsumerCertificate
intersectionalAuditReopensSituatedConsumer =
  Affected.obligationsCompose
    (Affected.oneEdgeCreatesReopeningObligation intersectionalAuditRequestsSituatedCoordinate)
    (Affected.oneEdgeCreatesReopeningObligation situatedCoordinateFeedsSituatedConsumer)

------------------------------------------------------------------------
-- Materialised anchors: these aliases keep the dependency calculus attached to
-- the actual SensibLaw fixture and its already-proved consumer facts.
------------------------------------------------------------------------

materialisedScopeAudit : Audit.MaterialisedSpacyCriticalAudit Audit.parserScopeAudit
materialisedScopeAudit = Audit.scopeAudit

materialisedFeministAudit :
  Audit.MaterialisedSpacyCriticalAudit Audit.feministSubjectPositionAudit
materialisedFeministAudit = Audit.feministPositionAudit

materialisedLacanianAudit :
  Audit.MaterialisedSpacyCriticalAudit Audit.lacanianClosureResidualAudit
materialisedLacanianAudit = Audit.lacanianResidualAudit

materialisedIrigarayanAudit :
  Audit.MaterialisedSpacyCriticalAudit Audit.irigarayanReciprocalRelationAudit
materialisedIrigarayanAudit = Audit.irigarayanRelationAudit

operationalConsumerAlreadyClosed =
  Consumer.operationalClosureReceipt

scopeConsumerStillOpen =
  Consumer.scopeSensitiveConsumerNotClosed

broadMaterialisedScopePathCertificate =
  ScopePath.broadScopeCertificate

narrowMaterialisedScopePathCertificate =
  ScopePath.narrowScopeCertificate

------------------------------------------------------------------------
-- Least-privilege no-direct-dependency results.
--
-- Ordinary object logic and the already-closed operational consumer are absent
-- from the audit-generated dependency graph.  Likewise one audit family cannot
-- directly rewrite another family's certificate merely because all are attached
-- to the same parser/369 surface.
------------------------------------------------------------------------

scopeAuditDoesNotDirectlyRewriteOperationalConsumer :
  Depends scopeAuditArtifact operationalConsumerCertificate → ⊥
scopeAuditDoesNotDirectlyRewriteOperationalConsumer ()

scopeAuditDoesNotDirectlyRewriteOrdinaryLogic :
  Depends scopeAuditArtifact ordinaryLogicalEntailmentCertificate → ⊥
scopeAuditDoesNotDirectlyRewriteOrdinaryLogic ()

feministAuditDoesNotDirectlyRewriteScopeCertificate :
  Depends feministSubjectAuditArtifact semanticScopeCertificate → ⊥
feministAuditDoesNotDirectlyRewriteScopeCertificate ()

feministAuditDoesNotDirectlyRewriteOrdinaryLogic :
  Depends feministSubjectAuditArtifact ordinaryLogicalEntailmentCertificate → ⊥
feministAuditDoesNotDirectlyRewriteOrdinaryLogic ()

lacanianAuditDoesNotDirectlyRewriteOrdinaryLogic :
  Depends lacanianClosureAuditArtifact ordinaryLogicalEntailmentCertificate → ⊥
lacanianAuditDoesNotDirectlyRewriteOrdinaryLogic ()

lacanianAuditDoesNotDirectlyRewriteScopeCertificate :
  Depends lacanianClosureAuditArtifact semanticScopeCertificate → ⊥
lacanianAuditDoesNotDirectlyRewriteScopeCertificate ()

irigarayanAuditDoesNotDirectlyRewriteScopeCertificate :
  Depends irigarayanRelationAuditArtifact semanticScopeCertificate → ⊥
irigarayanAuditDoesNotDirectlyRewriteScopeCertificate ()

irigarayanAuditDoesNotDirectlyRewriteSubjectConsumer :
  Depends irigarayanRelationAuditArtifact subjectSensitiveConsumerCertificate → ⊥
irigarayanAuditDoesNotDirectlyRewriteSubjectConsumer ()

------------------------------------------------------------------------
-- Reopening does not rewrite the retained parser observation.  The parser
-- evidence is an upstream historical artifact; none of the audit constructors
-- target it.
------------------------------------------------------------------------

criticalAuditDoesNotDirectlyRewriteParserEvidence :
  (auditArtifact : CriticalAuditArtifact) →
  (auditArtifact ≡ scopeAuditArtifact
   ⊎ auditArtifact ≡ feministSubjectAuditArtifact
   ⊎ auditArtifact ≡ lacanianClosureAuditArtifact
   ⊎ auditArtifact ≡ irigarayanRelationAuditArtifact
   ⊎ auditArtifact ≡ intersectionalAuditArtifact) →
  Depends auditArtifact materialisedParserEvidenceArtifact → ⊥
criticalAuditDoesNotDirectlyRewriteParserEvidence .scopeAuditArtifact (inj₁ refl) ()
criticalAuditDoesNotDirectlyRewriteParserEvidence .feministSubjectAuditArtifact (inj₂ (inj₁ refl)) ()
criticalAuditDoesNotDirectlyRewriteParserEvidence .lacanianClosureAuditArtifact (inj₂ (inj₂ (inj₁ refl))) ()
criticalAuditDoesNotDirectlyRewriteParserEvidence .irigarayanRelationAuditArtifact (inj₂ (inj₂ (inj₂ (inj₁ refl)))) ()
criticalAuditDoesNotDirectlyRewriteParserEvidence .intersectionalAuditArtifact (inj₂ (inj₂ (inj₂ (inj₂ refl)))) ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record CriticalAuditSelectiveReopeningBoundary : Set where
  constructor criticalAuditSelectiveReopeningBoundary
  field
    scopeAuditCanReopenScopeCertificate : Bool
    scopeAuditCanReopenScopeCertificateIsTrue :
      scopeAuditCanReopenScopeCertificate ≡ true
    feministAuditCanReopenSubjectSensitiveConsumer : Bool
    feministAuditCanReopenSubjectSensitiveConsumerIsTrue :
      feministAuditCanReopenSubjectSensitiveConsumer ≡ true
    lacanianAuditCanReopenClosureInterpretation : Bool
    lacanianAuditCanReopenClosureInterpretationIsTrue :
      lacanianAuditCanReopenClosureInterpretation ≡ true
    irigarayanAuditCanReopenRelationCertificate : Bool
    irigarayanAuditCanReopenRelationCertificateIsTrue :
      irigarayanAuditCanReopenRelationCertificate ≡ true
    oneAuditAutomaticallyReopensAllConsumers : Bool
    oneAuditAutomaticallyReopensAllConsumersIsFalse :
      oneAuditAutomaticallyReopensAllConsumers ≡ false
    criticalAuditRewritesMaterialisedParserEvidence : Bool
    criticalAuditRewritesMaterialisedParserEvidenceIsFalse :
      criticalAuditRewritesMaterialisedParserEvidence ≡ false
    criticalAuditInvalidatesOrdinaryModusPonens : Bool
    criticalAuditInvalidatesOrdinaryModusPonensIsFalse :
      criticalAuditInvalidatesOrdinaryModusPonens ≡ false
    reopeningMeansRefutation : Bool
    reopeningMeansRefutationIsFalse : reopeningMeansRefutation ≡ false

canonicalCriticalAuditSelectiveReopeningBoundary :
  CriticalAuditSelectiveReopeningBoundary
canonicalCriticalAuditSelectiveReopeningBoundary =
  criticalAuditSelectiveReopeningBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
