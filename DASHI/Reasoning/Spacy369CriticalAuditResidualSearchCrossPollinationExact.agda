module DASHI.Reasoning.Spacy369CriticalAuditResidualSearchCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.CostedResidualInformationChoiceExact as Costed
import DASHI.Reasoning.AristotleResidualInformationSearchExact as AristotleResidual
import DASHI.Reasoning.SemanticCandidateResidualBidiExact as Semantic
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.Spacy369FeministLacanConsumerRelativeExact as Consumer
import DASHI.Reasoning.Spacy369CriticalRelationalAuditExact as Audit
import DASHI.Reasoning.Spacy369CriticalAuditDiscriminatorPlannerExact as Planner
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as Trace

------------------------------------------------------------------------
-- COSTED RESIDUAL SEARCH OVER THE MATERIALISED SPACY/369 AUDIT LANE.
--
-- The canonical CostedResidualInformationChoice owner intentionally permits
-- heterogeneous information moves to share a residual-progress objective while
-- retaining their kinds.  Here the relevant moves are context/provenance audits
-- over semantic scope or situated subject position.  They remain information
-- progress, not theorem proof or empirical causal identification.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Scope branch: after a reviewed broad-scope outcome, retain only candidates
-- compatible with that outcome.  The fibre refinement is literal intersection.
------------------------------------------------------------------------

scopePrior : Bidi.ResidualFibre Candidate.CandidateSemanticFragment
scopePrior = Semantic.semanticCandidateFibre Trace.candidateFibre

broadScopePosterior : Bidi.ResidualFibre Candidate.CandidateSemanticFragment
broadScopePosterior candidate =
  scopePrior candidate ×
  Consumer.scopeConsumer candidate ≡ Consumer.broadScopeDecision

broadScopePosteriorRefinesPrior :
  Bidi.FibreRefines broadScopePosterior scopePrior
broadScopePosteriorRefinesPrior candidate witness = proj₁ witness

broadScopeContextAuditMove :
  Costed.ResidualInformationMove Candidate.CandidateSemanticFragment
broadScopeContextAuditMove =
  Costed.residualInformationMove
    scopePrior
    broadScopePosterior
    broadScopePosteriorRefinesPrior
    Costed.contextAuditResidualMove
    1
    1
    "materialised-spacy: broad-scope review outcome"
    "finite fixture: broad/narrow candidate distinction yields declared residual gain"
    "same spaCy dependency evidence; downstream scope adjudication only"
    "scope review authority required"
    "other semantic/world coordinates may remain unresolved"

narrowScopePosterior : Bidi.ResidualFibre Candidate.CandidateSemanticFragment
narrowScopePosterior candidate =
  scopePrior candidate ×
  Consumer.scopeConsumer candidate ≡ Consumer.narrowScopeDecision

narrowScopePosteriorRefinesPrior :
  Bidi.FibreRefines narrowScopePosterior scopePrior
narrowScopePosteriorRefinesPrior candidate witness = proj₁ witness

narrowScopeContextAuditMove :
  Costed.ResidualInformationMove Candidate.CandidateSemanticFragment
narrowScopeContextAuditMove =
  Costed.residualInformationMove
    scopePrior
    narrowScopePosterior
    narrowScopePosteriorRefinesPrior
    Costed.contextAuditResidualMove
    1
    1
    "materialised-spacy: narrow-scope review outcome"
    "finite fixture: broad/narrow candidate distinction yields declared residual gain"
    "same spaCy dependency evidence; downstream scope adjudication only"
    "scope review authority required"
    "other semantic/world coordinates may remain unresolved"

------------------------------------------------------------------------
-- Subject-position branch: this is a DIFFERENT hidden carrier.  It cannot be
-- silently compared as if scope and subject position were one coordinate.
------------------------------------------------------------------------

subjectPrior : Bidi.ResidualFibre Consumer.SituatedSpacyReading
subjectPrior state = ⊤

representedSubjectPosterior : Bidi.ResidualFibre Consumer.SituatedSpacyReading
representedSubjectPosterior state =
  subjectPrior state ×
  Consumer.subjectPositionResidual state ≡
    Consumer.subjectPositionResidual Consumer.representedReading

representedSubjectPosteriorRefinesPrior :
  Bidi.FibreRefines representedSubjectPosterior subjectPrior
representedSubjectPosteriorRefinesPrior state witness = proj₁ witness

subjectPositionContextAuditMove :
  Costed.ResidualInformationMove Consumer.SituatedSpacyReading
subjectPositionContextAuditMove =
  Costed.residualInformationMove
    subjectPrior
    representedSubjectPosterior
    representedSubjectPosteriorRefinesPrior
    Costed.contextAuditResidualMove
    2
    1
    "critical relational audit: acquire subject-position/provenance coordinate"
    "finite situated collision is split by the added subject-position observer"
    "parser/369 surface remains unchanged"
    "independent situated/provenance evidence required"
    "scope and other relational coordinates may remain unresolved"

------------------------------------------------------------------------
-- The already-closed operational consumer has no corresponding residual move.
-- That absence is deliberate: a planner should not manufacture information
-- acquisition merely because additional questions exist for other consumers.
------------------------------------------------------------------------

data OperationalConsumerNeedsResidualMove : Set where

closedOperationalConsumerDoesNotRequireResidualMove :
  OperationalConsumerNeedsResidualMove → ⊥
closedOperationalConsumerDoesNotRequireResidualMove ()

------------------------------------------------------------------------
-- Far cross-pollination: Aristotle residual search uses the same generic costed
-- residual owner, but proof-search progress remains constructor-distinct from a
-- theorem proof.  We consume the boundary rather than identifying parser review
-- with proof-search actions.
------------------------------------------------------------------------

aristotleResidualBoundary : AristotleResidual.AristotleResidualSearchBoundary
aristotleResidualBoundary = AristotleResidual.canonicalAristotleResidualSearchBoundary

scopeResidualProgressIsNotTheoremProof :
  Costed.partialResidualProgress ≡ Costed.theoremProved → ⊥
scopeResidualProgressIsNotTheoremProof = Costed.partialProgressNotTheoremProof

scopeResidualProgressIsNotExactMechanism :
  Costed.partialResidualProgress ≡ Costed.exactMechanismIdentified → ⊥
scopeResidualProgressIsNotExactMechanism =
  Costed.partialProgressNotMechanismIdentification

------------------------------------------------------------------------
-- Audit families may all be context-audit moves at this generic cost layer,
-- while remaining semantically distinct at the critical-audit layer.  Sharing
-- a move kind is therefore NOT identity of residual demand.
------------------------------------------------------------------------

auditMoveKind : Audit.CriticalAuditLens → Costed.ResidualInformationMoveKind
auditMoveKind Audit.parserScopeAudit = Costed.contextAuditResidualMove
auditMoveKind Audit.lacanianClosureResidualAudit = Costed.contextAuditResidualMove
auditMoveKind Audit.feministSubjectPositionAudit = Costed.contextAuditResidualMove
auditMoveKind Audit.irigarayanReciprocalRelationAudit = Costed.contextAuditResidualMove
auditMoveKind Audit.intersectionalMissingCoordinateAudit = Costed.contextAuditResidualMove

sameMoveKindDoesNotIdentifyAuditLens :
  auditMoveKind Audit.parserScopeAudit
  ≡ auditMoveKind Audit.feministSubjectPositionAudit
sameMoveKindDoesNotIdentifyAuditLens = refl

scopeAuditStillDistinctFromFeministAudit :
  Audit.parserScopeAudit ≡ Audit.feministSubjectPositionAudit → ⊥
scopeAuditStillDistinctFromFeministAudit = Audit.scopeAuditNotFeministAudit

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record Spacy369CriticalAuditResidualSearchBoundary : Set where
  constructor spacy369CriticalAuditResidualSearchBoundary
  field
    usefulAuditMoveMayNarrowResidualWithoutWorldIdentity : Bool
    usefulAuditMoveMayNarrowResidualWithoutWorldIdentityIsTrue :
      usefulAuditMoveMayNarrowResidualWithoutWorldIdentity ≡ true
    sameGenericMoveKindMeansSameCriticalQuestion : Bool
    sameGenericMoveKindMeansSameCriticalQuestionIsFalse :
      sameGenericMoveKindMeansSameCriticalQuestion ≡ false
    scopeAndSubjectAuditsMustShareHiddenCarrier : Bool
    scopeAndSubjectAuditsMustShareHiddenCarrierIsFalse :
      scopeAndSubjectAuditsMustShareHiddenCarrier ≡ false
    closedConsumerMustStillPayForResidualGain : Bool
    closedConsumerMustStillPayForResidualGainIsFalse :
      closedConsumerMustStillPayForResidualGain ≡ false
    residualGainIsTheoremProof : Bool
    residualGainIsTheoremProofIsFalse : residualGainIsTheoremProof ≡ false
    parserReviewIsDefinitionallyAristotleProofSearch : Bool
    parserReviewIsDefinitionallyAristotleProofSearchIsFalse :
      parserReviewIsDefinitionallyAristotleProofSearch ≡ false

canonicalSpacy369CriticalAuditResidualSearchBoundary :
  Spacy369CriticalAuditResidualSearchBoundary
canonicalSpacy369CriticalAuditResidualSearchBoundary =
  spacy369CriticalAuditResidualSearchBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
