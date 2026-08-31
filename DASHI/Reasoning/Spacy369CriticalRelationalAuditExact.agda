module DASHI.Reasoning.Spacy369CriticalRelationalAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IrigarayLabialRelationalCarrierExact as Irigaray
import DASHI.Core.LacanIrigarayTernaryGrammarBridgeExact as LI
import DASHI.Core.TernaryRoleCarrierExact as Ternary
import DASHI.Reasoning.PNFZizekOperator as Zizek
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SpacyPNF369DialecticBridgeExact as Bridge369
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as Trace
import DASHI.Reasoning.Spacy369FeministLacanConsumerRelativeExact as Consumer

------------------------------------------------------------------------
-- CRITICAL RELATIONAL AUDIT ATLAS OVER THE MATERIALISED SPACY/369 FIXTURE
--
-- The same parser/PNF/369 object can be asked different backward questions.
-- These questions do not become one master interpretation and do not alter the
-- spaCy evidence or object-logic consequence.
------------------------------------------------------------------------

data CriticalAuditLens : Set where
  parserScopeAudit
  lacanianClosureResidualAudit
  feministSubjectPositionAudit
  irigarayanReciprocalRelationAudit
  intersectionalMissingCoordinateAudit
  : CriticalAuditLens

data ResidualDemand : Set where
  moreScopeEvidence
  inspectMasterPredicateAndExcludedResidual
  addOriginatingSubjectPosition
  inspectReciprocalNonSovereignRelation
  addIntersectingSituatedCoordinate
  : ResidualDemand

auditDemand : CriticalAuditLens → ResidualDemand
 auditDemand parserScopeAudit = moreScopeEvidence
 auditDemand lacanianClosureResidualAudit = inspectMasterPredicateAndExcludedResidual
 auditDemand feministSubjectPositionAudit = addOriginatingSubjectPosition
 auditDemand irigarayanReciprocalRelationAudit = inspectReciprocalNonSovereignRelation
 auditDemand intersectionalMissingCoordinateAudit = addIntersectingSituatedCoordinate

record MaterialisedSpacyCriticalAudit (lens : CriticalAuditLens) : Set₁ where
  constructor materialisedSpacyCriticalAudit
  field
    semanticFibre : Candidate.CandidateSemanticFibre
    semanticFibreIsMaterialised : semanticFibre ≡ Trace.candidateFibre
    chart369 : Bridge369.SpacyCandidateDialectic369Atom
    chart369IsMaterialised : chart369 ≡ Trace.revised369
    demand : ResidualDemand
    demandMatchesLens : demand ≡ auditDemand lens
    parserEvidenceReference : String
    philosophicalSourceBoundaryReference : String
    auditCandidateOnly : Bool
    auditCandidateOnlyIsTrue : auditCandidateOnly ≡ true
    empiricalOrSubjectEvidenceStillRequired : Bool
    empiricalOrSubjectEvidenceStillRequiredIsTrue :
      empiricalOrSubjectEvidenceStillRequired ≡ true

open MaterialisedSpacyCriticalAudit public

scopeAudit : MaterialisedSpacyCriticalAudit parserScopeAudit
scopeAudit =
  materialisedSpacyCriticalAudit
    Trace.candidateFibre refl
    Trace.revised369 refl
    moreScopeEvidence refl
    "materialised spaCy neg/coordination witnesses"
    "parser scope review; no philosophical authority required"
    true refl true refl

lacanianResidualAudit : MaterialisedSpacyCriticalAudit lacanianClosureResidualAudit
lacanianResidualAudit =
  materialisedSpacyCriticalAudit
    Trace.candidateFibre refl
    Trace.revised369 refl
    inspectMasterPredicateAndExcludedResidual refl
    "same materialised spaCy/PNF fixture"
    "PNFZizekOperator: master predicate / excluded object / imagined closure are candidate audits"
    true refl true refl

feministPositionAudit : MaterialisedSpacyCriticalAudit feministSubjectPositionAudit
feministPositionAudit =
  materialisedSpacyCriticalAudit
    Trace.candidateFibre refl
    Trace.revised369 refl
    addOriginatingSubjectPosition refl
    "same materialised spaCy/PNF fixture"
    "RepresentationSubjectPositionNonfactorability + FeministRechartingSourceBridge"
    true refl true refl

irigarayanRelationAudit : MaterialisedSpacyCriticalAudit irigarayanReciprocalRelationAudit
irigarayanRelationAudit =
  materialisedSpacyCriticalAudit
    Trace.candidateFibre refl
    Trace.revised369 refl
    inspectReciprocalNonSovereignRelation refl
    "same materialised spaCy/PNF fixture"
    "IrigarayLabialRelationalCarrierExact; finite reciprocal-contact comparison only"
    true refl true refl

------------------------------------------------------------------------
-- Different backward questions remain genuinely distinct even though they are
-- attached to the same parser fibre and same 369 review atom.
------------------------------------------------------------------------

scopeAuditNotFeministAudit : parserScopeAudit ≡ feministSubjectPositionAudit → ⊥
scopeAuditNotFeministAudit ()

lacanianAuditNotIrigarayanAudit :
  lacanianClosureResidualAudit ≡ irigarayanReciprocalRelationAudit → ⊥
lacanianAuditNotIrigarayanAudit ()

scopeDemandNotSubjectDemand : moreScopeEvidence ≡ addOriginatingSubjectPosition → ⊥
scopeDemandNotSubjectDemand ()

closureDemandNotReciprocalDemand :
  inspectMasterPredicateAndExcludedResidual ≡ inspectReciprocalNonSovereignRelation → ⊥
closureDemandNotReciprocalDemand ()

------------------------------------------------------------------------
-- Existing source-bounded theorem surfaces are consumed as boundaries.
------------------------------------------------------------------------

zizekPNFAuthorityBoundary : Zizek.PNFZizekAuthorityBoundary
zizekPNFAuthorityBoundary = Zizek.canonicalPNFZizekAuthorityBoundary

irigarayOrientationRemainsAmbiguous : Irigaray.OrientationAmbiguity
irigarayOrientationRemainsAmbiguous = Irigaray.canonicalOrientationAmbiguity

lacanIrigaraySharedCarrierStillDoesNotIdentifyGrammar :
  (permutation : Ternary.TernaryPermutation) →
  LI.GrammarPreserving permutation → ⊥
lacanIrigaraySharedCarrierStillDoesNotIdentifyGrammar =
  LI.noTernaryRelabellingPreservesGrammar

feministSubjectPositionStillDoesNotDescendThroughParser =
  Consumer.parserSurfaceCannotRecoverSubjectPosition

feministSubjectPositionStillDoesNotDescendThrough369 =
  Consumer.chart369CannotRecoverSubjectPosition

------------------------------------------------------------------------
-- No-promotion permissions: an audit can request a richer observation or
-- interpretation, but cannot directly construct parser semantics/world facts.
------------------------------------------------------------------------

data AuditPromotesParserSemanticTruth : Set where

data AuditPromotesEmpiricalCause : Set where

data LacanianAuditSelectsIrigarayanGrammar : Set where

data FeministRechartingSelectsScopeReading : Set where

criticalAuditCannotPromoteParserSemanticTruth : AuditPromotesParserSemanticTruth → ⊥
criticalAuditCannotPromoteParserSemanticTruth ()

criticalAuditCannotPromoteEmpiricalCause : AuditPromotesEmpiricalCause → ⊥
criticalAuditCannotPromoteEmpiricalCause ()

lacanianAuditCannotSelectIrigarayanGrammar : LacanianAuditSelectsIrigarayanGrammar → ⊥
lacanianAuditCannotSelectIrigarayanGrammar ()

feministRechartingCannotSelectScopeReading : FeministRechartingSelectsScopeReading → ⊥
feministRechartingCannotSelectScopeReading ()

record Spacy369CriticalRelationalAuditBoundary : Set where
  constructor spacy369CriticalRelationalAuditBoundary
  field
    sameParser369ObjectMayCarryMultipleAuditLenses : Bool
    sameParser369ObjectMayCarryMultipleAuditLensesIsTrue :
      sameParser369ObjectMayCarryMultipleAuditLenses ≡ true
    philosophicalAuditIsAlternativeParserSemantics : Bool
    philosophicalAuditIsAlternativeParserSemanticsIsFalse :
      philosophicalAuditIsAlternativeParserSemantics ≡ false
    lacanianAndIrigarayanAuditsShareOneGrammar : Bool
    lacanianAndIrigarayanAuditsShareOneGrammarIsFalse :
      lacanianAndIrigarayanAuditsShareOneGrammar ≡ false
    feministAuditMayDemandAddedSubjectCoordinate : Bool
    feministAuditMayDemandAddedSubjectCoordinateIsTrue :
      feministAuditMayDemandAddedSubjectCoordinate ≡ true
    irigarayanReciprocityDeterminesUniqueOrientation : Bool
    irigarayanReciprocityDeterminesUniqueOrientationIsFalse :
      irigarayanReciprocityDeterminesUniqueOrientation ≡ false
    zizekClosureAuditProvesInstitutionalCause : Bool
    zizekClosureAuditProvesInstitutionalCauseIsFalse :
      zizekClosureAuditProvesInstitutionalCause ≡ false

canonicalSpacy369CriticalRelationalAuditBoundary :
  Spacy369CriticalRelationalAuditBoundary
canonicalSpacy369CriticalRelationalAuditBoundary =
  spacy369CriticalRelationalAuditBoundary
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
