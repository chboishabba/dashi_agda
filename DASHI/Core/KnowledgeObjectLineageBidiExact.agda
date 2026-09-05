module DASHI.Core.KnowledgeObjectLineageBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- KNOWLEDGE-OBJECT LINEAGE BIDI
--
-- A study, a later report about that study, and privately matured derivative
-- work are different objects unless a source explicitly welds them.
------------------------------------------------------------------------

data KnowledgeObjectKind : Set where
  experimentalStudy
  technicalReport
  derivedPrivateWork
  releaseReviewObject
  publicDerivative
  : KnowledgeObjectKind

record KnowledgeObject : Set where
  constructor knowledge-object
  field
    objectName : String
    kind : KnowledgeObjectKind
    sourceReference : String
    boundedReading : String

open KnowledgeObject public

data LineageRelation : Set where
  reportsResultsOf
  maturesFrom
  dependsOnReleaseOf
  candidateSameObject
  exactSameObject
  : LineageRelation

record KnowledgeObjectLineage : Set where
  constructor knowledge-object-lineage
  field
    earlier : KnowledgeObject
    later : KnowledgeObject
    relation : LineageRelation
    relationReference : String
    boundedReading : String

open KnowledgeObjectLineage public

record ExactIdentityWeld (lineage : KnowledgeObjectLineage) : Set where
  constructor exact-identity-weld
  field
    isExact : relation lineage ≡ exactSameObject
    identityReference : String

open ExactIdentityWeld public

record KnowledgeObjectLineageBoundary : Set where
  constructor knowledge-object-lineage-boundary
  field
    laterReportEqualsEarlierStudy : Bool
    laterReportEqualsEarlierStudyIsFalse : laterReportEqualsEarlierStudy ≡ false
    derivedWorkEqualsSourceStudy : Bool
    derivedWorkEqualsSourceStudyIsFalse : derivedWorkEqualsSourceStudy ≡ false
    releaseDependencyEqualsSameObject : Bool
    releaseDependencyEqualsSameObjectIsFalse : releaseDependencyEqualsSameObject ≡ false
    candidateIdentityEqualsExactIdentity : Bool
    candidateIdentityEqualsExactIdentityIsFalse :
      candidateIdentityEqualsExactIdentity ≡ false

canonicalKnowledgeObjectLineageBoundary : KnowledgeObjectLineageBoundary
canonicalKnowledgeObjectLineageBoundary = knowledge-object-lineage-boundary
  false refl
  false refl
  false refl
  false refl
