module DASHI.Cognition.PNF.EvidenceClassificationEdge where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.NumericAuthority
import DASHI.Cognition.PNF.ProofRelevantIdentityFibres as Identity
import DASHI.Core.ClassificationEdge as Core
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection

------------------------------------------------------------------------
-- Entity-candidate classification is an instance of the canonical revisable
-- classification edge. The subject occurrence remains stable when an edge is
-- revised or superseded.
------------------------------------------------------------------------

record CandidateClassificationEvidence : Set where
  constructor candidateClassificationEvidence
  field
    factorEvidence : FactorId
    candidatePhaseDirection : Selection.InteractionDirection
    candidatePhaseMagnitude : Nat

open CandidateClassificationEvidence public

CandidateClassificationRelation :
  ObjectId → Identity.CanonicalEntity → Set
CandidateClassificationRelation subject candidate =
  Core.ClassificationRelation
    {Subject = ObjectId}
    {Target = Identity.CanonicalEntity}
    {Evidence = CandidateClassificationEvidence}
    subject candidate

candidateClassificationRelation :
  ∀ {subject candidate} →
  FactorId → Selection.InteractionDirection → Nat → Nat →
  CandidateClassificationRelation subject candidate
candidateClassificationRelation factor direction magnitude revision =
  Core.classificationRelation
    (candidateClassificationEvidence factor direction magnitude)
    revision

evidenceFactor :
  ∀ {subject candidate} →
  CandidateClassificationRelation subject candidate → FactorId
evidenceFactor relation = factorEvidence (Core.classificationEvidence relation)

phaseDirection :
  ∀ {subject candidate} →
  CandidateClassificationRelation subject candidate →
  Selection.InteractionDirection
phaseDirection relation =
  candidatePhaseDirection (Core.classificationEvidence relation)

phaseMagnitude :
  ∀ {subject candidate} →
  CandidateClassificationRelation subject candidate → Nat
phaseMagnitude relation =
  candidatePhaseMagnitude (Core.classificationEvidence relation)

classificationRevision :
  ∀ {subject candidate} →
  CandidateClassificationRelation subject candidate → Nat
classificationRevision = Core.classificationRevision

CandidateClassificationEdge : Set
CandidateClassificationEdge =
  Core.ClassificationEdge
    ObjectId
    Identity.CanonicalEntity
    CandidateClassificationEvidence

revisedCandidateClassificationEdge :
  (subject : ObjectId) →
  (candidate : Identity.CanonicalEntity) →
  FactorId → Selection.InteractionDirection → Nat → Nat →
  String → String →
  CandidateClassificationEdge
revisedCandidateClassificationEdge
    subject candidate factor direction magnitude revision provenance scope =
  Core.classificationEdge
    subject
    candidate
    (candidateClassificationEvidence factor direction magnitude)
    revision
    provenance
    scope

candidateClassificationEdge :
  (subject : ObjectId) →
  (candidate : Identity.CanonicalEntity) →
  FactorId → Selection.InteractionDirection → Nat →
  String → String →
  CandidateClassificationEdge
candidateClassificationEdge subject candidate factor direction magnitude =
  revisedCandidateClassificationEdge
    subject candidate factor direction magnitude zero

------------------------------------------------------------------------
-- Candidate classification remains below identity authority.
------------------------------------------------------------------------

data CandidateClassificationIdentityPermission : Set where

candidateClassificationCannotPromoteIdentity :
  CandidateClassificationIdentityPermission → ⊥
candidateClassificationCannotPromoteIdentity ()

DeductiveIdentityEdge : Set
DeductiveIdentityEdge = Identity.IdentityFibreMember

record ClassificationEdgeBoundary : Set where
  constructor classificationEdgeBoundary
  field
    candidateEdgeIsNotIdentity :
      CandidateClassificationIdentityPermission → ⊥
    deductiveIdentityReusesExistingFibreMember : Set
    classificationCarriesExplicitRevision : Set
    canonicalClassificationCoreReused : Bool
    canonicalClassificationCoreReusedIsTrue :
      canonicalClassificationCoreReused ≡ true

open ClassificationEdgeBoundary public

canonicalClassificationEdgeBoundary : ClassificationEdgeBoundary
canonicalClassificationEdgeBoundary =
  classificationEdgeBoundary
    candidateClassificationCannotPromoteIdentity
    DeductiveIdentityEdge
    Nat
    true refl
