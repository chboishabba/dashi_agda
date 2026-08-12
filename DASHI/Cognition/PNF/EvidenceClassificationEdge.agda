module DASHI.Cognition.PNF.EvidenceClassificationEdge where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.NumericAuthority
import DASHI.Cognition.PNF.ProofRelevantIdentityFibres as Identity
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection

------------------------------------------------------------------------
-- Classification/reference edges are proposition-local dependencies, not
-- rewrites of the subject's identity.  They carry evidence, revision,
-- provenance and scope so a later interpretation can supersede the edge while
-- the source occurrence remains stable.
------------------------------------------------------------------------

record CandidateClassificationRelation
    (subject : ObjectId)
    (candidate : Identity.CanonicalEntity) : Set where
  constructor candidateClassificationRelation
  field
    evidenceFactor : FactorId
    phaseDirection : Selection.InteractionDirection
    phaseMagnitude : Nat
    classificationRevision : Nat

open CandidateClassificationRelation public

CandidateClassificationEdge : Set
CandidateClassificationEdge =
  Dependency.DependencyWitness CandidateClassificationRelation

revisedCandidateClassificationEdge :
  (subject : ObjectId) →
  (candidate : Identity.CanonicalEntity) →
  FactorId → Selection.InteractionDirection → Nat → Nat →
  String → String →
  CandidateClassificationEdge
revisedCandidateClassificationEdge
    subject candidate factor direction magnitude revision provenance scope =
  Dependency.dependencyWitness
    subject
    candidate
    (candidateClassificationRelation factor direction magnitude revision)
    Dependency.epistemicLayer
    Dependency.optionalDependency
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

open ClassificationEdgeBoundary public

canonicalClassificationEdgeBoundary : ClassificationEdgeBoundary
canonicalClassificationEdgeBoundary =
  classificationEdgeBoundary
    candidateClassificationCannotPromoteIdentity
    DeductiveIdentityEdge
    Nat
