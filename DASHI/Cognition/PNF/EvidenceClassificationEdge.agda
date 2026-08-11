module DASHI.Cognition.PNF.EvidenceClassificationEdge where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.NumericAuthority
import DASHI.Cognition.PNF.ProofRelevantIdentityFibres as Identity
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection

------------------------------------------------------------------------
-- Classification/reference edges are proposition-local dependencies, not
-- rewrites of the subject's identity.  The existing TypedDependencyCore keeps
-- source, target, relation, provenance and scope attached to the exact edge.
------------------------------------------------------------------------

record CandidateClassificationRelation
    (subject : ObjectId)
    (candidate : Identity.CanonicalEntity) : Set where
  constructor candidateClassificationRelation
  field
    evidenceFactor : FactorId
    phaseDirection : Selection.InteractionDirection
    phaseMagnitude : Nat

open CandidateClassificationRelation public

CandidateClassificationEdge : Set
CandidateClassificationEdge =
  Dependency.DependencyWitness CandidateClassificationRelation

candidateClassificationEdge :
  (subject : ObjectId) →
  (candidate : Identity.CanonicalEntity) →
  FactorId → Selection.InteractionDirection → Nat →
  String → String →
  CandidateClassificationEdge
candidateClassificationEdge subject candidate factor direction magnitude provenance scope =
  Dependency.dependencyWitness
    subject
    candidate
    (candidateClassificationRelation factor direction magnitude)
    Dependency.epistemicLayer
    Dependency.optionalDependency
    provenance
    scope

------------------------------------------------------------------------
-- Candidate classification remains below identity authority.  Deductive local
-- identity is represented by the existing IdentityFibreMember instead of a
-- second competing identity edge type.
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

open ClassificationEdgeBoundary public

canonicalClassificationEdgeBoundary : ClassificationEdgeBoundary
canonicalClassificationEdgeBoundary =
  classificationEdgeBoundary
    candidateClassificationCannotPromoteIdentity
    DeductiveIdentityEdge
