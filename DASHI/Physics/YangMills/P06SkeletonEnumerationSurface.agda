module DASHI.Physics.YangMills.P06SkeletonEnumerationSurface where

------------------------------------------------------------------------
-- P06 skeleton enumeration: the exact remaining finite semantic surface.
--
-- This is additive.  It does not decide Connected and it does not recover
-- witnesses from a dependent Dec-filter.  A caller supplies the finite list
-- of witness-carrying candidates and the one abstract count agreement.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List; length)
open import Data.Nat.Base using (ℕ; _∸_)
open import Data.Product using (Σ; _×_)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph; SkeletonCandidate; FiniteBallEnumeration
        ; ExplicitSkeletonCandidateEnumeration
        ; CountSkeletonsSemantics; CandidateFilterWitness
        ; countSkeletons; mapList; NoDuplicates; _∈_; chooseN
        ; explicitSkeletonCandidateEnumerationFromWitnesses
        ; explicitSkeletonCandidateEnumerationToCandidateFilterWitness
        ; explicitSkeletonCandidateEnumerationToCountSkeletonsSemantics
        )

------------------------------------------------------------------------
-- Exact additive boundary for the remaining skeleton-side assumptions.
------------------------------------------------------------------------

record P06SkeletonEnumerationSurface
  (G : Graph) (r : Graph.Vertex G) (n : ℕ)
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) : Set₁ where
  field
    candidates : List (SkeletonCandidate G r n FBE)

    complete :
      ∀ {ys}
      → ys ∈ chooseN (FiniteBallEnumeration.ballList FBE) n
      → r ∈ ys
      → GC.Connected G ys
      → Σ (SkeletonCandidate G r n FBE) λ c →
          c ∈ candidates ×
          SkeletonCandidate.candVertices c ≡ ys

    uniqueVertexLists :
      NoDuplicates
        (mapList SkeletonCandidate.candVertices candidates)

    countAgrees :
      countSkeletons G r n ≡ length candidates

------------------------------------------------------------------------
-- Constructive projections into the existing canonical surfaces.
------------------------------------------------------------------------

toExplicitSkeletonCandidateEnumeration :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  P06SkeletonEnumerationSurface G r n FBE →
  ExplicitSkeletonCandidateEnumeration G r n FBE
toExplicitSkeletonCandidateEnumeration surface =
  explicitSkeletonCandidateEnumerationFromWitnesses
    (P06SkeletonEnumerationSurface.candidates surface)
    (P06SkeletonEnumerationSurface.complete surface)
    (P06SkeletonEnumerationSurface.uniqueVertexLists surface)
    (P06SkeletonEnumerationSurface.countAgrees surface)

toCandidateFilterWitness :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  P06SkeletonEnumerationSurface G r n FBE →
  CandidateFilterWitness G r n FBE
toCandidateFilterWitness surface =
  explicitSkeletonCandidateEnumerationToCandidateFilterWitness
    (toExplicitSkeletonCandidateEnumeration surface)

toCountSkeletonsSemantics :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  P06SkeletonEnumerationSurface G r n FBE →
  CountSkeletonsSemantics G r n FBE
toCountSkeletonsSemantics surface =
  explicitSkeletonCandidateEnumerationToCountSkeletonsSemantics
    (toExplicitSkeletonCandidateEnumeration surface)

------------------------------------------------------------------------
-- Named projections keep the active assumptions auditable at call sites.
------------------------------------------------------------------------

candidateList :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  P06SkeletonEnumerationSurface G r n FBE →
  List (SkeletonCandidate G r n FBE)
candidateList = P06SkeletonEnumerationSurface.candidates

candidateCountAgreement :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (surface : P06SkeletonEnumerationSurface G r n FBE) →
  countSkeletons G r n ≡ length (candidateList surface)
candidateCountAgreement = P06SkeletonEnumerationSurface.countAgrees

candidateListComplete :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (surface : P06SkeletonEnumerationSurface G r n FBE) →
  ∀ {ys}
  → ys ∈ chooseN (FiniteBallEnumeration.ballList FBE) n
  → r ∈ ys
  → GC.Connected G ys
  → Σ (SkeletonCandidate G r n FBE) λ c →
      c ∈ candidateList surface ×
      SkeletonCandidate.candVertices c ≡ ys
candidateListComplete = P06SkeletonEnumerationSurface.complete

------------------------------------------------------------------------
-- Direct conversion from an existing explicit enumeration is definitionally
-- transparent and introduces no new assumption.
------------------------------------------------------------------------

surfaceFromExplicitEnumeration :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  ExplicitSkeletonCandidateEnumeration G r n FBE →
  P06SkeletonEnumerationSurface G r n FBE
surfaceFromExplicitEnumeration enumeration = record
  { candidates = ExplicitSkeletonCandidateEnumeration.candidates enumeration
  ; complete = ExplicitSkeletonCandidateEnumeration.complete enumeration
  ; uniqueVertexLists =
      ExplicitSkeletonCandidateEnumeration.uniqueVertexLists enumeration
  ; countAgrees = ExplicitSkeletonCandidateEnumeration.countAgrees enumeration
  }
