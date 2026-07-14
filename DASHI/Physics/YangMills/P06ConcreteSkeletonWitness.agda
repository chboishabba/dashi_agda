module DASHI.Physics.YangMills.P06ConcreteSkeletonWitness where

------------------------------------------------------------------------
-- P06 skeleton-side concrete witness package.
--
-- This module is additive.  It does not decide Connected and it does not
-- manufacture membership in an arbitrary candidate list.  The latter two
-- facts are the genuine finite-enumeration boundary.  What is constructive
-- here is everything attached to an individual candidate: chooseN soundness
-- supplies its size, no-duplicate, sortedness, and finite-ball membership.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; length)
open import Data.Nat.Base using (ℕ; _∸_)
open import Data.Product using (Σ; _×_)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph
        ; SkeletonCandidate
        ; FiniteBallEnumeration
        ; ExplicitSkeletonCandidateEnumeration
        ; CandidateFilterWitness
        ; CountSkeletonsSemantics
        ; CanonicalSkeletonObject
        ; Connected
        ; NoDuplicates
        ; Sorted
        ; _∈_
        ; _⊆_
        ; chooseN
        ; chooseNSoundLength
        ; chooseNSoundNoDup
        ; chooseNSoundSorted
        ; chooseNSoundSubset
        ; mapList
        ; countSkeletons
        ; candidateToCanonicalSkeletonObject
        ; explicitSkeletonCandidateEnumerationFromWitnesses
        ; explicitSkeletonCandidateEnumerationToCandidateFilterWitness
        ; explicitSkeletonCandidateEnumerationToCountSkeletonsSemantics
        )

open import DASHI.Physics.YangMills.P06SkeletonEnumerationSurface as Surface
  using ( P06SkeletonEnumerationSurface
        ; toExplicitSkeletonCandidateEnumeration
        ; toCandidateFilterWitness
        ; toCountSkeletonsSemantics
        )

------------------------------------------------------------------------
-- The exact additive witness boundary.
------------------------------------------------------------------------

record P06ConcreteSkeletonWitness
  (G : Graph) (r : Graph.Vertex G) (n : ℕ)
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) : Set₁ where
  field
    candidates : List (SkeletonCandidate G r n FBE)

    -- The only candidate-list coverage claim.  It is intentionally stated
    -- over the semantic chooseN/root/Connected universe, not over a Dec
    -- implementation detail.
    complete :
      ∀ {ys}
      → ys ∈ chooseN (FiniteBallEnumeration.ballList FBE) n
      → r ∈ ys
      → Connected G ys
      → Σ (SkeletonCandidate G r n FBE) λ c →
          c ∈ candidates ×
          SkeletonCandidate.candVertices c ≡ ys

    -- Extensional uniqueness is exactly what downstream canonical indexing
    -- needs; proof-heavy candidate records are not compared propositionally.
    uniqueVertexLists :
      NoDuplicates (mapList SkeletonCandidate.candVertices candidates)

    -- This is the sole abstract numerical meaning of countSkeletons on this
    -- surface.
    countAgrees : countSkeletons G r n ≡ length candidates

------------------------------------------------------------------------
-- Constructive candidate-level projections.
------------------------------------------------------------------------

candidateSound :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (c : SkeletonCandidate G r n FBE) →
  SkeletonCandidate.candVertices c ∈
    chooseN (FiniteBallEnumeration.ballList FBE) n
candidateSound c = SkeletonCandidate.inChooseN c

candidateLength :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (c : SkeletonCandidate G r n FBE) →
  length (SkeletonCandidate.candVertices c) ≡ n
candidateLength {n = n} {FBE = FBE} c =
  chooseNSoundLength
    {xs = FiniteBallEnumeration.ballList FBE}
    {ys = SkeletonCandidate.candVertices c}
    {n = n}
    (SkeletonCandidate.inChooseN c)

candidateNoDuplicates :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (c : SkeletonCandidate G r n FBE) →
  NoDuplicates (SkeletonCandidate.candVertices c)
candidateNoDuplicates {n = n} {FBE = FBE} c =
  chooseNSoundNoDup
    {xs = FiniteBallEnumeration.ballList FBE}
    {ys = SkeletonCandidate.candVertices c}
    {n = n}
    (FiniteBallEnumeration.ballNoDup FBE)
    (SkeletonCandidate.inChooseN c)

candidateSorted :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (c : SkeletonCandidate G r n FBE) →
  Sorted (GC.vertexOrder {G}) (SkeletonCandidate.candVertices c)
candidateSorted {n = n} {FBE = FBE} c =
  chooseNSoundSorted
    {xs = FiniteBallEnumeration.ballList FBE}
    {ys = SkeletonCandidate.candVertices c}
    {n = n}
    (FiniteBallEnumeration.ballSorted FBE)
    (SkeletonCandidate.inChooseN c)

candidateInsideBall :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (c : SkeletonCandidate G r n FBE) →
  SkeletonCandidate.candVertices c ⊆
    FiniteBallEnumeration.ballList FBE
candidateInsideBall c =
  chooseNSoundSubset (SkeletonCandidate.inChooseN c)

candidateToCanonicalObject :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (c : SkeletonCandidate G r n FBE) →
  CanonicalSkeletonObject G r n
candidateToCanonicalObject {FBE = FBE} c =
  candidateToCanonicalSkeletonObject
    FBE
    (SkeletonCandidate.inChooseN c)
    (SkeletonCandidate.rootIn c)
    (SkeletonCandidate.connected c)

candidateObjectVertices :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (c : SkeletonCandidate G r n FBE) →
  GC.CanonicalSkeletonObject.skelVertices
    (candidateToCanonicalObject c) ≡
    SkeletonCandidate.candVertices c
candidateObjectVertices c = refl

------------------------------------------------------------------------
-- Projections into the existing normalized surfaces.
------------------------------------------------------------------------

toSurface :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  P06ConcreteSkeletonWitness G r n FBE →
  P06SkeletonEnumerationSurface G r n FBE
toSurface witness = record
  { candidates = P06ConcreteSkeletonWitness.candidates witness
  ; complete = P06ConcreteSkeletonWitness.complete witness
  ; uniqueVertexLists = P06ConcreteSkeletonWitness.uniqueVertexLists witness
  ; countAgrees = P06ConcreteSkeletonWitness.countAgrees witness
  }

toExplicitEnumeration :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  P06ConcreteSkeletonWitness G r n FBE →
  ExplicitSkeletonCandidateEnumeration G r n FBE
toExplicitEnumeration witness =
  toExplicitSkeletonCandidateEnumeration (toSurface witness)

toCandidateFilter :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  P06ConcreteSkeletonWitness G r n FBE →
  CandidateFilterWitness G r n FBE
toCandidateFilter witness = toCandidateFilterWitness (toSurface witness)

toCountSemantics :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  P06ConcreteSkeletonWitness G r n FBE →
  CountSkeletonsSemantics G r n FBE
toCountSemantics witness = Surface.toCountSkeletonsSemantics (toSurface witness)

------------------------------------------------------------------------
-- Direct constructor from the three honest finite-list obligations.
------------------------------------------------------------------------

fromExplicitList :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (candidates : List (SkeletonCandidate G r n FBE)) →
  (∀ {ys}
   → ys ∈ chooseN (FiniteBallEnumeration.ballList FBE) n
   → r ∈ ys
   → Connected G ys
   → Σ (SkeletonCandidate G r n FBE) λ c →
       c ∈ candidates ×
       SkeletonCandidate.candVertices c ≡ ys) →
  NoDuplicates (mapList SkeletonCandidate.candVertices candidates) →
  countSkeletons G r n ≡ length candidates →
  P06ConcreteSkeletonWitness G r n FBE
fromExplicitList candidates complete unique count = record
  { candidates = candidates
  ; complete = complete
  ; uniqueVertexLists = unique
  ; countAgrees = count
  }

------------------------------------------------------------------------
-- The existing explicit constructor is a definitionally transparent
-- projection of the same package; keeping it named here makes the boundary
-- easy to audit without changing legacy consumers.
------------------------------------------------------------------------

toExplicitEnumerationDirect :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  P06ConcreteSkeletonWitness G r n FBE →
  ExplicitSkeletonCandidateEnumeration G r n FBE
toExplicitEnumerationDirect witness =
  explicitSkeletonCandidateEnumerationFromWitnesses
    (P06ConcreteSkeletonWitness.candidates witness)
    (P06ConcreteSkeletonWitness.complete witness)
    (P06ConcreteSkeletonWitness.uniqueVertexLists witness)
    (P06ConcreteSkeletonWitness.countAgrees witness)

------------------------------------------------------------------------
-- Constructive-status boundary:
--
-- * candidateLength/candidateNoDuplicates/candidateSorted/candidateInsideBall
--   are proved from the current chooseN/FBE APIs.
-- * complete is not derivable from an arbitrary list: chooseN completeness
--   constructs a candidate value, but does not prove that value occurs in the
--   caller-supplied list.
-- * uniqueVertexLists is not derivable from arbitrary candidate membership;
--   it is the list-level canonicality obligation supplied here.
-- * countAgrees is the sole remaining abstract countSkeletons bridge.
------------------------------------------------------------------------
