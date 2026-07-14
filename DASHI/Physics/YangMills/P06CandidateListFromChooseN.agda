module DASHI.Physics.YangMills.P06CandidateListFromChooseN where

------------------------------------------------------------------------
-- P06: the constructive part of the finite candidate-list boundary.
--
-- `Connected` has no decision procedure in the current graph surface.  We
-- therefore do not pretend that a Dec-filter is a constructive enumeration.
-- This module proves all facts that follow from a chooseN witness and gives
-- an explicit witness-list interface for the remaining finite-list facts.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; length)
open import Data.Nat.Base using (ℕ; _∸_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph
        ; SkeletonCandidate
        ; FiniteBallEnumeration
        ; CanonicalSkeletonObject
        ; ExplicitSkeletonCandidateEnumeration
        ; CandidateFilterWitness
        ; CountSkeletonsSemantics
        ; Connected
        ; RootedConnectedSkeleton
        ; NoDuplicates
        ; Sorted
        ; _∈_
        ; _⊆_
        ; chooseN
        ; chooseNSoundLength
        ; chooseNSoundNoDup
        ; chooseNSoundSorted
        ; chooseNSoundSubset
        ; canonicalSkeletonVerticesAppearInBallChooseN
        ; candidateToCanonicalSkeletonObject
        ; mapList
        ; countSkeletons
        ; explicitSkeletonCandidateEnumerationFromWitnesses
        ; explicitSkeletonCandidateEnumerationToCandidateFilterWitness
        ; explicitSkeletonCandidateEnumerationToCountSkeletonsSemantics
        ; canonicalSkeletonCandidatesFromBall
        )

------------------------------------------------------------------------
-- A candidate is constructively available as soon as the semantic chosen
-- set carries the three witnesses required by SkeletonCandidate.
------------------------------------------------------------------------

candidateFromChooseNWitnesses :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)}
  {ys : List (Graph.Vertex G)} →
  ys ∈ chooseN (FiniteBallEnumeration.ballList FBE) n →
  r ∈ ys →
  Connected G ys →
  SkeletonCandidate G r n FBE
candidateFromChooseNWitnesses {FBE = FBE} ys∈ r∈ connected = record
  { candVertices = _
  ; inChooseN = ys∈
  ; rootIn = r∈
  ; connected = connected
  }

candidateVerticesFromChooseN :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)}
  {ys : List (Graph.Vertex G)}
  (ys∈ : ys ∈ chooseN (FiniteBallEnumeration.ballList FBE) n) →
  (r∈ : r ∈ ys) →
  (connected : Connected G ys) →
  SkeletonCandidate.candVertices
    (candidateFromChooseNWitnesses {n = n} {FBE = FBE} {ys = ys} ys∈ r∈ connected) ≡ ys
candidateVerticesFromChooseN ys∈ r∈ connected = refl

------------------------------------------------------------------------
-- Candidate-level consequences.  These are independent of any enumeration
-- list and are the reusable soundness facts for later callers.
------------------------------------------------------------------------

candidateChooseNSound :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (c : SkeletonCandidate G r n FBE) →
  SkeletonCandidate.candVertices c ∈
    chooseN (FiniteBallEnumeration.ballList FBE) n
candidateChooseNSound c = SkeletonCandidate.inChooseN c

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
candidateSorted {G} {FBE = FBE} c =
  chooseNSoundSorted
    {G = G}
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

candidateToCanonical :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (c : SkeletonCandidate G r n FBE) →
  CanonicalSkeletonObject G r n
candidateToCanonical {FBE = FBE} c =
  candidateToCanonicalSkeletonObject
    FBE
    (SkeletonCandidate.inChooseN c)
    (SkeletonCandidate.rootIn c)
    (SkeletonCandidate.connected c)

------------------------------------------------------------------------
-- Every canonical object has a candidate witness.  The missing step for a
-- concrete list is only proving that this witness occurs in that list.
------------------------------------------------------------------------

candidateWitnessForCanonicalObject :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) →
  (obj : CanonicalSkeletonObject G r n) →
  Σ (SkeletonCandidate G r n FBE) λ c →
    SkeletonCandidate.candVertices c
      ≡ CanonicalSkeletonObject.skelVertices obj
candidateWitnessForCanonicalObject {n = n} FBE obj =
  let ys∈ = canonicalSkeletonVerticesAppearInBallChooseN FBE obj
      root∈ = RootedConnectedSkeleton.r-in-X
        (CanonicalSkeletonObject.connected obj)
      conn = RootedConnectedSkeleton.connected
        (CanonicalSkeletonObject.connected obj)
      c = candidateFromChooseNWitnesses
        {n = n} {FBE = FBE} {ys = CanonicalSkeletonObject.skelVertices obj}
        ys∈ root∈ conn
  in c , refl

------------------------------------------------------------------------
-- Honest finite-list interface.  The list itself is explicit data; the
-- interface does not smuggle in a Connected decision procedure.
------------------------------------------------------------------------

record P06CandidateListFromChooseN
  (G : Graph) (r : Graph.Vertex G) (n : ℕ)
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) : Set₁ where
  field
    candidates : List (SkeletonCandidate G r n FBE)

    complete :
      ∀ {ys}
      → ys ∈ chooseN (FiniteBallEnumeration.ballList FBE) n
      → r ∈ ys
      → Connected G ys
      → Σ (SkeletonCandidate G r n FBE) λ c →
          c ∈ candidates ×
          SkeletonCandidate.candVertices c ≡ ys

    uniqueVertexLists :
      NoDuplicates (mapList SkeletonCandidate.candVertices candidates)

    countAgrees :
      countSkeletons G r n ≡ length candidates

candidateListSound :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  (surface : P06CandidateListFromChooseN G r n FBE) →
  ∀ (c : SkeletonCandidate G r n FBE) →
  c ∈ P06CandidateListFromChooseN.candidates surface →
  SkeletonCandidate.candVertices c ∈
    chooseN (FiniteBallEnumeration.ballList FBE) n
candidateListSound surface c _ = SkeletonCandidate.inChooseN c

------------------------------------------------------------------------
-- No new assumption is introduced by converting this interface to the
-- already-existing normalized surfaces.
------------------------------------------------------------------------

toExplicitEnumeration :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  P06CandidateListFromChooseN G r n FBE →
  ExplicitSkeletonCandidateEnumeration G r n FBE
toExplicitEnumeration surface =
  explicitSkeletonCandidateEnumerationFromWitnesses
    (P06CandidateListFromChooseN.candidates surface)
    (P06CandidateListFromChooseN.complete surface)
    (P06CandidateListFromChooseN.uniqueVertexLists surface)
    (P06CandidateListFromChooseN.countAgrees surface)

toCandidateFilterWitness :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  P06CandidateListFromChooseN G r n FBE →
  CandidateFilterWitness G r n FBE
toCandidateFilterWitness surface =
  explicitSkeletonCandidateEnumerationToCandidateFilterWitness
    (toExplicitEnumeration surface)

toCountSkeletonsSemantics :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {FBE : FiniteBallEnumeration G r (n ∸ 1)} →
  P06CandidateListFromChooseN G r n FBE →
  CountSkeletonsSemantics G r n FBE
toCountSkeletonsSemantics surface =
  explicitSkeletonCandidateEnumerationToCountSkeletonsSemantics
    (toExplicitEnumeration surface)

------------------------------------------------------------------------
-- A decidable-connectedness lane can use the existing dependent filter.
-- This exports its constructive per-element soundness without claiming the
-- still-open list completeness/no-duplicates/count theorem.
------------------------------------------------------------------------

decidableCandidateList :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  (FBE : FiniteBallEnumeration G r (n ∸ 1)) →
  ((ys : List (Graph.Vertex G)) → Dec (Connected G ys)) →
  List (SkeletonCandidate G r n FBE)
decidableCandidateList = canonicalSkeletonCandidatesFromBall

decidableCandidateListSound :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  (FBE : FiniteBallEnumeration G r (n ∸ 1))
  (connectedDecider : (ys : List (Graph.Vertex G)) → Dec (Connected G ys)) →
  ∀ (c : SkeletonCandidate G r n FBE) →
  c ∈ decidableCandidateList FBE connectedDecider →
  SkeletonCandidate.candVertices c ∈
    chooseN (FiniteBallEnumeration.ballList FBE) n
decidableCandidateListSound FBE connectedDecider c _ =
  SkeletonCandidate.inChooseN c
