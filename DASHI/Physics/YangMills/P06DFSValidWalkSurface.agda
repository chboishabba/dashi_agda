module DASHI.Physics.YangMills.P06DFSValidWalkSurface where

------------------------------------------------------------------------
-- P06: the smallest honest DFS-valid-walk surface.
--
-- `DFSCover.w`/`dfsWalkRange` are coverage data only.  In particular, they
-- do not prove that the range starts at r, has consecutive graph edges, or
-- has the path length required by WalkObject.  This module therefore asks
-- for exactly one additional object: a genuine WalkObject together with its
-- vertex-list equality to the DFS range.  No postulate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph
        ; CanonicalSkeletonEnumeration
        ; CanonicalSkeletonObject
        ; CountWalksMembershipSemantics
        ; DFSCover
        ; BoundedNeighbourEnumeration
        ; WalkObject
        ; walkObjectVertices
        ; dfsWalkRange
        ; canonicalDFSObjectSound
        ; dfsWalkRangeMemberFromWalkObject
        ; generatedWalkVertexLists
        ; generatedWalkVertexListComplete
        ; MembershipIndexedCanonicalWalkObjectList
        ; SameVertexSet
        ; _∈_
        )

open import DASHI.Physics.YangMills.P06ConcreteEnumerationEndpoint
         using (MembershipIndexedDFSMap)

------------------------------------------------------------------------
-- A valid walk witnessing one DFS range.
------------------------------------------------------------------------

record DFSValidWalkWitness
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  (obj : CanonicalSkeletonObject G r n) : Set₁ where
  field
    walk : WalkObject G r (n + n)

    -- The WalkObject carries the actual nonempty/rooted/consecutive/length
    -- evidence through its Path.  This equality identifies its vertex
    -- sequence with the current DFS range; it does not treat DFSCover.w as a
    -- path.
    vertices-is-dfsRange :
      walkObjectVertices walk ≡ dfsWalkRange obj

------------------------------------------------------------------------
-- Constructive consequences of the witness.
------------------------------------------------------------------------

dfsValidWalkWitnessMember
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  → (BNE : BoundedNeighbourEnumeration G Δ)
  → (obj : CanonicalSkeletonObject G r n)
  → DFSValidWalkWitness obj
  → dfsWalkRange obj ∈
      generatedWalkVertexLists {r = r} {L = n + n} BNE
dfsValidWalkWitnessMember BNE obj witness =
  dfsWalkRangeMemberFromWalkObject
    BNE obj
    (DFSValidWalkWitness.walk witness)
    (DFSValidWalkWitness.vertices-is-dfsRange witness)

dfsValidWalkWitnessSound
  : {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  → (obj : CanonicalSkeletonObject G r n)
  → (witness : DFSValidWalkWitness obj)
  → SameVertexSet
      (walkObjectVertices (DFSValidWalkWitness.walk witness))
      (CanonicalSkeletonObject.skelVertices obj)
dfsValidWalkWitnessSound obj witness =
  subst
    (λ xs → SameVertexSet xs
      (CanonicalSkeletonObject.skelVertices obj))
    (sym (DFSValidWalkWitness.vertices-is-dfsRange witness))
    (canonicalDFSObjectSound obj)

------------------------------------------------------------------------
-- Generated-list membership and canonical injectivity.
------------------------------------------------------------------------

dfsValidWalkGeneratedMember
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  → (BNE : BoundedNeighbourEnumeration G Δ)
  → (obj : CanonicalSkeletonObject G r n)
  → (dw : DFSValidWalkWitness obj)
  → walkObjectVertices (DFSValidWalkWitness.walk dw)
      ∈ generatedWalkVertexLists {r = r} {L = n + n} BNE
dfsValidWalkGeneratedMember BNE obj dw
  with generatedWalkVertexListComplete
         BNE
         (DFSValidWalkWitness.walk dw)
... | vs , vs∈ , vs≡ =
  subst
    (λ xs → xs ∈ generatedWalkVertexLists {r = _} {L = _} BNE)
    vs≡
    vs∈

sameVertexSetFromListEquality
  : {A : Set} {xs ys : List A}
  → xs ≡ ys
  → SameVertexSet xs ys
sameVertexSetFromListEquality refl =
  (λ x∈ → x∈) , (λ x∈ → x∈)

sameVertexSetSym
  : {A : Set} {xs ys : List A}
  → SameVertexSet xs ys
  → SameVertexSet ys xs
sameVertexSetSym sv = proj₂ sv , proj₁ sv

sameVertexSetTrans
  : {A : Set} {xs ys zs : List A}
  → SameVertexSet xs ys
  → SameVertexSet ys zs
  → SameVertexSet xs zs
sameVertexSetTrans sv₁ sv₂ =
  (λ x∈ → proj₁ sv₂ (proj₁ sv₁ x∈)) ,
  (λ z∈ → proj₂ sv₁ (proj₂ sv₂ z∈))

dfsWalkVerticesInjective
  : {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  → (CE : CanonicalSkeletonEnumeration G r n)
  → (walkWitness :
      (s : Fin (GC.countSkeletons G r n)) →
      DFSValidWalkWitness
        (CanonicalSkeletonEnumeration.objectOf CE s))
  → ∀ {s₁ s₂}
  → walkObjectVertices
      (DFSValidWalkWitness.walk (walkWitness s₁))
      ≡
    walkObjectVertices
      (DFSValidWalkWitness.walk (walkWitness s₂))
  → s₁ ≡ s₂
dfsWalkVerticesInjective CE walkWitness {s₁} {s₂} walkEq =
  GC.canonicalSameVertexSetImpliesSameIndex CE skelSVS
  where
    walkSVS :
      SameVertexSet
        (walkObjectVertices
          (DFSValidWalkWitness.walk (walkWitness s₁)))
        (walkObjectVertices
          (DFSValidWalkWitness.walk (walkWitness s₂)))
    walkSVS = sameVertexSetFromListEquality walkEq

    sound₁ :
      SameVertexSet
        (walkObjectVertices
          (DFSValidWalkWitness.walk (walkWitness s₁)))
        (CanonicalSkeletonObject.skelVertices
          (CanonicalSkeletonEnumeration.objectOf CE s₁))
    sound₁ = dfsValidWalkWitnessSound _ (walkWitness s₁)

    sound₂ :
      SameVertexSet
        (walkObjectVertices
          (DFSValidWalkWitness.walk (walkWitness s₂)))
        (CanonicalSkeletonObject.skelVertices
          (CanonicalSkeletonEnumeration.objectOf CE s₂))
    sound₂ = dfsValidWalkWitnessSound _ (walkWitness s₂)

    skelSVS :
      SameVertexSet
        (CanonicalSkeletonObject.skelVertices
          (CanonicalSkeletonEnumeration.objectOf CE s₁))
        (CanonicalSkeletonObject.skelVertices
          (CanonicalSkeletonEnumeration.objectOf CE s₂))
    skelSVS =
      sameVertexSetTrans
        (sameVertexSetSym sound₁)
        (sameVertexSetTrans walkSVS sound₂)

------------------------------------------------------------------------
-- Compatibility between a membership-indexed semantic list and the
-- constructive generated list.  For the generated semantic constructor this
-- is normally `refl`; keeping it as a field prevents an accidental claim that
-- arbitrary CountWalksMembershipSemantics uses the generated list.
------------------------------------------------------------------------

record GeneratedWalkSemanticsCompatibility
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {L : ℕ}
  (BNE : BoundedNeighbourEnumeration G Δ)
  (WE : CountWalksMembershipSemantics G r L) : Set₁ where
  field
    walks-is-generated :
      MembershipIndexedCanonicalWalkObjectList.walks WE
        ≡ generatedWalkVertexLists {r = r} {L = L} BNE

generatedMemberToSemanticsMember
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {L : ℕ}
  → {BNE : BoundedNeighbourEnumeration G Δ}
  → {WE : CountWalksMembershipSemantics G r L}
  → GeneratedWalkSemanticsCompatibility BNE WE
  → (w : List (Graph.Vertex G))
  → w ∈ generatedWalkVertexLists {r = r} {L = L} BNE
  → w ∈ MembershipIndexedCanonicalWalkObjectList.walks WE
generatedMemberToSemanticsMember compatibility w member =
  subst
    (λ xs → w ∈ xs)
    (sym (GeneratedWalkSemanticsCompatibility.walks-is-generated compatibility))
    member

------------------------------------------------------------------------
-- A map-level witness.  The only obligations not derivable from a valid
-- WalkObject are semantic-list compatibility and index injectivity.  They
-- remain explicit instead of being smuggled in through DFSCover.
------------------------------------------------------------------------

record DFSValidWalkMapWitness
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  (CE : CanonicalSkeletonEnumeration G r n)
  (BNE : BoundedNeighbourEnumeration G Δ)
  (WE : CountWalksMembershipSemantics G r (n + n)) : Set₁ where
  field
    walkWitness :
      (s : Fin (GC.countSkeletons G r n))
      → DFSValidWalkWitness
          (CanonicalSkeletonEnumeration.objectOf CE s)

    semanticsCompatibility :
      GeneratedWalkSemanticsCompatibility BNE WE

    walkInjective :
      ∀ {s₁ s₂}
      → walkObjectVertices (DFSValidWalkWitness.walk
          (walkWitness s₁))
          ≡
        walkObjectVertices (DFSValidWalkWitness.walk
          (walkWitness s₂))
      → s₁ ≡ s₂

------------------------------------------------------------------------
-- Constructive adapter to the endpoint's MembershipIndexedDFSMap.
------------------------------------------------------------------------

dfsValidWalkMapToMembershipIndexedDFSMap
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  → {CE : CanonicalSkeletonEnumeration G r n}
  → {BNE : BoundedNeighbourEnumeration G Δ}
  → {WE : CountWalksMembershipSemantics G r (n + n)}
  → DFSValidWalkMapWitness CE BNE WE
  → MembershipIndexedDFSMap CE WE
dfsValidWalkMapToMembershipIndexedDFSMap {CE = CE} {BNE = BNE} {WE = WE} witness =
  record
  { dfsWalkOfSkeleton = λ s →
      walkObjectVertices
        (DFSValidWalkWitness.walk
          (DFSValidWalkMapWitness.walkWitness witness s))

  ; dfsWalkMember = λ s →
      subst
        (λ xs → xs ∈ MembershipIndexedCanonicalWalkObjectList.walks WE)
        (sym (DFSValidWalkWitness.vertices-is-dfsRange
          (DFSValidWalkMapWitness.walkWitness witness s)))
        (generatedMemberToSemanticsMember
          (DFSValidWalkMapWitness.semanticsCompatibility witness)
          (dfsWalkRange
            (CanonicalSkeletonEnumeration.objectOf CE s))
          (dfsValidWalkWitnessMember
            BNE
            (CanonicalSkeletonEnumeration.objectOf CE s)
            (DFSValidWalkMapWitness.walkWitness witness s)))

  ; dfsWalkSound = λ s →
      dfsValidWalkWitnessSound
        (CanonicalSkeletonEnumeration.objectOf CE s)
        (DFSValidWalkMapWitness.walkWitness witness s)

  ; dfsWalkInjective =
      DFSValidWalkMapWitness.walkInjective witness
  }

------------------------------------------------------------------------
-- Integrated packaging once the genuine WalkObject construction is owned.
-- The remaining input is deliberately only the per-skeleton valid-walk
-- constructor; membership and injectivity are derived here.
------------------------------------------------------------------------

canonicalSkeletonEnumerationToDFSValidWalkMapWitnessFromWalks
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  → (CE : CanonicalSkeletonEnumeration G r n)
  → (BNE : BoundedNeighbourEnumeration G Δ)
  → (WE : CountWalksMembershipSemantics G r (n + n))
  → GeneratedWalkSemanticsCompatibility BNE WE
  → (walkWitness :
      (s : Fin (GC.countSkeletons G r n)) →
      DFSValidWalkWitness
        (CanonicalSkeletonEnumeration.objectOf CE s))
  → DFSValidWalkMapWitness CE BNE WE
canonicalSkeletonEnumerationToDFSValidWalkMapWitnessFromWalks
  CE BNE WE compat walkWitness =
  record
  { walkWitness = walkWitness
  ; semanticsCompatibility = compat
  ; walkInjective = dfsWalkVerticesInjective CE walkWitness
  }

------------------------------------------------------------------------
-- Direct range-membership adapter, useful before a full semantic WE exists.
------------------------------------------------------------------------

record DFSRangeMembershipWitness
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  (BNE : BoundedNeighbourEnumeration G Δ)
  (obj : CanonicalSkeletonObject G r n) : Set₁ where
  field
    validWalk : DFSValidWalkWitness obj

dfsRangeMembershipWitnessMember
  : {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  → {BNE : BoundedNeighbourEnumeration G Δ}
  → {obj : CanonicalSkeletonObject G r n}
  → DFSRangeMembershipWitness BNE obj
  → dfsWalkRange obj ∈
      generatedWalkVertexLists {r = r} {L = n + n} BNE
dfsRangeMembershipWitnessMember {BNE = BNE} {obj = obj} witness =
  dfsValidWalkWitnessMember
    BNE obj
    (DFSRangeMembershipWitness.validWalk witness)

------------------------------------------------------------------------
-- DFSCover remains an explicitly named coverage input.  No conversion is
-- supplied: its length/coverage fields are insufficient for a WalkObject.
------------------------------------------------------------------------

DFSCoverRange
  : {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} {m : ℕ}
  → DFSCover G r X m
  → List (Graph.Vertex G)
DFSCoverRange = DFSCover.w
