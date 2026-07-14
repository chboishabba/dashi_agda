module DASHI.Physics.YangMills.P06GeneratedWalkUniqueness where

------------------------------------------------------------------------
-- P06: uniqueness of the vertex lists emitted by the recursive generator.
--
-- The proof is deliberately extensional.  Two WalkObjects with the same
-- vertex list need not be propositionally equal, since their Path records
-- contain proof fields.  We therefore prove NoDuplicates after mapping the
-- generator to vertex lists, using the last vertex to separate extensions
-- and the prefix to separate recursive blocks.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
open import DASHI.Physics.YangMills.P06CanonicalNeighbourEnumeration as P06
open GC using (noDup-nil; noDup-cons)
open import DASHI.Core.Prelude using
  ( Nat; List; Σ; _×_; []; _∷_; proj₁; proj₂; _≡_; refl; trans; sym; cong )
open import Data.List using (length; _++_)
open import Data.Nat.Base using (suc; zero)
open import Relation.Binary.PropositionalEquality using (subst)

------------------------------------------------------------------------
-- One extension block is duplicate-free.
------------------------------------------------------------------------

extensionBlockNoDuplicates :
  {G : GC.Graph} {Δ : Nat} {r : GC.Graph.Vertex G} {L : Nat} →
  (BNE : GC.BoundedNeighbourEnumeration G Δ) →
  (w : GC.WalkObject G r L) →
  (nd : GC.NoDuplicates
    (GC.BoundedNeighbourEnumeration.neighbours BNE
      (GC.WalkObject.endpoint w))) →
  GC.NoDuplicates
    (GC.mapList GC.walkObjectVertices (GC.walkObjectExtend BNE w))
extensionBlockNoDuplicates {G} BNE w nd =
  go (GC.BoundedNeighbourEnumeration.neighbours BNE
        (GC.WalkObject.endpoint w))
    (λ {z} z∈ → GC.BoundedNeighbourEnumeration.neighbourSound BNE z∈)
    nd
  where
  go :
    (xs : List (GC.Graph.Vertex G)) →
    (sound : ∀ {z} → z ∈ xs →
      GC.Graph.Adj G (GC.WalkObject.endpoint w) z) →
    GC.NoDuplicates xs →
    GC.NoDuplicates
      (GC.mapList GC.walkObjectVertices
        (GC.mapListWithMembership xs (λ z z∈ → record
          { endpoint = z
          ; path = GC.snocPath
              (GC.WalkObject.path w)
              (sound z∈)
          ; length-is =
              trans
                (GC.pathLength-snoc
                  (GC.WalkObject.path w)
                  (sound z∈))
                (cong suc (GC.WalkObject.length-is w))
          })))
  go [] sound noDup-nil = GC.noDup-nil
  go (z ∷ zs) sound (noDup-cons z∉zs nd-zs) =
    GC.noDup-cons
      (λ y∈ →
        let
          y-data = GC.map-elem GC.walkObjectVertices
            (GC.mapListWithMembership zs (λ z z∈ → record
              { endpoint = z
              ; path = GC.snocPath (GC.WalkObject.path w) (sound (there z∈))
              ; length-is =
                  trans (GC.pathLength-snoc (GC.WalkObject.path w) (sound (there z∈)))
                    (cong suc (GC.WalkObject.length-is w))
              })) y∈
          w′ = proj₁ y-data
          y′ = proj₁ (proj₂ y-data)
          w′∈ = proj₂ (proj₂ y-data)
          z-data = GC.mapListWithMembership-elem
            zs
            (λ z z∈ → record
              { endpoint = z
              ; path = GC.snocPath (GC.WalkObject.path w) (sound (there z∈))
              ; length-is =
                  trans (GC.pathLength-snoc (GC.WalkObject.path w) (sound (there z∈)))
                    (cong suc (GC.WalkObject.length-is w))
              }) w′∈
          z′ = proj₁ z-data
          w-z′∈ = proj₁ (proj₂ z-data)
          object-eq = proj₂ (proj₂ z-data)
          tail-eq = trans (cong GC.walkObjectVertices object-eq) refl
          z-eq = GC.append-singleton-last-injective
            (trans y′ tail-eq)
        in z∉zs (subst (λ q → q ∈ zs) (sym z-eq) w-z′∈))
      (go zs (λ {z} z∈ → sound (there z∈)) nd-zs)

mapList-++ :
  {A B : Set} (f : A → B) (xs ys : List A) →
  GC.mapList f (xs ++ ys) ≡ GC.mapList f xs ++ GC.mapList f ys
mapList-++ f [] ys = refl
mapList-++ f (x ∷ xs) ys = cong (λ zs → f x ∷ zs) (mapList-++ f xs ys)

mapList-concatMap-cons :
  {A B C : Set} (f : B → C) (g : A → List B)
  (x : A) (xs : List A) →
  GC.mapList f (GC.concatMapList g (x ∷ xs))
    ≡ GC.mapList f (g x) ++ GC.mapList f (GC.concatMapList g xs)
mapList-concatMap-cons f g x xs =
  mapList-++ f (g x) (GC.concatMapList g xs)

------------------------------------------------------------------------
-- Recursive block uniqueness.  The local induction is on the list of
-- prefix objects; its invariant is NoDuplicates of their vertex lists.
------------------------------------------------------------------------

generatedBlocksNoDuplicates :
  {G : GC.Graph} {Δ : Nat} {r : GC.Graph.Vertex G} {L : Nat} →
  (BNE : GC.BoundedNeighbourEnumeration G Δ) →
  (ws : List (GC.WalkObject G r L)) →
  GC.NoDuplicates (GC.mapList GC.walkObjectVertices ws) →
  (∀ (w : GC.WalkObject G r L) → GC.NoDuplicates
    (GC.BoundedNeighbourEnumeration.neighbours BNE
      (GC.WalkObject.endpoint w))) →
  GC.NoDuplicates
    (GC.mapList GC.walkObjectVertices
      (GC.concatMapList (GC.walkObjectExtend BNE) ws))
generatedBlocksNoDuplicates {G} {Δ} {r} {L} BNE [] noDup-nil nd = GC.noDup-nil
generatedBlocksNoDuplicates {G} {Δ} {r} {L} BNE (w ∷ ws)
  (noDup-cons w∉ws nd-ws) nd =
  subst GC.NoDuplicates
    (sym (mapList-concatMap-cons GC.walkObjectVertices
      (GC.walkObjectExtend BNE) w ws))
    (GC.++-noDup
      (GC.mapList GC.walkObjectVertices (GC.walkObjectExtend BNE w))
      (GC.mapList GC.walkObjectVertices
        (GC.concatMapList (GC.walkObjectExtend BNE) ws))
      (extensionBlockNoDuplicates {G = G} {Δ = Δ} {r = r} {L = L}
        BNE w (nd w))
      (generatedBlocksNoDuplicates {G = G} {Δ = Δ} {r = r} {L = L}
        BNE ws nd-ws nd)
      (λ {x} x∈block →
      λ x∈tail →
        let
          x-data = GC.map-elem GC.walkObjectVertices
            (GC.walkObjectExtend BNE w) x∈block
          w′ = proj₁ x-data
          x-eq = proj₁ (proj₂ x-data)
          w′∈ = proj₂ (proj₂ x-data)
          tail-vertex-data = GC.map-elem GC.walkObjectVertices
            (GC.concatMapList (GC.walkObjectExtend BNE) ws) x∈tail
          x-tail-eq = proj₁ (proj₂ tail-vertex-data)
          x-tail∈ = proj₂ (proj₂ tail-vertex-data)
          tail-data = GC.concatMap-elem
            (GC.walkObjectExtend BNE) ws x-tail∈
          u = proj₁ tail-data
          u∈ = proj₁ (proj₂ tail-data)
          u-ext∈ = proj₂ (proj₂ tail-data)
          u-data = GC.walkObjectExtendMemberByVertices BNE u u-ext∈
          z = proj₁ u-data
          u-z∈ = proj₁ (proj₂ u-data)
          u′-eq = proj₂ (proj₂ u-data)
          w-data = GC.walkObjectExtendMemberByVertices BNE w w′∈
          z′ = proj₁ w-data
          w-z′∈ = proj₁ (proj₂ w-data)
          w′-eq = proj₂ (proj₂ w-data)
          prefix-eq = GC.append-singleton-prefix-injective
            (trans (sym w′-eq)
              (trans (sym x-eq) (trans x-tail-eq u′-eq)))
        in w∉ws
          (subst (λ q → q ∈ GC.mapList GC.walkObjectVertices ws)
            (sym prefix-eq)
            (GC.in-map GC.walkObjectVertices {x = u} {xs = ws} u∈))))

------------------------------------------------------------------------
-- Public theorem for the canonicalized BNE adapter.
------------------------------------------------------------------------

generatedWalkVertexListsNoDuplicates :
  {G : GC.Graph} {Δ : Nat} {r : GC.Graph.Vertex G} {L : Nat} →
  (E : P06.P06CanonicalBoundedNeighbourEnumeration G Δ) →
  GC.NoDuplicates
    (GC.generatedWalkVertexLists {r = r} {L = L}
      (GC.CanonicalBoundedNeighbourEnumeration.bounded
        (P06.toGraphCanonicalBoundedNeighbourEnumeration E)))
generatedWalkVertexListsNoDuplicates {G} {Δ} {r} {L = zero} E =
  GC.noDup-cons (λ ()) GC.noDup-nil
generatedWalkVertexListsNoDuplicates {G} {Δ} {r} {L = suc k} E =
  generatedBlocksNoDuplicates
    {G = G} {Δ = Δ} {r = r} {L = k}
    A
    (GC.walkObjectsFromNeighbourCodes A r k)
    (generatedWalkVertexListsNoDuplicates′ k)
    (λ (w : GC.WalkObject G r k) → GC.CanonicalBoundedNeighbourEnumeration.neighboursNoDuplicates
      (P06.toGraphCanonicalBoundedNeighbourEnumeration E)
      (GC.WalkObject.endpoint w))
  where
  A : GC.BoundedNeighbourEnumeration G Δ
  A = GC.CanonicalBoundedNeighbourEnumeration.bounded
    (P06.toGraphCanonicalBoundedNeighbourEnumeration E)

  generatedWalkVertexListsNoDuplicates′ :
    (k : Nat) →
    GC.NoDuplicates
      (GC.mapList GC.walkObjectVertices
        (GC.walkObjectsFromNeighbourCodes
          A r k))
  generatedWalkVertexListsNoDuplicates′ zero =
    GC.noDup-cons (λ ()) GC.noDup-nil
  generatedWalkVertexListsNoDuplicates′ (suc k) =
    generatedBlocksNoDuplicates
      {G = G} {Δ = Δ} {r = r} {L = k}
      A
      (GC.walkObjectsFromNeighbourCodes
        A r k)
      (generatedWalkVertexListsNoDuplicates′ k)
      (λ (w : GC.WalkObject G r k) → GC.CanonicalBoundedNeighbourEnumeration.neighboursNoDuplicates
        (P06.toGraphCanonicalBoundedNeighbourEnumeration E)
        (GC.WalkObject.endpoint w))

------------------------------------------------------------------------
-- Complete finite valid-walk semantic package.
------------------------------------------------------------------------

record GeneratedWalkVertexListSemantics
  {G : GC.Graph} {Δ : Nat} {r : GC.Graph.Vertex G} {L : Nat}
  (E : P06.P06CanonicalBoundedNeighbourEnumeration G Δ)
  : Set₁ where
  field
    walks : List (List (GC.Graph.Vertex G))
    walksAreGenerated :
      walks ≡
        GC.generatedWalkVertexLists {r = r} {L = L}
          (GC.CanonicalBoundedNeighbourEnumeration.bounded
            (P06.toGraphCanonicalBoundedNeighbourEnumeration E))
    completeByVertices :
      ∀ (w : GC.WalkObject G r L) →
      Σ (List (GC.Graph.Vertex G)) λ vs →
        vs ∈ walks × vs ≡ GC.walkObjectVertices w
    noDuplicates : GC.NoDuplicates walks
    countAgrees :
      GC.countWalks G r L ≡ length walks

generatedWalkVertexListSemantics :
  {G : GC.Graph} {Δ : Nat} {r : GC.Graph.Vertex G} {L : Nat}
  (E : P06.P06CanonicalBoundedNeighbourEnumeration G Δ) →
  GC.ConcreteWalkCountAgreement G Δ
    (GC.CanonicalBoundedNeighbourEnumeration.bounded
      (P06.toGraphCanonicalBoundedNeighbourEnumeration E))
    r L →
  GeneratedWalkVertexListSemantics {r = r} {L = L} E
generatedWalkVertexListSemantics {G} {Δ} {r} {L} E agreement = record
  { walks =
      GC.generatedWalkVertexLists {r = r} {L = L}
        (GC.CanonicalBoundedNeighbourEnumeration.bounded
          (P06.toGraphCanonicalBoundedNeighbourEnumeration E))
  ; walksAreGenerated = refl
  ; completeByVertices = λ w →
      GC.generatedWalkVertexListComplete
        (GC.CanonicalBoundedNeighbourEnumeration.bounded
          (P06.toGraphCanonicalBoundedNeighbourEnumeration E)) w
  ; noDuplicates = generatedWalkVertexListsNoDuplicates {L = L} E
  ; countAgrees =
      trans
        (GC.ConcreteWalkCountAgreement.countAgrees agreement)
        (sym (GC.listMapLength GC.walkObjectVertices
          (GC.walkObjectsFromNeighbourCodes
            (GC.CanonicalBoundedNeighbourEnumeration.bounded
              (P06.toGraphCanonicalBoundedNeighbourEnumeration E))
            r L)))
  }
