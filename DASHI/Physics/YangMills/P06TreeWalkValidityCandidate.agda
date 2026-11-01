module DASHI.Physics.YangMills.P06TreeWalkValidityCandidate where

------------------------------------------------------------------------
-- P06 tree/DFS validity candidate.
--
-- TreeDFSWalk stores coverage and length metadata, but not the data needed
-- by Path: nonemptiness/root, endpoint, or consecutive adjacency.  This
-- module supplies precisely that missing evidence and proves the
-- tree-to-ambient adapters.  No postulate is introduced and no existing
-- module is edited.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Nat.Base using (ℕ; _∸_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC

------------------------------------------------------------------------
-- Minimal missing evidence for a TreeDFSWalk to be a Path.
------------------------------------------------------------------------

record TreeDFSWalkPathEvidence
  {T : GC.Graph} {r : GC.Graph.Vertex T}
  (w : GC.TreeDFSWalk T r)
  (L : ℕ) : Set₁ where
  field
    endpoint : GC.Graph.Vertex T
    nonEmpty : GC.NonEmpty (GC.TreeDFSWalk.w w)
    startsAt :
      GC.head (GC.TreeDFSWalk.w w) nonEmpty ≡ r
    endsAt :
      GC.last (GC.TreeDFSWalk.w w) nonEmpty ≡ endpoint
    adjacent :
      GC.ConsecutiveEdges T (GC.TreeDFSWalk.w w)
    length-is :
      GC.pathLength
        (record
          { vertices = GC.TreeDFSWalk.w w
          ; nonEmptyWitness = nonEmpty
          ; startsAt = startsAt
          ; endsAt = endsAt
          ; adjacent = adjacent
          })
        ≡ L

treeDFSWalkPath
  : {T : GC.Graph} {r : GC.Graph.Vertex T}
  → {w : GC.TreeDFSWalk T r} {L : ℕ}
  → (evidence : TreeDFSWalkPathEvidence w L)
  → GC.Path T r (TreeDFSWalkPathEvidence.endpoint evidence)
treeDFSWalkPath {w = w} evidence = record
  { vertices = GC.TreeDFSWalk.w w
  ; nonEmptyWitness = TreeDFSWalkPathEvidence.nonEmpty evidence
  ; startsAt = TreeDFSWalkPathEvidence.startsAt evidence
  ; endsAt = TreeDFSWalkPathEvidence.endsAt evidence
  ; adjacent = TreeDFSWalkPathEvidence.adjacent evidence
  }

treeDFSWalkEvidenceToWalkObject
  : {T : GC.Graph} {r : GC.Graph.Vertex T}
  → {w : GC.TreeDFSWalk T r} {L : ℕ}
  → (evidence : TreeDFSWalkPathEvidence w L)
  → GC.WalkObject T r L
treeDFSWalkEvidenceToWalkObject evidence = record
  { endpoint = TreeDFSWalkPathEvidence.endpoint evidence
  ; path = treeDFSWalkPath evidence
  ; length-is = TreeDFSWalkPathEvidence.length-is evidence
  }

------------------------------------------------------------------------
-- List transport needed to lift the evidence through a spanning tree.
------------------------------------------------------------------------

mapNonEmpty
  : {A B : Set} (f : A → B) {xs : List A}
  → GC.NonEmpty xs
  → GC.NonEmpty (GC.mapList f xs)
mapNonEmpty f GC.nonempty = GC.nonempty

mapHead
  : {A B : Set} (f : A → B) {xs : List A}
  → (nonEmpty : GC.NonEmpty xs)
  → GC.head (GC.mapList f xs) (mapNonEmpty f nonEmpty)
      ≡ f (GC.head xs nonEmpty)
mapHead f GC.nonempty = refl

mapLast
  : {A B : Set} (f : A → B) {xs : List A}
  → (nonEmpty : GC.NonEmpty xs)
  → GC.last (GC.mapList f xs) (mapNonEmpty f nonEmpty)
      ≡ f (GC.last xs nonEmpty)
mapLast f {xs = x ∷ []} GC.nonempty = refl
mapLast f {xs = x ∷ y ∷ xs} nonempty =
  mapLast f {xs = y ∷ xs} nonempty

mapConsecutiveEdges
  : {G H : GC.Graph}
  → (f : GC.Graph.Vertex G → GC.Graph.Vertex H)
  → (preserve : ∀ {x y} → GC.Graph.Adj G x y
                         → GC.Graph.Adj H (f x) (f y))
  → {xs : List (GC.Graph.Vertex G)}
  → GC.ConsecutiveEdges G xs
  → GC.ConsecutiveEdges H (GC.mapList f xs)
mapConsecutiveEdges f preserve GC.edges-single = GC.edges-single
mapConsecutiveEdges f preserve (GC.edges-step xy rest) =
  GC.edges-step (preserve xy) (mapConsecutiveEdges f preserve rest)

------------------------------------------------------------------------
-- Strong constructive adapter: tree path evidence lifts to ambient path.
------------------------------------------------------------------------

treePathEvidenceToAmbientPath
  : {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  → (st : GC.SpanningTree G X)
  → {r : GC.Graph.Vertex G}
  → (rt : Σ (GC.Graph.Vertex (GC.SpanningTree.T st))
          (λ rT → GC.SpanningTree.embed st rT ≡ r
            × GC.RootedTree (GC.SpanningTree.T st) rT))
  → {w : GC.TreeDFSWalk (GC.SpanningTree.T st) (proj₁ rt)}
  → {L : ℕ}
  → (evidence : TreeDFSWalkPathEvidence w L)
  → GC.Path G r
      (GC.SpanningTree.embed st
        (TreeDFSWalkPathEvidence.endpoint evidence))
treePathEvidenceToAmbientPath st rt {w = w} evidence = record
  { vertices = GC.mapList (GC.SpanningTree.embed st)
      (GC.TreeDFSWalk.w w)
  ; nonEmptyWitness =
      mapNonEmpty
        (GC.SpanningTree.embed st)
        (TreeDFSWalkPathEvidence.nonEmpty evidence)
  ; startsAt =
      trans
        (mapHead
          (GC.SpanningTree.embed st)
          (TreeDFSWalkPathEvidence.nonEmpty evidence))
        (trans
          (cong (GC.SpanningTree.embed st)
            (TreeDFSWalkPathEvidence.startsAt evidence))
          (proj₁ (proj₂ rt)))
  ; endsAt =
      trans
        (mapLast
          (GC.SpanningTree.embed st)
          (TreeDFSWalkPathEvidence.nonEmpty evidence))
        (cong (GC.SpanningTree.embed st)
          (TreeDFSWalkPathEvidence.endsAt evidence))
  ; adjacent =
      mapConsecutiveEdges
        (GC.SpanningTree.embed st)
        (λ {x} {y} → GC.SubgraphAdjImpliesAmbientAdj st x y)
        (TreeDFSWalkPathEvidence.adjacent evidence)
  }

treePathEvidenceAmbientLength
  : {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  → (st : GC.SpanningTree G X)
  → {r : GC.Graph.Vertex G}
  → (rt : Σ (GC.Graph.Vertex (GC.SpanningTree.T st))
          (λ rT → GC.SpanningTree.embed st rT ≡ r
            × GC.RootedTree (GC.SpanningTree.T st) rT))
  → {w : GC.TreeDFSWalk (GC.SpanningTree.T st) (proj₁ rt)}
  → {L : ℕ}
  → (evidence : TreeDFSWalkPathEvidence w L)
  → GC.pathLength (treePathEvidenceToAmbientPath st rt evidence) ≡ L
treePathEvidenceAmbientLength st rt {w = w} evidence =
  let
    mapped-length :
      length
        (GC.mapList (GC.SpanningTree.embed st)
          (GC.TreeDFSWalk.w w)) ∸ 1
        ≡ length (GC.TreeDFSWalk.w w) ∸ 1
    mapped-length =
      cong (λ k → k ∸ 1)
        (GC.listMapLength
          {A = GC.Graph.Vertex (GC.SpanningTree.T st)}
          (GC.SpanningTree.embed st)
          (GC.TreeDFSWalk.w w))
  in trans mapped-length (TreeDFSWalkPathEvidence.length-is evidence)

treePathEvidenceToAmbientWalkObject
  : {G : GC.Graph} {X : List (GC.Graph.Vertex G)}
  → (st : GC.SpanningTree G X)
  → {r : GC.Graph.Vertex G}
  → (rt : Σ (GC.Graph.Vertex (GC.SpanningTree.T st))
          (λ rT → GC.SpanningTree.embed st rT ≡ r
            × GC.RootedTree (GC.SpanningTree.T st) rT))
  → {w : GC.TreeDFSWalk (GC.SpanningTree.T st) (proj₁ rt)}
  → {L : ℕ}
  → (evidence : TreeDFSWalkPathEvidence w L)
  → GC.WalkObject G r L
treePathEvidenceToAmbientWalkObject st rt evidence = record
  { endpoint =
      GC.SpanningTree.embed st
        (TreeDFSWalkPathEvidence.endpoint evidence)
  ; path = treePathEvidenceToAmbientPath st rt evidence
  ; length-is = treePathEvidenceAmbientLength st rt evidence
  }

------------------------------------------------------------------------
-- The exact remaining bridge to a selected DFS range.
------------------------------------------------------------------------

record DFSRangeTreePathWitness
  {G : GC.Graph} {r : GC.Graph.Vertex G} {X : List (GC.Graph.Vertex G)}
  (st : GC.SpanningTree G X)
  (rt : Σ (GC.Graph.Vertex (GC.SpanningTree.T st))
          (λ rT → GC.SpanningTree.embed st rT ≡ r
            × GC.RootedTree (GC.SpanningTree.T st) rT))
  (w : GC.TreeDFSWalk (GC.SpanningTree.T st) (proj₁ rt))
  (range : List (GC.Graph.Vertex G))
  (L : ℕ) : Set₁ where
  field
    pathEvidence : TreeDFSWalkPathEvidence w L

    -- Coverage does not imply equality with a chosen range.  Keeping this
    -- equality explicit prevents a false conversion from DFSCover.covers.
    range-is :
      GC.SubgraphWalkLiftsToAmbient st rt w
        ≡ range

dfsRangeTreePathWitnessToRangeWalkObject
  : {G : GC.Graph} {r : GC.Graph.Vertex G} {X : List (GC.Graph.Vertex G)}
  → {st : GC.SpanningTree G X}
  → {rt : Σ (GC.Graph.Vertex (GC.SpanningTree.T st))
          (λ rT → GC.SpanningTree.embed st rT ≡ r
            × GC.RootedTree (GC.SpanningTree.T st) rT)}
  → {w : GC.TreeDFSWalk (GC.SpanningTree.T st) (proj₁ rt)}
  → {range : List (GC.Graph.Vertex G)} {L : ℕ}
  → (witness : DFSRangeTreePathWitness st rt w range L)
  → Σ (GC.WalkObject G r L)
      (λ walk → GC.walkObjectVertices walk ≡ range)
dfsRangeTreePathWitnessToRangeWalkObject {st = st} {rt = rt} witness =
  let walk =
        treePathEvidenceToAmbientWalkObject st rt
          (DFSRangeTreePathWitness.pathEvidence witness)
  in walk ,
     trans refl (DFSRangeTreePathWitness.range-is witness)

dfsRangeTreePathWitnessToAmbientWalkObject
  : {G : GC.Graph} {r : GC.Graph.Vertex G} {X : List (GC.Graph.Vertex G)}
  → {st : GC.SpanningTree G X}
  → {rt : Σ (GC.Graph.Vertex (GC.SpanningTree.T st))
          (λ rT → GC.SpanningTree.embed st rT ≡ r
            × GC.RootedTree (GC.SpanningTree.T st) rT)}
  → {w : GC.TreeDFSWalk (GC.SpanningTree.T st) (proj₁ rt)}
  → {L : ℕ}
  → DFSRangeTreePathWitness st rt w
      (GC.SubgraphWalkLiftsToAmbient st rt w) L
  → GC.WalkObject G r L
dfsRangeTreePathWitnessToAmbientWalkObject {st = st} {rt = rt} witness =
  treePathEvidenceToAmbientWalkObject st rt
    (DFSRangeTreePathWitness.pathEvidence witness)
