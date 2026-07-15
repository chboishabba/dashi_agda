module DASHI.Physics.YangMills.BalabanCubeEdgeDFSTour where

------------------------------------------------------------------------
-- Proof-free recovery data for canonical DFS tours of cube-edge trees.
--
-- This module deliberately separates the lossless *decoder* from the
-- remaining construction of a rooted structural view of a valid tree code.
-- Once that view supplies its closed DFS tour, the two canonical lists below
-- are the exact proof-free data that must agree with `canonicalVertices` and
-- `canonicalEdges` from BalabanCubeEdgeTreeCodes.  In particular, no equality
-- of proof-carrying tree records occurs anywhere in this decoding layer.
------------------------------------------------------------------------

open import Data.Nat.Base using (NonZero)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Physics.YangMills.GraphCombinatorics using
  ( NoDuplicates; mapList; canonicalize; canonicalizeNoDup )
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( faceCubeGraph )
open import DASHI.Physics.YangMills.BalabanCubeEdgeIncidence using
  ( CubeGridVertex4 )
open import DASHI.Physics.YangMills.BalabanCubeEdgeTreeCodes using
  ( CubeGridEdgeCode; gridEdge
  ; edgeCodeGraph; normaliseGridEdge )

------------------------------------------------------------------------
-- Consecutive pairs retain the directed traversal presentation.  The
-- canonical edge decoder subsequently normalises orientation, removes the
-- return traversal of each tree edge, and orders the result.

adjacentPairs : ∀ {N} →
  List (CubeGridVertex4 N) → List (CubeGridEdgeCode N)
adjacentPairs [] = []
adjacentPairs (u ∷ []) = []
adjacentPairs (u ∷ v ∷ vertices) =
  gridEdge u v ∷ adjacentPairs (v ∷ vertices)

tourCanonicalVertices : ∀ {N} {{_ : NonZero N}} →
  List (CubeGridVertex4 N) → List (CubeGridVertex4 N)
tourCanonicalVertices {N} vertices =
  canonicalize {G = faceCubeGraph {N}} vertices

tourCanonicalEdges : ∀ {N} {{_ : NonZero N}} →
  List (CubeGridVertex4 N) → List (CubeGridEdgeCode N)
tourCanonicalEdges {N} tour =
  canonicalize {G = edgeCodeGraph {N}}
    (mapList normaliseGridEdge (adjacentPairs tour))

tourCanonicalVertices-noDuplicates : ∀ {N} {{_ : NonZero N}}
  (tour : List (CubeGridVertex4 N)) →
  NoDuplicates (tourCanonicalVertices tour)
tourCanonicalVertices-noDuplicates {N} tour =
  canonicalizeNoDup {G = faceCubeGraph {N}} tour

tourCanonicalEdges-noDuplicates : ∀ {N} {{_ : NonZero N}}
  (tour : List (CubeGridVertex4 N)) →
  NoDuplicates (tourCanonicalEdges tour)
tourCanonicalEdges-noDuplicates {N} tour =
  canonicalizeNoDup {G = edgeCodeGraph {N}}
    (mapList normaliseGridEdge (adjacentPairs tour))
