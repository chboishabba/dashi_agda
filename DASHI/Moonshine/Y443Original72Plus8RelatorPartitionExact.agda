module DASHI.Moonshine.Y443Original72Plus8RelatorPartitionExact where

------------------------------------------------------------------------
-- THE ACTUAL ORIGINAL Y443 80 RELATORS, REORGANIZED AS 72 + 8.
--
-- 72 = 55 nonedge Coxeter relators + 8 selected node involutions
--    + 8 tree-edge relators + the single spider relator.
--  8 = 4 complementary involutions + 3 complementary tree edges
--    + the single CENTRAL f312 relator.
--
-- This is a finite RELATOR PARTITION, not an equivariant
-- P^1(F9) indexing, not a new presentation, and not a proof of
-- the universal-quotient-to-selected-group kernel reflection.
--
-- Source ownership: Ivanov/Bray and Y443CoxeterPresentationExact.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y

-- Eight original nodes retained in the 72-slot section.
coreNodes : List Y.Node
coreNodes =
  Y.a ∷ Y.b1 ∷ Y.c1 ∷ Y.d1 ∷ Y.e1 ∷
  Y.b2 ∷ Y.c2 ∷ Y.d2 ∷ []

complementNodes : List Y.Node
complementNodes = Y.e2 ∷ Y.b3 ∷ Y.c3 ∷ Y.d3 ∷ []

-- Eight original connected diagram edges in the retained section.
coreEdges : List Y.Pair
coreEdges =
  Y.pair Y.a Y.b1 ∷
  Y.pair Y.b1 Y.c1 ∷
  Y.pair Y.c1 Y.d1 ∷
  Y.pair Y.d1 Y.e1 ∷
  Y.pair Y.a Y.b2 ∷
  Y.pair Y.b2 Y.c2 ∷
  Y.pair Y.c2 Y.d2 ∷
  Y.pair Y.a Y.b3 ∷ []

complementEdges : List Y.Pair
complementEdges =
  Y.pair Y.d2 Y.e2 ∷
  Y.pair Y.b3 Y.c3 ∷
  Y.pair Y.c3 Y.d3 ∷ []

-- All 55 original nonadjacent pairs, with no replacement relation.
originalNonedges : List Y.Pair → List Y.Pair
originalNonedges [] = []
originalNonedges (p ∷ ps) with Y.adjacent (Y.first p) (Y.second p)
... | true = originalNonedges ps
... | false = p ∷ originalNonedges ps

retained72 : List Y.Word
retained72 =
  Y.map Y.square coreNodes Y.++ 
  (Y.map Y.pairRelator coreEdges Y.++
  (Y.map Y.pairRelator (originalNonedges Y.pairs) Y.++
  (Y.spiderRelator ∷ [])))

complement8 : List Y.Word
complement8 =
  Y.map Y.square complementNodes Y.++
  (Y.map Y.pairRelator complementEdges Y.++
  (Y.centralInvolutionRelator ∷ []))

eightSelectedNodeInvolutions : Y.length coreNodes ≡ 8
eightSelectedNodeInvolutions = refl

fourComplementNodeInvolutions : Y.length complementNodes ≡ 4
fourComplementNodeInvolutions = refl

eightSelectedEdges : Y.length coreEdges ≡ 8
eightSelectedEdges = refl

threeComplementEdges : Y.length complementEdges ≡ 3
threeComplementEdges = refl

fiftyFiveLiteralNonedges :
  Y.length (originalNonedges Y.pairs) ≡ 55
fiftyFiveLiteralNonedges = refl

actualOriginal72Count : Y.length retained72 ≡ 72
actualOriginal72Count = refl

actualOriginal8Count : Y.length complement8 ≡ 8
actualOriginal8Count = refl

original80ReorganizedCount :
  Y.length retained72 + Y.length complement8 ≡ 80
original80ReorganizedCount = refl

-- Independent projective/number-role arithmetic. The 72=9×8
-- indexing is *not* automatically equivariant under graph symmetry.
nineTimesEightPlusEight : 9 * 8 + 8 ≡ 80
nineTimesEightPlusEight = refl

seventyOnePlusNine : 71 + 9 ≡ 80
seventyOnePlusNine = refl

seventyOnePlusTen : 71 + 10 ≡ 81
seventyOnePlusTen = refl

-- Exact semantic gap, intentionally NOT defined as an equality:
-- 1) all original 80 relation words are a permutation of
--    retained72 ++ complement8;
-- 2) an action-compatible isomorphism (if any) between the
--    projective F9 80 labels and original Y443 relator labels;
-- 3) selected group nonabelian kernel reflection (separate source).
