module DASHI.Moonshine.Y443ArmSwapOrbitMaxCutExact where

------------------------------------------------------------------------
-- Y443 RELATOR GRAPH AUTOMORPHISM / 72+8 MAX-CUT
--
-- The two length-four arms of the Y443 Coxeter tree may be exchanged;
-- the length-three arm and central vertex remain fixed.
-- This order-two automorphism is NOT the global balanced-ternary
-- antipodal map; compare the fixed-point censuses below.
--
-- Novel finite structure:
--   12 nodes    = 4 fixed + 2*4 moving
--   11 edges    = 3 fixed + 2*4 moving
--   55 nonedges = 7 fixed + 2*24 moving
--   78 Coxeter relators = 14 fixed + 2*32 moving
--   80 all relator LABELS = 16 fixed + 2*32 moving
--
-- Canonically indexed core 72:
--   ALL 55 nonedges + 8 moving-arm node involutions
--   + 8 moving-arm edge relators + central-node involution.
-- Complement 8:
--   three short-arm node involutions + three short-arm edge relators
--   + spider + central quotient relators.
--
-- This is a STRUCTURAL partition of the relator indices, not a
-- group-theoretic splitting of the normal closure of their words;
-- spider/central words are not assumed wordwise invariant under swap.
--
-- Reuses existing Y443 source transcription. No new Monster group.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y

swap : Y.Node → Y.Node
swap Y.a = Y.a
swap Y.b1 = Y.b2
swap Y.c1 = Y.c2
swap Y.d1 = Y.d2
swap Y.e1 = Y.e2
swap Y.b2 = Y.b1
swap Y.c2 = Y.c1
swap Y.d2 = Y.d1
swap Y.e2 = Y.e1
swap Y.b3 = Y.b3
swap Y.c3 = Y.c3
swap Y.d3 = Y.d3

swapInvolutive : (n : Y.Node) → swap (swap n) ≡ n
swapInvolutive Y.a = refl
swapInvolutive Y.b1 = refl
swapInvolutive Y.c1 = refl
swapInvolutive Y.d1 = refl
swapInvolutive Y.e1 = refl
swapInvolutive Y.b2 = refl
swapInvolutive Y.c2 = refl
swapInvolutive Y.d2 = refl
swapInvolutive Y.e2 = refl
swapInvolutive Y.b3 = refl
swapInvolutive Y.c3 = refl
swapInvolutive Y.d3 = refl

-- Fully exhaustive proof for the 12x12 graph adjacency matrix.
swapPreservesAdjacency :
  (x y : Y.Node) →
  Y.adjacent (swap x) (swap y) ≡ Y.adjacent x y
swapPreservesAdjacency Y.a Y.a = refl
swapPreservesAdjacency Y.a Y.b1 = refl
swapPreservesAdjacency Y.a Y.c1 = refl
swapPreservesAdjacency Y.a Y.d1 = refl
swapPreservesAdjacency Y.a Y.e1 = refl
swapPreservesAdjacency Y.a Y.b2 = refl
swapPreservesAdjacency Y.a Y.c2 = refl
swapPreservesAdjacency Y.a Y.d2 = refl
swapPreservesAdjacency Y.a Y.e2 = refl
swapPreservesAdjacency Y.a Y.b3 = refl
swapPreservesAdjacency Y.a Y.c3 = refl
swapPreservesAdjacency Y.a Y.d3 = refl
swapPreservesAdjacency Y.b1 Y.a = refl
swapPreservesAdjacency Y.b1 Y.b1 = refl
swapPreservesAdjacency Y.b1 Y.c1 = refl
swapPreservesAdjacency Y.b1 Y.d1 = refl
swapPreservesAdjacency Y.b1 Y.e1 = refl
swapPreservesAdjacency Y.b1 Y.b2 = refl
swapPreservesAdjacency Y.b1 Y.c2 = refl
swapPreservesAdjacency Y.b1 Y.d2 = refl
swapPreservesAdjacency Y.b1 Y.e2 = refl
swapPreservesAdjacency Y.b1 Y.b3 = refl
swapPreservesAdjacency Y.b1 Y.c3 = refl
swapPreservesAdjacency Y.b1 Y.d3 = refl
swapPreservesAdjacency Y.c1 Y.a = refl
swapPreservesAdjacency Y.c1 Y.b1 = refl
swapPreservesAdjacency Y.c1 Y.c1 = refl
swapPreservesAdjacency Y.c1 Y.d1 = refl
swapPreservesAdjacency Y.c1 Y.e1 = refl
swapPreservesAdjacency Y.c1 Y.b2 = refl
swapPreservesAdjacency Y.c1 Y.c2 = refl
swapPreservesAdjacency Y.c1 Y.d2 = refl
swapPreservesAdjacency Y.c1 Y.e2 = refl
swapPreservesAdjacency Y.c1 Y.b3 = refl
swapPreservesAdjacency Y.c1 Y.c3 = refl
swapPreservesAdjacency Y.c1 Y.d3 = refl
swapPreservesAdjacency Y.d1 Y.a = refl
swapPreservesAdjacency Y.d1 Y.b1 = refl
swapPreservesAdjacency Y.d1 Y.c1 = refl
swapPreservesAdjacency Y.d1 Y.d1 = refl
swapPreservesAdjacency Y.d1 Y.e1 = refl
swapPreservesAdjacency Y.d1 Y.b2 = refl
swapPreservesAdjacency Y.d1 Y.c2 = refl
swapPreservesAdjacency Y.d1 Y.d2 = refl
swapPreservesAdjacency Y.d1 Y.e2 = refl
swapPreservesAdjacency Y.d1 Y.b3 = refl
swapPreservesAdjacency Y.d1 Y.c3 = refl
swapPreservesAdjacency Y.d1 Y.d3 = refl
swapPreservesAdjacency Y.e1 Y.a = refl
swapPreservesAdjacency Y.e1 Y.b1 = refl
swapPreservesAdjacency Y.e1 Y.c1 = refl
swapPreservesAdjacency Y.e1 Y.d1 = refl
swapPreservesAdjacency Y.e1 Y.e1 = refl
swapPreservesAdjacency Y.e1 Y.b2 = refl
swapPreservesAdjacency Y.e1 Y.c2 = refl
swapPreservesAdjacency Y.e1 Y.d2 = refl
swapPreservesAdjacency Y.e1 Y.e2 = refl
swapPreservesAdjacency Y.e1 Y.b3 = refl
swapPreservesAdjacency Y.e1 Y.c3 = refl
swapPreservesAdjacency Y.e1 Y.d3 = refl
swapPreservesAdjacency Y.b2 Y.a = refl
swapPreservesAdjacency Y.b2 Y.b1 = refl
swapPreservesAdjacency Y.b2 Y.c1 = refl
swapPreservesAdjacency Y.b2 Y.d1 = refl
swapPreservesAdjacency Y.b2 Y.e1 = refl
swapPreservesAdjacency Y.b2 Y.b2 = refl
swapPreservesAdjacency Y.b2 Y.c2 = refl
swapPreservesAdjacency Y.b2 Y.d2 = refl
swapPreservesAdjacency Y.b2 Y.e2 = refl
swapPreservesAdjacency Y.b2 Y.b3 = refl
swapPreservesAdjacency Y.b2 Y.c3 = refl
swapPreservesAdjacency Y.b2 Y.d3 = refl
swapPreservesAdjacency Y.c2 Y.a = refl
swapPreservesAdjacency Y.c2 Y.b1 = refl
swapPreservesAdjacency Y.c2 Y.c1 = refl
swapPreservesAdjacency Y.c2 Y.d1 = refl
swapPreservesAdjacency Y.c2 Y.e1 = refl
swapPreservesAdjacency Y.c2 Y.b2 = refl
swapPreservesAdjacency Y.c2 Y.c2 = refl
swapPreservesAdjacency Y.c2 Y.d2 = refl
swapPreservesAdjacency Y.c2 Y.e2 = refl
swapPreservesAdjacency Y.c2 Y.b3 = refl
swapPreservesAdjacency Y.c2 Y.c3 = refl
swapPreservesAdjacency Y.c2 Y.d3 = refl
swapPreservesAdjacency Y.d2 Y.a = refl
swapPreservesAdjacency Y.d2 Y.b1 = refl
swapPreservesAdjacency Y.d2 Y.c1 = refl
swapPreservesAdjacency Y.d2 Y.d1 = refl
swapPreservesAdjacency Y.d2 Y.e1 = refl
swapPreservesAdjacency Y.d2 Y.b2 = refl
swapPreservesAdjacency Y.d2 Y.c2 = refl
swapPreservesAdjacency Y.d2 Y.d2 = refl
swapPreservesAdjacency Y.d2 Y.e2 = refl
swapPreservesAdjacency Y.d2 Y.b3 = refl
swapPreservesAdjacency Y.d2 Y.c3 = refl
swapPreservesAdjacency Y.d2 Y.d3 = refl
swapPreservesAdjacency Y.e2 Y.a = refl
swapPreservesAdjacency Y.e2 Y.b1 = refl
swapPreservesAdjacency Y.e2 Y.c1 = refl
swapPreservesAdjacency Y.e2 Y.d1 = refl
swapPreservesAdjacency Y.e2 Y.e1 = refl
swapPreservesAdjacency Y.e2 Y.b2 = refl
swapPreservesAdjacency Y.e2 Y.c2 = refl
swapPreservesAdjacency Y.e2 Y.d2 = refl
swapPreservesAdjacency Y.e2 Y.e2 = refl
swapPreservesAdjacency Y.e2 Y.b3 = refl
swapPreservesAdjacency Y.e2 Y.c3 = refl
swapPreservesAdjacency Y.e2 Y.d3 = refl
swapPreservesAdjacency Y.b3 Y.a = refl
swapPreservesAdjacency Y.b3 Y.b1 = refl
swapPreservesAdjacency Y.b3 Y.c1 = refl
swapPreservesAdjacency Y.b3 Y.d1 = refl
swapPreservesAdjacency Y.b3 Y.e1 = refl
swapPreservesAdjacency Y.b3 Y.b2 = refl
swapPreservesAdjacency Y.b3 Y.c2 = refl
swapPreservesAdjacency Y.b3 Y.d2 = refl
swapPreservesAdjacency Y.b3 Y.e2 = refl
swapPreservesAdjacency Y.b3 Y.b3 = refl
swapPreservesAdjacency Y.b3 Y.c3 = refl
swapPreservesAdjacency Y.b3 Y.d3 = refl
swapPreservesAdjacency Y.c3 Y.a = refl
swapPreservesAdjacency Y.c3 Y.b1 = refl
swapPreservesAdjacency Y.c3 Y.c1 = refl
swapPreservesAdjacency Y.c3 Y.d1 = refl
swapPreservesAdjacency Y.c3 Y.e1 = refl
swapPreservesAdjacency Y.c3 Y.b2 = refl
swapPreservesAdjacency Y.c3 Y.c2 = refl
swapPreservesAdjacency Y.c3 Y.d2 = refl
swapPreservesAdjacency Y.c3 Y.e2 = refl
swapPreservesAdjacency Y.c3 Y.b3 = refl
swapPreservesAdjacency Y.c3 Y.c3 = refl
swapPreservesAdjacency Y.c3 Y.d3 = refl
swapPreservesAdjacency Y.d3 Y.a = refl
swapPreservesAdjacency Y.d3 Y.b1 = refl
swapPreservesAdjacency Y.d3 Y.c1 = refl
swapPreservesAdjacency Y.d3 Y.d1 = refl
swapPreservesAdjacency Y.d3 Y.e1 = refl
swapPreservesAdjacency Y.d3 Y.b2 = refl
swapPreservesAdjacency Y.d3 Y.c2 = refl
swapPreservesAdjacency Y.d3 Y.d2 = refl
swapPreservesAdjacency Y.d3 Y.e2 = refl
swapPreservesAdjacency Y.d3 Y.b3 = refl
swapPreservesAdjacency Y.d3 Y.c3 = refl
swapPreservesAdjacency Y.d3 Y.d3 = refl

isFixedNode : Y.Node → Bool
isFixedNode Y.a = true
isFixedNode Y.b3 = true
isFixedNode Y.c3 = true
isFixedNode Y.d3 = true
isFixedNode _ = false

isMovingNode : Y.Node → Bool
isMovingNode Y.a = false
isMovingNode Y.b3 = false
isMovingNode Y.c3 = false
isMovingNode Y.d3 = false
isMovingNode _ = true

andB : Bool → Bool → Bool
andB true true = true
andB _ _ = false

orB : Bool → Bool → Bool
orB false false = false
orB _ _ = true

notB : Bool → Bool
notB false = true
notB true = false

-- Four inter-arm matched pairs are unordered-fixed even though neither
-- endpoint is fixed; six further unordered-fixed pairs use two fixed nodes.
isPartnerPair : Y.Node → Y.Node → Bool
isPartnerPair Y.b1 Y.b2 = true
isPartnerPair Y.b2 Y.b1 = true
isPartnerPair Y.c1 Y.c2 = true
isPartnerPair Y.c2 Y.c1 = true
isPartnerPair Y.d1 Y.d2 = true
isPartnerPair Y.d2 Y.d1 = true
isPartnerPair Y.e1 Y.e2 = true
isPartnerPair Y.e2 Y.e1 = true
isPartnerPair _ _ = false

isFixedPair : Y.Pair → Bool
isFixedPair p =
  orB (andB (isFixedNode (Y.first p)) (isFixedNode (Y.second p)))
      (isPartnerPair (Y.first p) (Y.second p))

ind : Bool → Nat
ind true = 1
ind false = 0

sumNodes : (Y.Node → Nat) → List Y.Node → Nat
sumNodes f [] = 0
sumNodes f (n ∷ ns) = f n + sumNodes f ns

sumPairs : (Y.Pair → Nat) → List Y.Pair → Nat
sumPairs f [] = 0
sumPairs f (p ∷ ps) = f p + sumPairs f ps

fixedNodeCount : Nat
fixedNodeCount = sumNodes (λ n → ind (isFixedNode n)) Y.nodes

movingNodeCount : Nat
movingNodeCount = sumNodes (λ n → ind (isMovingNode n)) Y.nodes

fixedEdgeCount : Nat
fixedEdgeCount =
  sumPairs
    (λ p → ind (andB (isFixedPair p)
       (Y.adjacent (Y.first p) (Y.second p)))) Y.pairs

movingEdgeCount : Nat
movingEdgeCount =
  sumPairs
    (λ p → ind (andB (notB (isFixedPair p))
       (Y.adjacent (Y.first p) (Y.second p)))) Y.pairs

fixedNonedgeCount : Nat
fixedNonedgeCount =
  sumPairs
    (λ p → ind (andB (isFixedPair p)
       (notB (Y.adjacent (Y.first p) (Y.second p))))) Y.pairs

movingNonedgeCount : Nat
movingNonedgeCount =
  sumPairs
    (λ p → ind (andB (notB (isFixedPair p))
       (notB (Y.adjacent (Y.first p) (Y.second p))))) Y.pairs

fixedNodesAreFour : fixedNodeCount ≡ 4
fixedNodesAreFour = refl

movingNodesAreEight : movingNodeCount ≡ 8
movingNodesAreEight = refl

fixedEdgesAreThree : fixedEdgeCount ≡ 3
fixedEdgesAreThree = refl

movingEdgesAreEight : movingEdgeCount ≡ 8
movingEdgesAreEight = refl

fixedNonedgesAreSeven : fixedNonedgeCount ≡ 7
fixedNonedgesAreSeven = refl

movingNonedgesAreFortyEight : movingNonedgeCount ≡ 48
movingNonedgesAreFortyEight = refl

coxeterFixedCount : Nat
coxeterFixedCount = fixedNodeCount + fixedEdgeCount + fixedNonedgeCount

coxeterMovingCount : Nat
coxeterMovingCount = movingNodeCount + movingEdgeCount + movingNonedgeCount

coxeterFourteenFixed : coxeterFixedCount ≡ 14
coxeterFourteenFixed = refl

coxeterSixtyFourMoving : coxeterMovingCount ≡ 64
coxeterSixtyFourMoving = refl

coxeterSeventyEight : coxeterFixedCount + coxeterMovingCount ≡ 78
coxeterSeventyEight = refl

-- The fixed spider/central values are relator INDEX tags. This does not
-- prove the words fixed by the arm-swap substitution as literal lists.
fullFixedLabelCount : Nat
fullFixedLabelCount = coxeterFixedCount + 2

fullLabelCount : Nat
fullLabelCount = fullFixedLabelCount + coxeterMovingCount

fullSixteenFixedLabels : fullFixedLabelCount ≡ 16
fullSixteenFixedLabels = refl

fullEightyLabels : fullLabelCount ≡ 80
fullEightyLabels = refl

------------------------------------------------------------------------
-- Graph-canonical 72/6/8 segmentation by the unique trivalent centre,
-- its two equal-length arms, and the short arm.
------------------------------------------------------------------------

isCentralNode : Y.Node → Bool
isCentralNode Y.a = true
isCentralNode _ = false

centralCount : Nat
centralCount = sumNodes (λ n → ind (isCentralNode n)) Y.nodes

shortArmNoncentralCount : Nat
shortArmNoncentralCount = 3

shortArmEdgeCount : Nat
shortArmEdgeCount = fixedEdgeCount

coreRelatorCount : Nat
coreRelatorCount =
  Y.countNonedges Y.pairs + movingNodeCount + movingEdgeCount + centralCount

coxeterResidualCount : Nat
coxeterResidualCount = shortArmNoncentralCount + shortArmEdgeCount

allResidualCount : Nat
allResidualCount = coxeterResidualCount + 2

coreIsEightByNine : coreRelatorCount ≡ 8 * 9
coreIsEightByNine = refl

coxeterCutIsSeventyTwoPlusSix :
  coreRelatorCount + coxeterResidualCount ≡ 78
coxeterCutIsSeventyTwoPlusSix = refl

fullCutIsSeventyTwoPlusEight :
  coreRelatorCount + allResidualCount ≡ 80
fullCutIsSeventyTwoPlusEight = refl

-- Under this graph automorphism the 11 edge relators have THREE fixed
-- indices; the 55 nonedge relators have SEVEN fixed indices.
-- Thus neither raw family is the "one centre + antipodal pairs" shape
-- of the existing 9 (one fixed) or 27 (one fixed) ternary carriers.
edgeOrbitCount : Nat
edgeOrbitCount = fixedEdgeCount + 4

nonedgeOrbitCount : Nat
nonedgeOrbitCount = fixedNonedgeCount + 24

edgeHasSevenOrbitClasses : edgeOrbitCount ≡ 7
edgeHasSevenOrbitClasses = refl

nonedgeHasThirtyOneOrbitClasses : nonedgeOrbitCount ≡ 31
nonedgeHasThirtyOneOrbitClasses = refl
