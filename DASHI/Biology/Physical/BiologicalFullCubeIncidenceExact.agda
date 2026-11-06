module DASHI.Biology.Physical.BiologicalFullCubeIncidenceExact where

------------------------------------------------------------------------
-- P2: COMPLETE NONPERIODIC 3x3x3 CUBICAL INCIDENCE
--
-- There are 27 voxels, 54 positive oriented nearest-neighbour edges
-- and 36 elementary squares.  Each edge carries an actual native
-- HypervoxelAdjacent proof; square paths close by definitional equality.
-- This is the lattice/incidence skeleton, NOT a discretized PNP law or
-- an empirical conservation/boundary-condition certificate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Biology.Physical.BiologicalHistoryFutureQuotientExact as Bio

data Segment2 : Set where
  lower upper : Segment2

low : Segment2 → SSP.SSPTrit
low lower = SSP.sspNegOne
low upper = SSP.sspZero

high : Segment2 → SSP.SSPTrit
high lower = SSP.sspZero
high upper = SSP.sspPosOne

forwardWitness :
  (s : Segment2) → Cube.TritGridStep (low s) (high s)
forwardWitness lower = Cube.negToZero
forwardWitness upper = Cube.zeroToPos

-- Each physical (undirected) grid bond appears once, with a positive
-- coordinate orientation.  Reverse transport is NOT confused with
-- another geometrically distinct bond.
data PositiveBond : Set where
  xBond : Segment2 → SSP.SSPTrit → SSP.SSPTrit → PositiveBond
  yBond : SSP.SSPTrit → Segment2 → SSP.SSPTrit → PositiveBond
  zBond : SSP.SSPTrit → SSP.SSPTrit → Segment2 → PositiveBond

bondStart : PositiveBond → Cube.Ternary27Point
bondStart (xBond s y z) = Cube.ternary27Point (low s) y z
bondStart (yBond x s z) = Cube.ternary27Point x (low s) z
bondStart (zBond x y s) = Cube.ternary27Point x y (low s)

bondEnd : PositiveBond → Cube.Ternary27Point
bondEnd (xBond s y z) = Cube.ternary27Point (high s) y z
bondEnd (yBond x s z) = Cube.ternary27Point x (high s) z
bondEnd (zBond x y s) = Cube.ternary27Point x y (high s)

bondIsNearestNeighbour :
  (edge : PositiveBond) →
  Cube.HypervoxelAdjacent (bondStart edge) (bondEnd edge)
bondIsNearestNeighbour (xBond s y z) =
  Cube.adjacentX (forwardWitness s)
bondIsNearestNeighbour (yBond x s z) =
  Cube.adjacentY (forwardWitness s)
bondIsNearestNeighbour (zBond x y s) =
  Cube.adjacentZ (forwardWitness s)

trits : List SSP.SSPTrit
trits = SSP.sspNegOne ∷ SSP.sspZero ∷ SSP.sspPosOne ∷ []

segments : List Segment2
segments = lower ∷ upper ∷ []

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

flatMap : ∀ {A B : Set} → (A → List B) → List A → List B
flatMap f [] = []
flatMap f (x ∷ xs) = append (f x) (flatMap f xs)

countList : ∀ {A : Set} → List A → Nat
countList [] = zero
countList (_ ∷ rest) = suc (countList rest)

xBonds : List PositiveBond
xBonds = flatMap
  (λ s → flatMap
    (λ y → mapList (λ z → xBond s y z) trits) trits)
  segments

yBonds : List PositiveBond
yBonds = flatMap
  (λ s → flatMap
    (λ x → mapList (λ z → yBond x s z) trits) trits)
  segments

zBonds : List PositiveBond
zBonds = flatMap
  (λ s → flatMap
    (λ x → mapList (λ y → zBond x y s) trits) trits)
  segments

allPositiveBonds : List PositiveBond
allPositiveBonds = append xBonds (append yBonds zBonds)

completeBondCount : countList allPositiveBonds ≡ 54
completeBondCount = refl

-- 12 xy, 12 xz, 12 yz squares, each uniquely positive oriented.
data ElementarySquare : Set where
  xySquare : Segment2 → Segment2 → SSP.SSPTrit → ElementarySquare
  xzSquare : Segment2 → SSP.SSPTrit → Segment2 → ElementarySquare
  yzSquare : SSP.SSPTrit → Segment2 → Segment2 → ElementarySquare

allXYSquares : List ElementarySquare
allXYSquares = flatMap
  (λ a → flatMap
    (λ b → mapList (λ z → xySquare a b z) trits) segments)
  segments

allXZSquares : List ElementarySquare
allXZSquares = flatMap
  (λ a → flatMap
    (λ b → mapList (λ y → xzSquare a y b) trits) segments)
  segments

allYZSquares : List ElementarySquare
allYZSquares = flatMap
  (λ a → flatMap
    (λ b → mapList (λ x → yzSquare x a b) trits) segments)
  segments

allElementarySquares : List ElementarySquare
allElementarySquares =
  append allXYSquares (append allXZSquares allYZSquares)

completePlaquetteCount : countList allElementarySquares ≡ 36
completePlaquetteCount = refl

-- Four bonds of a square, giving two oriented two-hop paths:
-- lowerFirst; upperSecond and lowerSecond; upperFirst.
lowerFirst upperFirst lowerSecond upperSecond :
  ElementarySquare → PositiveBond

lowerFirst (xySquare a b z) = xBond a (low b) z
upperFirst (xySquare a b z) = xBond a (high b) z
lowerSecond (xySquare a b z) = yBond (low a) b z
upperSecond (xySquare a b z) = yBond (high a) b z

lowerFirst (xzSquare a y b) = xBond a y (low b)
upperFirst (xzSquare a y b) = xBond a y (high b)
lowerSecond (xzSquare a y b) = zBond (low a) y b
upperSecond (xzSquare a y b) = zBond (high a) y b

lowerFirst (yzSquare x a b) = yBond x a (low b)
upperFirst (yzSquare x a b) = yBond x a (high b)
lowerSecond (yzSquare x a b) = zBond x (low a) b
upperSecond (yzSquare x a b) = zBond x (high a) b

squareInitialCorner :
  (q : ElementarySquare) →
  bondStart (lowerFirst q) ≡ bondStart (lowerSecond q)
squareInitialCorner (xySquare a b z) = refl
squareInitialCorner (xzSquare a y b) = refl
squareInitialCorner (yzSquare x a b) = refl

firstThenSecondMeet :
  (q : ElementarySquare) →
  bondEnd (lowerFirst q) ≡ bondStart (upperSecond q)
firstThenSecondMeet (xySquare a b z) = refl
firstThenSecondMeet (xzSquare a y b) = refl
firstThenSecondMeet (yzSquare x a b) = refl

secondThenFirstMeet :
  (q : ElementarySquare) →
  bondEnd (lowerSecond q) ≡ bondStart (upperFirst q)
secondThenFirstMeet (xySquare a b z) = refl
secondThenFirstMeet (xzSquare a y b) = refl
secondThenFirstMeet (yzSquare x a b) = refl

squareFinalCorner :
  (q : ElementarySquare) →
  bondEnd (upperSecond q) ≡ bondEnd (upperFirst q)
squareFinalCorner (xySquare a b z) = refl
squareFinalCorner (xzSquare a y b) = refl
squareFinalCorner (yzSquare x a b) = refl

-- Only observable junction incidence is transported, no constitutive
-- current or flux parameter is invented.
fineJunctionPair :
  Bio.TissueField → PositiveBond → Bool × Bool
fineJunctionPair field edge =
  Bio.junctionPresent (field (bondStart edge)) ,
  Bio.junctionPresent (field (bondEnd edge))

coarseJunctionPair :
  Bio.CoarseTissueField → PositiveBond → Bool × Bool
coarseJunctionPair field edge =
  Bio.codeJunction (field (bondStart edge)) ,
  Bio.codeJunction (field (bondEnd edge))

allBondJunctionReadingsSurviveProjection :
  (field : Bio.TissueField) (edge : PositiveBond) →
  fineJunctionPair field edge
    ≡ coarseJunctionPair (Bio.spatialProject field) edge
allBondJunctionReadingsSurviveProjection field edge
  with field (bondStart edge) | field (bondEnd edge)
... | Bio.biologicalState g c h j e p
    | Bio.biologicalState g' c' h' j' e' p' = refl
