module DASHI.Codec.IndexedCubeMarkedAffine9Exact where

-- H07: selected literal graph-of-slopes chart on affine two-planes
-- in F3^5. This is a NINE-parameter marked chart, not the quotient
-- by all possible pivot charts or a global real Grassmannian chart.
-- Reuses the original 8-object/12-map/6-square commuting cube.
-- Source-written; Agda kernel OPEN.

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Codec.IndexedCubeMaskSignExact as C
import DASHI.Codec.IndexedCubeMaskSignInstanceExact as I
import DASHI.Codec.IndexedCubeGeometryChartExact as G
import DASHI.Core.GovernedIndexedResidualCubeExact as Q

-- The chart mark is material: this concrete chart has pivots 0 and 1,
-- and the remaining three coordinates are the dependent positions.
data PivotChart : Set where
  pivot01 : PivotChart

record Affine9 (A : Set) : Set where
  constructor affine9
  field
    pivot : PivotChart
    slopeU : M.Triple A
    slopeV : M.Triple A
    offset : M.Triple A
open Affine9 public

fromBlocks : ∀ {A : Set} → C.Blocks A → Affine9 A
fromBlocks (C.blocks u v b) = affine9 pivot01 u v b

toBlocks : ∀ {A : Set} → Affine9 A → C.Blocks A
toBlocks (affine9 pivot01 u v b) = C.blocks u v b

blocksRoundTrip : ∀ {A : Set} (x : C.Blocks A) →
  toBlocks (fromBlocks x) ≡ x
blocksRoundTrip (C.blocks u v b) = refl

affineRoundTrip : ∀ {A : Set} (x : Affine9 A) →
  fromBlocks (toBlocks x) ≡ x
affineRoundTrip (affine9 pivot01 u v b) = refl

fromSplit : ∀ {A : Set} → C.PrefixResidual A → Affine9 A
fromSplit x = fromBlocks (C.join x)

toSplit : ∀ {A : Set} → Affine9 A → C.PrefixResidual A
toSplit x = C.partition (toBlocks x)

splitRoundTrip : ∀ {A : Set} (x : C.PrefixResidual A) →
  toSplit (fromSplit x) ≡ x
splitRoundTrip (C.split u v b) = refl

affineSplitRoundTrip : ∀ {A : Set} (x : Affine9 A) →
  fromSplit (toSplit x) ≡ x
affineSplitRoundTrip (affine9 pivot01 u v b) = refl

-- The selected field F3 arithmetic is an explicit, non-Boolean table.
-- Marked graph: (u,v) -> (u,v,b + u*slopeU + v*slopeV).
add3 : Trit → Trit → Trit
add3 neg neg = pos
add3 neg zer = neg
add3 neg pos = zer
add3 zer a = a
add3 pos neg = zer
add3 pos zer = pos
add3 pos pos = neg

mul3 : Trit → Trit → Trit
mul3 neg neg = pos
mul3 neg zer = zer
mul3 neg pos = neg
mul3 zer _ = zer
mul3 pos a = a

addTriple : M.Triple Trit → M.Triple Trit → M.Triple Trit
addTriple (M.triple a b c) (M.triple d e f) =
  M.triple (add3 a d) (add3 b e) (add3 c f)

scaleTriple : Trit → M.Triple Trit → M.Triple Trit
scaleTriple u = M.mapTriple (mul3 u)

record Point5 : Set where
  constructor point5
  field
    firstCoordinate secondCoordinate : Trit
    dependentCoordinates : M.Triple Trit

evaluate : Affine9 Trit → Trit → Trit → Point5
evaluate plane u v =
  point5 u v
    (addTriple (offset plane)
      (addTriple (scaleTriple u (slopeU plane))
                 (scaleTriple v (slopeV plane))))

-- In the selected pivot chart, the same two distinct first coordinates
-- prove that the parametrization does not collapse the sheet.
recoverPivotU : (p : Affine9 Trit) (u v : Trit) →
  Point5.firstCoordinate (evaluate p u v) ≡ u
recoverPivotU p u v = refl

recoverPivotV : (p : Affine9 Trit) (u v : Trit) →
  Point5.secondCoordinate (evaluate p u v) ≡ v
recoverPivotV p u v = refl

blocksChart : ∀ {A : Set} → G.Chart (C.Blocks A)
blocksChart = record
  { Coordinates = Affine9 _
  ; encode = fromBlocks
  ; decode = toBlocks
  ; decodeEncode = blocksRoundTrip
  ; encodeDecode = affineRoundTrip
  }

splitChart : ∀ {A : Set} → G.Chart (C.PrefixResidual A)
splitChart = record
  { Coordinates = Affine9 _
  ; encode = fromSplit
  ; decode = toSplit
  ; decodeEncode = splitRoundTrip
  ; encodeDecode = affineSplitRoundTrip
  }

-- Distinguish raw trits and mask/sign factorized trits at vertices,
-- retaining all nine original coordinates rather than claiming compression.
markedCharts : G.Charts I.codecCube
markedCharts = record
  { a = blocksChart ; b = splitChart
  ; c = blocksChart ; d = splitChart
  ; e = blocksChart ; f = splitChart
  ; h = blocksChart ; i = splitChart
  }

markedCube : Q.Cube
markedCube = G.recharted I.codecCube markedCharts

markedFaces : Q.Faces markedCube
markedFaces = G.rechartedFaces I.codecCube I.codecFaces markedCharts

markedExact : Q.ExactFaces markedCube markedFaces
markedExact =
  G.rechartedExact I.codecCube I.codecFaces markedCharts I.codecExactFaces

-- The six monotone terminal paths agree by the original SIX FACE witnesses.
markedAllPaths : (x : Q.A markedCube) →
  Q.xyz markedCube x ≡ Q.zyx markedCube x
markedAllPaths = Q.xyz-zyx markedExact
