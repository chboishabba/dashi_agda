module DASHI.Moonshine.JInvariant369Cube27ModularSliceActionExact where

-- Spatially meaningful 27 = balanced 3x3x3 cube; three z-slices
-- are nine-position sheets, and the integral braid modular matrix M
-- acts on each sheet AFTER a chosen reduction mod 3.
-- It is a bijection of 27 POINTS but not an automorphism of the
-- nearest-neighbour cube graph. Hence modular "27" != cube geometry.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.JInvariant369PuncturedSheetModularBraidActionExact as M3

toKernel : SSP.SSPTrit → Triadic.KernelTrit
toKernel SSP.sspNegOne = Triadic.negativeTrit
toKernel SSP.sspZero = Triadic.zeroTrit
toKernel SSP.sspPosOne = Triadic.positiveTrit

fromKernel : Triadic.KernelTrit → SSP.SSPTrit
fromKernel Triadic.negativeTrit = SSP.sspNegOne
fromKernel Triadic.zeroTrit = SSP.sspZero
fromKernel Triadic.positiveTrit = SSP.sspPosOne

toFromKernel : (t : Triadic.KernelTrit) →
  toKernel (fromKernel t) ≡ t
toFromKernel Triadic.negativeTrit = refl
toFromKernel Triadic.zeroTrit = refl
toFromKernel Triadic.positiveTrit = refl

fromToKernel : (t : SSP.SSPTrit) →
  fromKernel (toKernel t) ≡ t
fromToKernel SSP.sspNegOne = refl
fromToKernel SSP.sspZero = refl
fromToKernel SSP.sspPosOne = refl

xySheet : Cube.Ternary27Point → Triadic.NineSheet
xySheet (Cube.ternary27Point x y z) = toKernel x , toKernel y

-- Matrix [[13,-8],[-8,5]] mod3 is [[1,1],[1,-1]].
-- Spatial cube operator M3(x,y,z)=(x+y,x-y,z), all sums mod3.
-- The z axis is the selected sheet index, not a modular exponent.
modularSheetAction : Cube.Ternary27Point → Cube.Ternary27Point
modularSheetAction (Cube.ternary27Point x y z) =
  Cube.ternary27Point
    (fromKernel (M3.add3 (toKernel x) (toKernel y)))
    (fromKernel
      (M3.add3 (toKernel x)
        (Triadic.negateTrit (toKernel y))))
    z

-- This map is literally the old M3 action on every nine-position
-- xy-sheet; not a newly assigned 27-cycle.
cubeSheetActionAgreesWithPrior9 :
  (p : Cube.Ternary27Point) →
  xySheet (modularSheetAction p) ≡
  M3.modularMatrixOnNine (xySheet p)
cubeSheetActionAgreesWithPrior9 (Cube.ternary27Point x y z)
  rewrite toFromKernel (M3.add3 (toKernel x) (toKernel y))
        | toFromKernel
            (M3.add3 (toKernel x)
              (Triadic.negateTrit (toKernel y))) = refl

cubeModularPreservesZ :
  (p : Cube.Ternary27Point) →
  Cube.z (modularSheetAction p) ≡ Cube.z p
cubeModularPreservesZ (Cube.ternary27Point x y z) = refl

negateSSP : SSP.SSPTrit → SSP.SSPTrit
negateSSP SSP.sspNegOne = SSP.sspPosOne
negateSSP SSP.sspZero = SSP.sspZero
negateSSP SSP.sspPosOne = SSP.sspNegOne

xyAntipodal : Cube.Ternary27Point → Cube.Ternary27Point
xyAntipodal (Cube.ternary27Point x y z) =
  Cube.ternary27Point (negateSSP x) (negateSSP y) z

cubeModularSquareIsXYAntipodal :
  (x y z : SSP.SSPTrit) →
  modularSheetAction
    (modularSheetAction (Cube.ternary27Point x y z))
  ≡ xyAntipodal (Cube.ternary27Point x y z)
cubeModularSquareIsXYAntipodal SSP.sspNegOne SSP.sspNegOne z = refl
cubeModularSquareIsXYAntipodal SSP.sspNegOne SSP.sspZero z = refl
cubeModularSquareIsXYAntipodal SSP.sspNegOne SSP.sspPosOne z = refl
cubeModularSquareIsXYAntipodal SSP.sspZero SSP.sspNegOne z = refl
cubeModularSquareIsXYAntipodal SSP.sspZero SSP.sspZero z = refl
cubeModularSquareIsXYAntipodal SSP.sspZero SSP.sspPosOne z = refl
cubeModularSquareIsXYAntipodal SSP.sspPosOne SSP.sspNegOne z = refl
cubeModularSquareIsXYAntipodal SSP.sspPosOne SSP.sspZero z = refl
cubeModularSquareIsXYAntipodal SSP.sspPosOne SSP.sspPosOne z = refl

cubeModularFourthIsIdentity :
  (x y z : SSP.SSPTrit) →
  modularSheetAction (modularSheetAction
    (modularSheetAction (modularSheetAction
      (Cube.ternary27Point x y z))))
  ≡ Cube.ternary27Point x y z
cubeModularFourthIsIdentity SSP.sspNegOne SSP.sspNegOne z = refl
cubeModularFourthIsIdentity SSP.sspNegOne SSP.sspZero z = refl
cubeModularFourthIsIdentity SSP.sspNegOne SSP.sspPosOne z = refl
cubeModularFourthIsIdentity SSP.sspZero SSP.sspNegOne z = refl
cubeModularFourthIsIdentity SSP.sspZero SSP.sspZero z = refl
cubeModularFourthIsIdentity SSP.sspZero SSP.sspPosOne z = refl
cubeModularFourthIsIdentity SSP.sspPosOne SSP.sspNegOne z = refl
cubeModularFourthIsIdentity SSP.sspPosOne SSP.sspZero z = refl
cubeModularFourthIsIdentity SSP.sspPosOne SSP.sspPosOne z = refl

-- However: origin -> +x is a native cube EDGE, while its M image
-- origin -> (+x,+y,0) changes TWO coordinates simultaneously.
-- The modular action is not a cube grid-graph automorphism.
nativeOriginToPositiveXIsEdge :
  Cube.HypervoxelAdjacent Cube.origin
    (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero)
nativeOriginToPositiveXIsEdge = Cube.originAdjacentPositiveX

modularImageOfNativeEdgeNotAnEdge :
  Cube.HypervoxelAdjacent
    (modularSheetAction Cube.origin)
    (modularSheetAction
      (Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero))
  → ⊥
modularImageOfNativeEdgeNotAnEdge ()

-- Orbit counts for each z sheet: one (0,0,z) fixed and two
-- 4-cycles among its eight noncentral xy sites. Therefore on the
-- full cube: three fixed axial sites and six 4-cycles, NOT one C27.
