module DASHI.Biology.IITCubePermutationStabilizer18Exact where

------------------------------------------------------------------------
-- EXPLICIT 18-NORMAL-FORM PERMUTATION SPINE INSIDE THE CUBE STABILIZER
--
-- The diagonal stabilizer owner already proves
--
--   PreservesGraph T  <->  CommutesWithB T
--
-- and exhibits row/column order-three translations plus transpose, with
-- transpose exchanging row and column translation.  This owner packages all
-- 3 x 3 x 2 normal forms as actual face endomorphisms and proves every one
-- preserves the concrete cube graph by closure of the centralizer.
--
-- A separate finite Python receipt checks that the 18 induced permutation
-- matrices are distinct and closed with the expected C3^2 semidirect-C2 law.
-- This Agda owner does not claim the 18 permutations exhaust the full linear
-- centralizer; the latter has independently verified dimension 27 over F3.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IITCubeConcreteTorusImageExact as Cube
import DASHI.Biology.IITCubeDiagonalStabilizerExact as Stabilizer

------------------------------------------------------------------------
-- 1. Composition closure for graph-preserving centralizer endomorphisms.
------------------------------------------------------------------------

composeEndo :
  Stabilizer.FaceLinearEndo →
  Stabilizer.FaceLinearEndo →
  Stabilizer.FaceLinearEndo
composeEndo T U = Stabilizer.face-linear-endo
  (λ x → Stabilizer.map T (Stabilizer.map U x))
  (trans (cong (Stabilizer.map T) (Stabilizer.mapZero U)) (Stabilizer.mapZero T))
  (λ x y →
    trans
      (cong (Stabilizer.map T) (Stabilizer.mapSub U x y))
      (Stabilizer.mapSub T (Stabilizer.map U x) (Stabilizer.map U y)))

composeCommutesWithB :
  (T U : Stabilizer.FaceLinearEndo) →
  Stabilizer.CommutesWithB T →
  Stabilizer.CommutesWithB U →
  Stabilizer.CommutesWithB (composeEndo T U)
composeCommutesWithB T U commT commU f =
  trans
    (cong (Stabilizer.map T) (commU f))
    (commT (Stabilizer.map U f))

composePreservesGraph :
  (T U : Stabilizer.FaceLinearEndo) →
  Stabilizer.CommutesWithB T →
  Stabilizer.CommutesWithB U →
  Stabilizer.PreservesGraph (composeEndo T U)
composePreservesGraph T U commT commU =
  Stabilizer.centralizerPreservesGraph
    (composeEndo T U)
    (composeCommutesWithB T U commT commU)

------------------------------------------------------------------------
-- 2. Three translation powers in each direction.
------------------------------------------------------------------------

data Shift3 : Set where
  shift0 shift1 shift2 : Shift3

rowPowerEndo : Shift3 → Stabilizer.FaceLinearEndo
rowPowerEndo shift0 = Stabilizer.identityFaceEndo
rowPowerEndo shift1 = Stabilizer.rowShiftEndo
rowPowerEndo shift2 = composeEndo Stabilizer.rowShiftEndo Stabilizer.rowShiftEndo

columnPowerEndo : Shift3 → Stabilizer.FaceLinearEndo
columnPowerEndo shift0 = Stabilizer.identityFaceEndo
columnPowerEndo shift1 = Stabilizer.columnShiftEndo
columnPowerEndo shift2 = composeEndo Stabilizer.columnShiftEndo Stabilizer.columnShiftEndo

rowPowerCommutes :
  (shift : Shift3) → Stabilizer.CommutesWithB (rowPowerEndo shift)
rowPowerCommutes shift0 = Stabilizer.identityCommutesWithB
rowPowerCommutes shift1 = Stabilizer.rowShiftCommutesWithB
rowPowerCommutes shift2 =
  composeCommutesWithB
    Stabilizer.rowShiftEndo Stabilizer.rowShiftEndo
    Stabilizer.rowShiftCommutesWithB Stabilizer.rowShiftCommutesWithB

columnPowerCommutes :
  (shift : Shift3) → Stabilizer.CommutesWithB (columnPowerEndo shift)
columnPowerCommutes shift0 = Stabilizer.identityCommutesWithB
columnPowerCommutes shift1 = Stabilizer.columnShiftCommutesWithB
columnPowerCommutes shift2 =
  composeCommutesWithB
    Stabilizer.columnShiftEndo Stabilizer.columnShiftEndo
    Stabilizer.columnShiftCommutesWithB Stabilizer.columnShiftCommutesWithB

------------------------------------------------------------------------
-- 3. Optional row/column reflection (transpose).
------------------------------------------------------------------------

data Reflection2 : Set where
  direct reflected : Reflection2

reflectionEndo : Reflection2 → Stabilizer.FaceLinearEndo
reflectionEndo direct = Stabilizer.identityFaceEndo
reflectionEndo reflected = Stabilizer.transposeEndo

reflectionCommutes :
  (reflection : Reflection2) →
  Stabilizer.CommutesWithB (reflectionEndo reflection)
reflectionCommutes direct = Stabilizer.identityCommutesWithB
reflectionCommutes reflected = Stabilizer.transposeCommutesWithB

------------------------------------------------------------------------
-- 4. The 3 x 3 x 2 normal-form carrier and its actual action.
------------------------------------------------------------------------

record Permutation18 : Set where
  constructor permutation18
  field
    rowTranslation : Shift3
    columnTranslation : Shift3
    reflection : Reflection2
open Permutation18 public

permutationEndo : Permutation18 → Stabilizer.FaceLinearEndo
permutationEndo g =
  composeEndo
    (rowPowerEndo (rowTranslation g))
    (composeEndo
      (columnPowerEndo (columnTranslation g))
      (reflectionEndo (reflection g)))

permutationCommutesWithB :
  (g : Permutation18) →
  Stabilizer.CommutesWithB (permutationEndo g)
permutationCommutesWithB g =
  composeCommutesWithB
    (rowPowerEndo (rowTranslation g))
    (composeEndo
      (columnPowerEndo (columnTranslation g))
      (reflectionEndo (reflection g)))
    (rowPowerCommutes (rowTranslation g))
    (composeCommutesWithB
      (columnPowerEndo (columnTranslation g))
      (reflectionEndo (reflection g))
      (columnPowerCommutes (columnTranslation g))
      (reflectionCommutes (reflection g)))

permutationPreservesGraph :
  (g : Permutation18) →
  Stabilizer.PreservesGraph (permutationEndo g)
permutationPreservesGraph g =
  Stabilizer.centralizerPreservesGraph
    (permutationEndo g)
    (permutationCommutesWithB g)

actOnFace : Permutation18 → Cube.Face9 → Cube.Face9
actOnFace g = Stabilizer.map (permutationEndo g)

actOnCube : Permutation18 → Cube.CubeFaces → Cube.CubeFaces
actOnCube g = Stabilizer.mapCube (permutationEndo g)

actOnGraph :
  (g : Permutation18) →
  (cube : Cube.CubeFaces) →
  Cube.GraphLaw cube → Cube.GraphLaw (actOnCube g cube)
actOnGraph g = permutationPreservesGraph g

------------------------------------------------------------------------
-- 5. Syntactic normal-form arithmetic for the semidirect-product spine.
------------------------------------------------------------------------

addShift : Shift3 → Shift3 → Shift3
addShift shift0 b = b
addShift shift1 shift0 = shift1
addShift shift1 shift1 = shift2
addShift shift1 shift2 = shift0
addShift shift2 shift0 = shift2
addShift shift2 shift1 = shift0
addShift shift2 shift2 = shift1

swapTranslations : Shift3 → Shift3 → Reflection2 → Shift3 × Shift3
swapTranslations row column direct = row , column
swapTranslations row column reflected = column , row

xorReflection : Reflection2 → Reflection2 → Reflection2
xorReflection direct r = r
xorReflection reflected direct = reflected
xorReflection reflected reflected = direct

multiplyPermutation : Permutation18 → Permutation18 → Permutation18
multiplyPermutation g h =
  permutation18
    (addShift (rowTranslation g) translatedRow)
    (addShift (columnTranslation g) translatedColumn)
    (xorReflection (reflection g) (reflection h))
  where
  translated : Shift3 × Shift3
  translated =
    swapTranslations
      (rowTranslation h)
      (columnTranslation h)
      (reflection g)
  translatedRow : Shift3
  translatedRow = proj₁ translated
  translatedColumn : Shift3
  translatedColumn = proj₂ translated

identityPermutation : Permutation18
identityPermutation = permutation18 shift0 shift0 direct

------------------------------------------------------------------------
-- 6. Authority boundary.
------------------------------------------------------------------------

record PermutationStabilizer18Boundary : Set where
  constructor permutation-stabilizer-18-boundary
  field
    normalFormHasThreeRowChoices : Bool
    normalFormHasThreeColumnChoices : Bool
    normalFormHasTwoReflectionChoices : Bool
    everyNormalFormActsOnConcreteFace : Bool
    everyNormalFormPreservesConcreteCubeGraph : Bool
    transposeExchangesRowAndColumnGenerators : Bool
    normalFormExhaustsFullLinearCentralizer : Bool
    physicalExceptionalSymmetryIdentifiedAutomatically : Bool
open PermutationStabilizer18Boundary public

canonicalPermutationStabilizer18Boundary : PermutationStabilizer18Boundary
canonicalPermutationStabilizer18Boundary =
  permutation-stabilizer-18-boundary
    true true true true true true false false
