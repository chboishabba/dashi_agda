{-# OPTIONS --safe #-}
module DASHI.Combinatorics.GraphColouring369PantsSymmetryCutInvariantExact where

------------------------------------------------------------------------
-- NATIVE S3 / SEAM REFLECTION ACT ON THE *SELECTED* MAX-CUT PARTITION.
--
-- Existing Grid.S3CoordinatePermutation already supplies all six
-- distinct coordinate maps and adjacency preservation; existing
-- Grid.flipSecondPants already supplies the seam reflection.
-- The checkerboard's parity is invariant under EVERY coordinate
-- permutation and under sign-flipping ONE ternary coordinate.
--
-- This is a stronger theorem than "the pullback remains a proper
-- two-colouring": it says the existing selected partition is fixed
-- pointwise as a boolean-valued function. This is NOT invariance of
-- arbitrary asymmetric directed weights, Monster action or a smooth
-- pair-of-pants cobordism.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Topology.TernaryCylinderPantsGeometryExact as Pants
import DASHI.Topology.TernaryPantsFrontierExact as Frontier
import DASHI.Combinatorics.GraphColouring369PantsGridAdjacencyExact as Grid
import DASHI.Combinatorics.GraphColouring369PantsWeightedMaxCutExact as Cut
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as Pants369

middleSlot : Pants.BranchSlot -> Bool
middleSlot s = Grid.middleTrit (Grid.slotToSSP s)

checkerPants : Frontier.PantsPath 3 -> Bool
checkerPants (a vcons b vcons c vcons vnil) =
  Grid.xorBool (Grid.xorBool (middleSlot a) (middleSlot b)) (middleSlot c)

checkerPantsEqualsNativeCut :
  (p : Frontier.PantsPath 3) ->
  checkerPants p ≡ Cut.checkerCut (Pants369.pants3ToVoxel27 p)
checkerPantsEqualsNativeCut
  (Pants.slot3 vcons Pants.slot3 vcons Pants.slot3 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot3 vcons Pants.slot3 vcons Pants.slot6 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot3 vcons Pants.slot3 vcons Pants.slot9 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot3 vcons Pants.slot6 vcons Pants.slot3 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot3 vcons Pants.slot6 vcons Pants.slot6 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot3 vcons Pants.slot6 vcons Pants.slot9 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot3 vcons Pants.slot9 vcons Pants.slot3 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot3 vcons Pants.slot9 vcons Pants.slot6 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot3 vcons Pants.slot9 vcons Pants.slot9 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot6 vcons Pants.slot3 vcons Pants.slot3 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot6 vcons Pants.slot3 vcons Pants.slot6 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot6 vcons Pants.slot3 vcons Pants.slot9 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot6 vcons Pants.slot6 vcons Pants.slot3 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot6 vcons Pants.slot6 vcons Pants.slot6 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot6 vcons Pants.slot6 vcons Pants.slot9 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot6 vcons Pants.slot9 vcons Pants.slot3 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot6 vcons Pants.slot9 vcons Pants.slot6 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot6 vcons Pants.slot9 vcons Pants.slot9 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot9 vcons Pants.slot3 vcons Pants.slot3 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot9 vcons Pants.slot3 vcons Pants.slot6 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot9 vcons Pants.slot3 vcons Pants.slot9 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot9 vcons Pants.slot6 vcons Pants.slot3 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot9 vcons Pants.slot6 vcons Pants.slot6 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot9 vcons Pants.slot6 vcons Pants.slot9 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot9 vcons Pants.slot9 vcons Pants.slot3 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot9 vcons Pants.slot9 vcons Pants.slot6 vcons vnil) = refl
checkerPantsEqualsNativeCut
  (Pants.slot9 vcons Pants.slot9 vcons Pants.slot9 vcons vnil) = refl

xorComm : (a b : Bool) -> Grid.xorBool a b ≡ Grid.xorBool b a
xorComm false false = refl
xorComm false true = refl
xorComm true false = refl
xorComm true true = refl

xorRotate : (a b c : Bool) ->
  Grid.xorBool (Grid.xorBool a b) c ≡
  Grid.xorBool (Grid.xorBool b c) a
xorRotate false false false = refl
xorRotate false false true = refl
xorRotate false true false = refl
xorRotate false true true = refl
xorRotate true false false = refl
xorRotate true false true = refl
xorRotate true true false = refl
xorRotate true true true = refl

swapPreservesChecker :
  (p : Frontier.PantsPath 3) ->
  checkerPants (Grid.swapPantsXY p) ≡ checkerPants p
swapPreservesChecker (a vcons b vcons c vcons vnil)
  rewrite xorComm (middleSlot b) (middleSlot a) = refl

rotatePreservesChecker :
  (p : Frontier.PantsPath 3) ->
  checkerPants (Grid.rotatePants p) ≡ checkerPants p
rotatePreservesChecker (a vcons b vcons c vcons vnil)
  = sym (xorRotate (middleSlot a) (middleSlot b) (middleSlot c))

flipPreservesMiddle : (s : Pants.BranchSlot) ->
  middleSlot (Grid.flipSlot s) ≡ middleSlot s
flipPreservesMiddle Pants.slot3 = refl
flipPreservesMiddle Pants.slot6 = refl
flipPreservesMiddle Pants.slot9 = refl

flipSecondPreservesChecker :
  (p : Frontier.PantsPath 3) ->
  checkerPants (Grid.flipSecondPants p) ≡ checkerPants p
flipSecondPreservesChecker (a vcons b vcons c vcons vnil)
  rewrite flipPreservesMiddle b = refl

s3PreservesSelectedChecker :
  (g : Grid.S3CoordinatePermutation) ->
  (p : Frontier.PantsPath 3) ->
  checkerPants (Grid.actS3Pants g p) ≡ checkerPants p
s3PreservesSelectedChecker Grid.permutationABC p = refl
s3PreservesSelectedChecker Grid.permutationBCA p = rotatePreservesChecker p
s3PreservesSelectedChecker Grid.permutationCAB p =
  trans (rotatePreservesChecker (Grid.rotatePants p))
        (rotatePreservesChecker p)
s3PreservesSelectedChecker Grid.permutationBAC p = swapPreservesChecker p
s3PreservesSelectedChecker Grid.permutationCBA p =
  trans (swapPreservesChecker (Grid.rotatePants p))
        (rotatePreservesChecker p)
s3PreservesSelectedChecker Grid.permutationACB p =
  trans (swapPreservesChecker (Grid.rotatePants (Grid.rotatePants p)))
    (trans (rotatePreservesChecker (Grid.rotatePants p))
           (rotatePreservesChecker p))

-- Same selected partition, not simply "some" two-colouring.
s3PreservesNativeMaxCutPartition :
  (g : Grid.S3CoordinatePermutation) ->
  (p : Frontier.PantsPath 3) ->
  Cut.checkerCut (Pants369.pants3ToVoxel27 (Grid.actS3Pants g p))
  ≡ Cut.checkerCut (Pants369.pants3ToVoxel27 p)
s3PreservesNativeMaxCutPartition g p =
  trans
    (sym (checkerPantsEqualsNativeCut (Grid.actS3Pants g p)))
    (trans (s3PreservesSelectedChecker g p)
           (checkerPantsEqualsNativeCut p))

seamFlipPreservesNativeMaxCutPartition :
  (p : Frontier.PantsPath 3) ->
  Cut.checkerCut (Pants369.pants3ToVoxel27 (Grid.flipSecondPants p))
  ≡ Cut.checkerCut (Pants369.pants3ToVoxel27 p)
seamFlipPreservesNativeMaxCutPartition p =
  trans
    (sym (checkerPantsEqualsNativeCut (Grid.flipSecondPants p)))
    (trans (flipSecondPreservesChecker p)
           (checkerPantsEqualsNativeCut p))

record SymmetryCutInvariantBoundary : Set where
  constructor symmetry-cut-invariant-boundary
  field
    allSixS3KeepSelectedPartition : Bool
    secondCoordinateReflectionKeepsPartition : Bool
    asymmetricWeightsAutomaticallyS3Invariant : Bool
    syntheticTriadicFaceAutomaticallyInvariant : Bool
    exactHeadKernelChecked : Bool

canonicalSymmetryCutInvariantBoundary : SymmetryCutInvariantBoundary
canonicalSymmetryCutInvariantBoundary =
  symmetry-cut-invariant-boundary true true false false false
