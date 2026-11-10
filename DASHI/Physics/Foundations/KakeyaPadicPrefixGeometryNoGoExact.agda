module DASHI.Physics.Foundations.KakeyaPadicPrefixGeometryNoGoExact where

------------------------------------------------------------------------
-- ORIGINAL CARRIER, ORIGINAL METRIC, NONINJECTIVE REFINEMENT.
--
-- Reuses the original DASHI.SSP369Ultrametric distance and the
-- original PadicCylinderLODReasoningField prefix/refine/voxel maps.
-- Unlike a general record with an uninhabited source, the witnesses
-- below are literal original addresses and reduce by computation.
--
-- Results: a genuine source-level counterexample to a global exact
-- coarse-prefix isometry and a constructed finite collinear voxel
-- sample. The latter is NOT the all-directions Euclidean Kakeya
-- property. No physical (TSFV/KK) metric is invented.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Vec using ([]; _∷_) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Geometry.SSP369Ultrametric as Ultra
import DASHI.Biology.PadicCylinderLODReasoningField as Cylinder

parent : Cylinder.DepthOneAddress
parent = Ultra.digit3 vcons vnil

fine3 fine6 fine9 : Cylinder.DepthTwoAddress
fine3 = Cylinder.refineOne parent Ultra.digit3
fine6 = Cylinder.refineOne parent Ultra.digit6
fine9 = Cylinder.refineOne parent Ultra.digit9

fine3NotFine6 : fine3 ≡ fine6 → ⊥
fine3NotFine6 ()

fine3NotFine9 : fine3 ≡ fine9 → ⊥
fine3NotFine9 ()

fine6NotFine9 : fine6 ≡ fine9 → ⊥
fine6NotFine9 ()

sameOriginalParent36 :
  Cylinder.prefixTwoToOne fine3 ≡ Cylinder.prefixTwoToOne fine6
sameOriginalParent36 = refl

sameOriginalParent39 :
  Cylinder.prefixTwoToOne fine3 ≡ Cylinder.prefixTwoToOne fine9
sameOriginalParent39 = refl

sameOriginalParent69 :
  Cylinder.prefixTwoToOne fine6 ≡ Cylinder.prefixTwoToOne fine9
sameOriginalParent69 = refl

-- The distance of two distinct original depth-two cylinders is 1;
-- the coarse distance of their identical original parent is 0.
fineDistance36IsOne : Ultra.distance fine3 fine6 ≡ 1
fineDistance36IsOne = refl

coarseDistance36IsZero :
  Ultra.distance
    (Cylinder.prefixTwoToOne fine3)
    (Cylinder.prefixTwoToOne fine6) ≡ 0
coarseDistance36IsZero = refl

-- An exact same-distance factorisation through original prefix
-- truncation contradicts those two COMPUTED values.
noExactOriginalPrefixMetricIsometry :
  (∀ x y →
    Ultra.distance x y ≡
      Ultra.distance
        (Cylinder.prefixTwoToOne x)
        (Cylinder.prefixTwoToOne y)) → ⊥
noExactOriginalPrefixMetricIsometry h with h fine3 fine6
... | ()

-- The actual selected original prefix map is not injective.
noOriginalPrefixInjectivity :
  (∀ x y →
    Cylinder.prefixTwoToOne x ≡ Cylinder.prefixTwoToOne y →
    x ≡ y) → ⊥
noOriginalPrefixInjectivity assumed =
  fine3NotFine6 (assumed fine3 fine6 sameOriginalParent36)

-- The ORIGINAL Morton-style voxel observation nevertheless supplies
-- a useful finite straight-line *sample*, not an ultrametric isometry.
-- These are the three children along the last spatial voxel coordinate.
voxel3 voxel6 voxel9 : Cylinder.Voxel3
voxel3 = Cylinder.embedDepthThree
  (Ultra.digit3 vcons Ultra.digit6 vcons Ultra.digit3 vcons vnil)
voxel6 = Cylinder.embedDepthThree
  (Ultra.digit3 vcons Ultra.digit6 vcons Ultra.digit6 vcons vnil)
voxel9 = Cylinder.embedDepthThree
  (Ultra.digit3 vcons Ultra.digit6 vcons Ultra.digit9 vcons vnil)

voxel3SourceIsOriginal : voxel3 ≡ Cylinder.voxel3 0 1 0
voxel3SourceIsOriginal = refl

voxel6SourceIsOriginal : voxel6 ≡ Cylinder.voxel3 0 1 1
voxel6SourceIsOriginal = refl

voxel9SourceIsOriginal : voxel9 ≡ Cylinder.voxel3 0 1 2
voxel9SourceIsOriginal = refl

voxelLineX :
  Cylinder.voxelX voxel3 ≡ Cylinder.voxelX voxel6
voxelLineX = refl

voxelLineY :
  Cylinder.voxelY voxel3 ≡ Cylinder.voxelY voxel6
voxelLineY = refl

voxelLineArithmeticProgression :
  2 * Cylinder.voxelZ voxel6 ≡
    Cylinder.voxelZ voxel3 + Cylinder.voxelZ voxel9
voxelLineArithmeticProgression = refl

-- This finite voxel line does not claim any unit segment in every
-- Euclidean direction. Physical continuum metric and line transport
-- must still be established from original observer/YM/KK evidence.
