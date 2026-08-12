module DASHI.Physics.YangMills.BalabanPath13SU2RationalMatrixDimensionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Count the newly generalized source-admissible physical state carrier rather
-- than quoting the earlier mismatch arithmetic.  The literal nested Cartesian
-- enumeration has
--
--       13^4 = 28561 sites,
--       4*13^4 = 114244 positive bonds,
--       3*4*13^4 = 342732 su(2) scalar coordinates.
--
-- Thus subsequent L=13 KKT matrices can use the exact same enumerated carrier
-- whose size caused the side-four no-go, with no hidden 3072-coordinate reuse.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.List.Base using (length)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact using
  (lengthAllCyclicIndices)
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanPhysicalSU2RationalMatrixCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanPath13NormalizedAxisAverageExact as Side13

lengthMapExact :
  ∀ {A B : Set} (function : A → B) (values : List A) →
  length (map function values) ≡ length values
lengthMapExact function [] = refl
lengthMapExact function (value ∷ values)
  rewrite lengthMapExact function values = refl

lengthAppendExact :
  ∀ {A : Set} (left right : List A) →
  length (left ++ right) ≡ length left + length right
lengthAppendExact [] right = refl
lengthAppendExact (value ∷ values) right
  rewrite lengthAppendExact values right = refl

lengthCartesianExact :
  ∀ {A B : Set} (left : List A) (right : List B) →
  length (cartesian left right) ≡ length left * length right
lengthCartesianExact [] right = refl
lengthCartesianExact (value ∷ values) right
  rewrite lengthAppendExact
      (map (λ item → pair value item) right)
      (cartesian values right)
        | lengthMapExact (λ item → pair value item) right
        | lengthCartesianExact values right = refl

lieCoordinateCountExact : length Physical.lieCoordinates3 ≡ 3
lieCoordinateCountExact = refl

axisCountExact : length (allCyclicIndices four) ≡ 4
axisCountExact = lengthAllCyclicIndices four

side13IndexCountExact :
  length (allCyclicIndices Side13.side13) ≡ 13
side13IndexCountExact = lengthAllCyclicIndices Side13.side13

siteCountExact :
  length (elements (periodicTorus4Finite Side13.side13)) ≡ 28561
siteCountExact
  rewrite lengthCartesianExact
      (cartesian
        (allCyclicIndices Side13.side13)
        (allCyclicIndices Side13.side13))
      (cartesian
        (allCyclicIndices Side13.side13)
        (allCyclicIndices Side13.side13))
        | lengthCartesianExact
            (allCyclicIndices Side13.side13)
            (allCyclicIndices Side13.side13)
        | side13IndexCountExact = refl

bondCellCountExact :
  length (elements
    (productFinite
      (cyclicIndexFinite four)
      (periodicTorus4Finite Side13.side13))) ≡ 114244
bondCellCountExact
  rewrite lengthCartesianExact
      (allCyclicIndices four)
      (elements (periodicTorus4Finite Side13.side13))
        | axisCountExact
        | siteCountExact = refl

physicalCoordinateCountExact :
  length (elements (Coordinates.physicalCoordinateFinite Side13.side13))
  ≡ 342732
physicalCoordinateCountExact
  rewrite lengthCartesianExact Physical.lieCoordinates3
      (elements
        (productFinite
          (cyclicIndexFinite four)
          (periodicTorus4Finite Side13.side13)))
        | lieCoordinateCountExact
        | bondCellCountExact = refl

path13PhysicalMatrixDimension : Nat
path13PhysicalMatrixDimension =
  length (elements (Coordinates.physicalCoordinateFinite Side13.side13))

path13PhysicalMatrixDimensionIs342732 :
  path13PhysicalMatrixDimension ≡ 342732
path13PhysicalMatrixDimensionIs342732 = physicalCoordinateCountExact

path13PhysicalMatrixDimensionLevel : ProofLevel
path13PhysicalMatrixDimensionLevel = machineChecked
