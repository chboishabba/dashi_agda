module DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixDimensionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (length)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanFourDimensionalHaloOverlapExact using
  (lengthAllCyclicIndices)
open import DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixCoordinatesExact

------------------------------------------------------------------------
-- Literal list-cardinality calculus for the nested Cartesian enumerator.
------------------------------------------------------------------------

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

componentCountExact : length componentElements ≡ 3
componentCountExact = refl

axisCountExact : length (allCyclicIndices four) ≡ 4
axisCountExact = lengthAllCyclicIndices four

siteCountExact :
  length (elements (periodicTorus4Finite four)) ≡ 256
siteCountExact
  rewrite lengthCartesianExact
      (cartesian (allCyclicIndices four) (allCyclicIndices four))
      (cartesian (allCyclicIndices four) (allCyclicIndices four))
        | lengthCartesianExact
            (allCyclicIndices four) (allCyclicIndices four)
        | lengthAllCyclicIndices four = refl

positiveBondCountExact :
  length (elements positiveBondFinite) ≡ 1024
positiveBondCountExact
  rewrite lengthCartesianExact
      (elements (periodicTorus4Finite four))
      (allCyclicIndices four)
        | siteCountExact
        | lengthAllCyclicIndices four = refl

physicalCoordinateCountExact :
  length (elements physicalCoordinateFinite) ≡ 3072
physicalCoordinateCountExact
  rewrite lengthCartesianExact componentElements (elements positiveBondFinite)
        | componentCountExact
        | positiveBondCountExact = refl

configuredMatrixDimension : Nat
configuredMatrixDimension = length (elements physicalCoordinateFinite)

configuredMatrixDimensionIs3072 : configuredMatrixDimension ≡ 3072
configuredMatrixDimensionIs3072 = physicalCoordinateCountExact

finiteCartesianLengthLevel : ProofLevel
finiteCartesianLengthLevel = machineChecked

configuredPhysicalMatrixDimensionLevel : ProofLevel
configuredPhysicalMatrixDimensionLevel = machineChecked
