module DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixDimensionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List.Base using (length)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

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

lengthProductFiniteExact :
  ∀ {A B : Set} (finiteA : FiniteEnumeration A) (finiteB : FiniteEnumeration B) →
  length (elements (productFinite finiteA finiteB))
  ≡ length (elements finiteA) * length (elements finiteB)
lengthProductFiniteExact finiteA finiteB =
  lengthCartesianExact (elements finiteA) (elements finiteB)

componentCountExact : length componentElements ≡ 3
componentCountExact = refl

axisCountExact : length (allCyclicIndices four) ≡ 4
axisCountExact = lengthAllCyclicIndices four

pair2CountExact : length (elements pair2FourFinite) ≡ 16
pair2CountExact =
  trans
    (lengthProductFiniteExact (cyclicIndexFinite four) (cyclicIndexFinite four))
    (cong₂ _*_ axisCountExact axisCountExact)

siteCountExact :
  length (elements (periodicTorus4Finite four)) ≡ 256
siteCountExact =
  trans
    (lengthProductFiniteExact pair2FourFinite pair2FourFinite)
    (cong₂ _*_ pair2CountExact pair2CountExact)

positiveBondCountExact :
  length (elements positiveBondFinite) ≡ 1024
positiveBondCountExact =
  trans
    (lengthProductFiniteExact (periodicTorus4Finite four) (cyclicIndexFinite four))
    (cong₂ _*_ siteCountExact axisCountExact)

physicalCoordinateCountExact :
  length (elements physicalCoordinateFinite) ≡ 3072
physicalCoordinateCountExact =
  trans
    (lengthProductFiniteExact componentFinite positiveBondFinite)
    (cong₂ _*_ componentCountExact positiveBondCountExact)

configuredMatrixDimension : Nat
configuredMatrixDimension = length (elements physicalCoordinateFinite)

configuredMatrixDimensionIs3072 : configuredMatrixDimension ≡ 3072
configuredMatrixDimensionIs3072 = physicalCoordinateCountExact

finiteCartesianLengthLevel : ProofLevel
finiteCartesianLengthLevel = machineChecked

configuredPhysicalMatrixDimensionLevel : ProofLevel
configuredPhysicalMatrixDimensionLevel = machineChecked
