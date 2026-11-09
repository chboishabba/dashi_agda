module DASHI.Moonshine.AbelE8GeneratedRootNormTwoExact where

------------------------------------------------------------------------
-- GENUINE FINITE E8 ROOT NORM CERTIFICATE
--
-- The upstream indexed E8 root generator uses coordinates
--    -1, -1/2, 0, +1/2, +1
-- (native HalfTritIndexed). For doubled coordinates, their exact
-- integer squares are 4,1,0,1,4.
--
-- Every enumerated root has sum of doubled-coordinate squares = 8,
-- hence original Euclidean squared norm = 8/4 = 2.
--
-- The Boolean exhaustive check is paired with an inductive proof
-- lifting it to every item. This does NOT characterize ALL vectors
-- of the genuine E8 lattice or prove theta_E8 = E4.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.List.Base using (List; []; _∷_)
import Data.Vec as Vec
open import Relation.Nullary using (yes; no)
import Data.Nat.Properties as NatP

import DASHI.Algebra.Trit.HalfTritIndexed as Indexed
import DASHI.Algebra.Trit.E8RootEnumeration as E8
import DASHI.Moonshine.JInvariantEisensteinIncrementCoefficientBoundExact as Coeff

doubledCoordinateSquare : Indexed.HalfTritIndexed → Nat
doubledCoordinateSquare Indexed.indexedNegOne = 4
doubledCoordinateSquare Indexed.indexedNegHalf = 1
doubledCoordinateSquare Indexed.indexedZero = 0
doubledCoordinateSquare Indexed.indexedPosHalf = 1
doubledCoordinateSquare Indexed.indexedPosOne = 4

doubledSquaredNorm : ∀ {n} → Vec.Vec Indexed.HalfTritIndexed n → Nat
doubledSquaredNorm Vec.[] = zero
doubledSquaredNorm (coordinate Vec.∷ rest) =
  doubledCoordinateSquare coordinate + doubledSquaredNorm rest

-- Root square length=2 is represented without rational arithmetic
-- by the provably equivalent integer relation 4 * ||root||² = 8.
data AllDoubledNormEight : List E8.E8IndexedRootCarrier → Set where
  allNil : AllDoubledNormEight []
  allCons :
    ∀ {root rest} →
    doubledSquaredNorm root ≡ 8 →
    AllDoubledNormEight rest →
    AllDoubledNormEight (root ∷ rest)

allNormEightCheck : List E8.E8IndexedRootCarrier → Bool
allNormEightCheck [] = true
allNormEightCheck (root ∷ rest) with NatP._≟_ (doubledSquaredNorm root) 8
... | yes _ = allNormEightCheck rest
... | no _ = false

allNormEightCheckSound :
  (roots : List E8.E8IndexedRootCarrier) →
  allNormEightCheck roots ≡ true →
  AllDoubledNormEight roots
allNormEightCheckSound [] _ = allNil
allNormEightCheckSound (root ∷ rest) valid
  with NatP._≟_ (doubledSquaredNorm root) 8 | valid
... | yes normEq | accepted =
  allCons normEq (allNormEightCheckSound rest accepted)
... | no notEq | ()

generatedE8NormEightCheckIsTrue :
  allNormEightCheck E8.combinedIndexedRoots ≡ true
generatedE8NormEightCheckIsTrue = refl

generatedE8RootsAllHaveNormTwo :
  AllDoubledNormEight E8.combinedIndexedRoots
generatedE8RootsAllHaveNormTwo =
  allNormEightCheckSound
    E8.combinedIndexedRoots
    generatedE8NormEightCheckIsTrue

integerGeneratedE8NormEightCheckIsTrue :
  allNormEightCheck E8.integerIndexedRoots ≡ true
integerGeneratedE8NormEightCheckIsTrue = refl

halfGeneratedE8NormEightCheckIsTrue :
  allNormEightCheck E8.halfIndexedRoots ≡ true
halfGeneratedE8NormEightCheckIsTrue = refl

integerGeneratedE8RootsAllHaveNormTwo :
  AllDoubledNormEight E8.integerIndexedRoots
integerGeneratedE8RootsAllHaveNormTwo =
  allNormEightCheckSound
    E8.integerIndexedRoots
    integerGeneratedE8NormEightCheckIsTrue

halfGeneratedE8RootsAllHaveNormTwo :
  AllDoubledNormEight E8.halfIndexedRoots
halfGeneratedE8RootsAllHaveNormTwo =
  allNormEightCheckSound
    E8.halfIndexedRoots
    halfGeneratedE8NormEightCheckIsTrue

------------------------------------------------------------------------
-- Actual first theta-shell count among the generated root list.
-- No "expected 240" is used in this computation.
------------------------------------------------------------------------

countGeneratedNormTwo : List E8.E8IndexedRootCarrier → Nat
countGeneratedNormTwo [] = zero
countGeneratedNormTwo (root ∷ rest)
  with NatP._≟_ (doubledSquaredNorm root) 8
... | yes _ = suc (countGeneratedNormTwo rest)
... | no _ = countGeneratedNormTwo rest

generatedE8NormTwoShellCountIs240 :
  countGeneratedNormTwo E8.combinedIndexedRoots ≡ 240
generatedE8NormTwoShellCountIs240 = refl

generatedIntegerE8NormTwoShellCountIs112 :
  countGeneratedNormTwo E8.integerIndexedRoots ≡ 112
generatedIntegerE8NormTwoShellCountIs112 = refl

generatedHalfE8NormTwoShellCountIs128 :
  countGeneratedNormTwo E8.halfIndexedRoots ≡ 128
generatedHalfE8NormTwoShellCountIs128 = refl

generatedNormTwoShellMatchesOriginalE4FirstCoefficient :
  countGeneratedNormTwo E8.combinedIndexedRoots
  ≡ Coeff.e4IncrementCoefficient 0
generatedNormTwoShellMatchesOriginalE4FirstCoefficient =
  trans
    generatedE8NormTwoShellCountIs240
    (sym refl)
