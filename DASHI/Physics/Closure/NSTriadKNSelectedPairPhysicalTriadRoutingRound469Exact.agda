module DASHI.Physics.Closure.NSTriadKNSelectedPairPhysicalTriadRoutingRound469Exact where

------------------------------------------------------------------------
-- ROUND469 / R109 CARTESIAN SELECTOR = LITERAL PHYSICAL-TRIAD FOLD
--
-- The physical triad enumeration is definitionally obtained from
--
--   cutoffModes N x cutoffModes N
--
-- by retaining exactly those ordered pairs whose output p+q remains inside the
-- same cutoff.  R109 independently folds an arbitrary Boolean selector over
-- that same cartesian pair family.
--
-- This module proves the exact finite routing identity between those carriers.
-- For a selector chi(p,q), strengthen it only by output admissibility:
--
--   chi_N(p,q) = outputInCutoff_N(p+q) AND chi(p,q).
--
-- Then R109's selected pair sum is exactly the scalar fold over the selected
-- literal physical triads. R39 may regroup that fold by output fibres with no
-- cardinality factor and no caller-supplied global partition equality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (map)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergyDissipationProductRound109Exact as R109
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNF4GlobalOutputFiberPartitionRound39Exact as R39

outputFilteredSelect :
  Nat →
  (Z3.FourierMode → Z3.FourierMode → Bool) →
  Z3.FourierMode → Z3.FourierMode → Bool
outputFilteredSelect cutoff select left right =
  Physical._&&_
    (Physical.modeWithinCutoff cutoff (Z3.addMode left right))
    (select left right)

selectedTriadValue :
  R109.ModalEnergyDissipation Z3.FourierMode →
  (Z3.FourierMode → Z3.FourierMode → Bool) →
  Physical.PhysicalTriadIncidence → ℚ
selectedTriadValue M select tau with select (Physical.p tau) (Physical.q tau)
... | true = R109.pairKernel M (Physical.p tau) (Physical.q tau)
... | false = 0ℚ

pairValue :
  R109.ModalEnergyDissipation Z3.FourierMode →
  Nat →
  (Z3.FourierMode → Z3.FourierMode → Bool) →
  Cube.Pair Z3.FourierMode Z3.FourierMode → ℚ
pairValue M cutoff select pair
  with Physical.modeWithinCutoff cutoff
    (Z3.addMode (Cube.first pair) (Cube.second pair))
... | false = 0ℚ
... | true with select (Cube.first pair) (Cube.second pair)
...   | true = R109.pairKernel M (Cube.first pair) (Cube.second pair)
...   | false = 0ℚ

pairFold :
  (Cube.Pair Z3.FourierMode Z3.FourierMode → ℚ) →
  List (Cube.Pair Z3.FourierMode Z3.FourierMode) → ℚ
pairFold value [] = 0ℚ
pairFold value (pair ∷ rest) = value pair + pairFold value rest

pairFoldAppend :
  (value : Cube.Pair Z3.FourierMode Z3.FourierMode → ℚ) →
  (left right : List (Cube.Pair Z3.FourierMode Z3.FourierMode)) →
  pairFold value (Cube._++_ left right)
  ≡ pairFold value left + pairFold value right
pairFoldAppend value [] right = sym (ℚP.+-identityˡ (pairFold value right))
pairFoldAppend value (pair ∷ left) right =
  trans
    (cong (value pair +_) (pairFoldAppend value left right))
    (ℚP.+-assoc (value pair) (pairFold value left) (pairFold value right))

selectedInnerIsMappedPairFold :
  (M : R109.ModalEnergyDissipation Z3.FourierMode) →
  (cutoff : Nat) →
  (select : Z3.FourierMode → Z3.FourierMode → Bool) →
  (left : Z3.FourierMode) →
  (rights : List Z3.FourierMode) →
  R109.selectedInner M (outputFilteredSelect cutoff select) left rights
  ≡ pairFold (pairValue M cutoff select)
      (map (λ right → Cube.pair left right) rights)
selectedInnerIsMappedPairFold M cutoff select left [] = refl
selectedInnerIsMappedPairFold M cutoff select left (right ∷ rest)
  with Physical.modeWithinCutoff cutoff (Z3.addMode left right)
... | false = selectedInnerIsMappedPairFold M cutoff select left rest
... | true with select left right
...   | false = selectedInnerIsMappedPairFold M cutoff select left rest
...   | true =
  cong (R109.pairKernel M left right +_)
    (selectedInnerIsMappedPairFold M cutoff select left rest)

selectedOrderedPairSumIsCartesianFold :
  (M : R109.ModalEnergyDissipation Z3.FourierMode) →
  (cutoff : Nat) →
  (select : Z3.FourierMode → Z3.FourierMode → Bool) →
  (lefts rights : List Z3.FourierMode) →
  R109.selectedOrderedPairSum M (outputFilteredSelect cutoff select) lefts rights
  ≡ pairFold (pairValue M cutoff select) (Cube.cartesian lefts rights)
selectedOrderedPairSumIsCartesianFold M cutoff select [] rights = refl
selectedOrderedPairSumIsCartesianFold M cutoff select (left ∷ lefts) rights =
  trans
    (cong₂ _+_
      (selectedInnerIsMappedPairFold M cutoff select left rights)
      (selectedOrderedPairSumIsCartesianFold M cutoff select lefts rights))
    (sym
      (pairFoldAppend (pairValue M cutoff select)
        (map (λ right → Cube.pair left right) rights)
        (Cube.cartesian lefts rights)))
  where
  cong₂ : ∀ {A B C : Set} (f : A → B → C) {a a' b b'} →
    a ≡ a' → b ≡ b' → f a b ≡ f a' b'
  cong₂ f refl refl = refl

pairFoldIsEnumeratedTriadFold :
  (M : R109.ModalEnergyDissipation Z3.FourierMode) →
  (cutoff : Nat) →
  (select : Z3.FourierMode → Z3.FourierMode → Bool) →
  (pairs : List (Cube.Pair Z3.FourierMode Z3.FourierMode)) →
  pairFold (pairValue M cutoff select) pairs
  ≡ R38.foldPower (selectedTriadValue M select)
      (Physical.enumerateFromPairs cutoff pairs)
pairFoldIsEnumeratedTriadFold M cutoff select [] = refl
pairFoldIsEnumeratedTriadFold M cutoff select (pair ∷ pairs)
  with Physical.modeWithinCutoff cutoff
    (Z3.addMode (Cube.first pair) (Cube.second pair))
... | false =
  trans
    (ℚP.+-identityˡ (pairFold (pairValue M cutoff select) pairs))
    (pairFoldIsEnumeratedTriadFold M cutoff select pairs)
... | true with select (Cube.first pair) (Cube.second pair)
...   | true =
  cong (R109.pairKernel M (Cube.first pair) (Cube.second pair) +_)
    (pairFoldIsEnumeratedTriadFold M cutoff select pairs)
...   | false =
  trans
    (ℚP.+-identityˡ (pairFold (pairValue M cutoff select) pairs))
    (pairFoldIsEnumeratedTriadFold M cutoff select pairs)

selectedPairsEqualPhysicalTriadFold :
  (M : R109.ModalEnergyDissipation Z3.FourierMode) →
  (cutoff : Nat) →
  (select : Z3.FourierMode → Z3.FourierMode → Bool) →
  let modes = Cube.cutoffModes cutoff
  in
  R109.selectedOrderedPairSum M
      (outputFilteredSelect cutoff select) modes modes
  ≡ R38.foldPower (selectedTriadValue M select)
      (Physical.physicalTriadEnumeration cutoff)
selectedPairsEqualPhysicalTriadFold M cutoff select =
  trans
    (selectedOrderedPairSumIsCartesianFold M cutoff select
      (Cube.cutoffModes cutoff) (Cube.cutoffModes cutoff))
    (pairFoldIsEnumeratedTriadFold M cutoff select
      (Cube.cartesian (Cube.cutoffModes cutoff) (Cube.cutoffModes cutoff)))

selectedPairsEqualOutputFibrePartitionFold :
  (M : R109.ModalEnergyDissipation Z3.FourierMode) →
  (cutoff : Nat) →
  (select : Z3.FourierMode → Z3.FourierMode → Bool) →
  let modes = Cube.cutoffModes cutoff
      value = selectedTriadValue M select
  in
  R109.selectedOrderedPairSum M
      (outputFilteredSelect cutoff select) modes modes
  ≡ R38.foldPower value
      (R39.concatOutputFibers cutoff modes)
selectedPairsEqualOutputFibrePartitionFold M cutoff select =
  trans
    (selectedPairsEqualPhysicalTriadFold M cutoff select)
    (sym
      (R38.foldPermutationInvariant
        (selectedTriadValue M select)
        (R39.literalOutputPartitionPermutation cutoff)))

round469R109CartesianToPhysicalTriadFoldClosed : Bool
round469R109CartesianToPhysicalTriadFoldClosed = true

round469PhysicalTriadFoldToOutputFibresClosed : Bool
round469PhysicalTriadFoldToOutputFibresClosed = true

round469CallerSuppliedGlobalPartitionEqualityRequired : Bool
round469CallerSuppliedGlobalPartitionEqualityRequired = false

round469ContainsPostulate : Bool
round469ContainsPostulate = false

round469PackageAClosed : Bool
round469PackageAClosed = false

round469ClayPromotion : Bool
round469ClayPromotion = false

round469CallerSuppliedGlobalPartitionEqualityRequiredIsFalse :
  round469CallerSuppliedGlobalPartitionEqualityRequired ≡ false
round469CallerSuppliedGlobalPartitionEqualityRequiredIsFalse = refl

round469ContainsPostulateIsFalse : round469ContainsPostulate ≡ false
round469ContainsPostulateIsFalse = refl
