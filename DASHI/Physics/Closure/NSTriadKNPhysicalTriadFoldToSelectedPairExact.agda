module DASHI.Physics.Closure.NSTriadKNPhysicalTriadFoldToSelectedPairExact where

------------------------------------------------------------------------
-- LITERAL PHYSICAL TRIAD FOLD = FILTERED ORDERED-PAIR FOLD
--
-- physicalTriadEnumeration N is definitionally obtained by filtering the
-- Cartesian product cutoffModes N x cutoffModes N by the requirement that
-- the resonant output p+q also lies in the cutoff.
--
-- Therefore any scalar depending on a physical incidence only through its
-- ordered input pair may be folded as the corresponding Boolean-selected
-- ordered-pair sum.  No triad multiplicity theorem is required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNSignedSelfPhaseSelectedPairPaymentExact as PairPay

pairContribution :
  (Physical.PhysicalTriadIncidence → ℚ) →
  Z3.FourierMode → Z3.FourierMode → ℚ
pairContribution contribution p q =
  contribution (Physical.pairTriad (Cube.pair p q))

resonantOutputSelected :
  Nat → Z3.FourierMode → Z3.FourierMode → Bool
resonantOutputSelected cutoff p q =
  Physical.modeWithinCutoff cutoff (Z3.addMode p q)

foldTriads :
  (Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
foldTriads contribution [] = 0ℚ
foldTriads contribution (tau ∷ rest) =
  contribution tau + foldTriads contribution rest

foldPairList :
  Nat →
  (Physical.PhysicalTriadIncidence → ℚ) →
  List (Cube.Pair Z3.FourierMode Z3.FourierMode) → ℚ
foldPairList cutoff contribution [] = 0ℚ
foldPairList cutoff contribution (pair ∷ rest)
    with Physical.modeWithinCutoff cutoff
      (Z3.addMode (Cube.first pair) (Cube.second pair))
... | true =
    contribution (Physical.pairTriad pair)
      + foldPairList cutoff contribution rest
... | false =
    foldPairList cutoff contribution rest

foldEnumerateFromPairs :
  (cutoff : Nat) →
  (contribution : Physical.PhysicalTriadIncidence → ℚ) →
  (pairs : List (Cube.Pair Z3.FourierMode Z3.FourierMode)) →
  foldTriads contribution (Physical.enumerateFromPairs cutoff pairs)
  ≡ foldPairList cutoff contribution pairs
foldEnumerateFromPairs cutoff contribution [] = refl
foldEnumerateFromPairs cutoff contribution (pair ∷ rest)
  with Physical.modeWithinCutoff cutoff
    (Z3.addMode (Cube.first pair) (Cube.second pair))
... | true =
    cong
      (contribution (Physical.pairTriad pair) +_)
      (foldEnumerateFromPairs cutoff contribution rest)
... | false =
    foldEnumerateFromPairs cutoff contribution rest

foldFixedLeft :
  Nat →
  (Physical.PhysicalTriadIncidence → ℚ) →
  Z3.FourierMode →
  List Z3.FourierMode → ℚ
foldFixedLeft cutoff contribution p [] = 0ℚ
foldFixedLeft cutoff contribution p (q ∷ rest)
    with Physical.modeWithinCutoff cutoff (Z3.addMode p q)
... | true =
    contribution (Physical.pairTriad (Cube.pair p q))
      + foldFixedLeft cutoff contribution p rest
... | false =
    foldFixedLeft cutoff contribution p rest

selectedInnerMeaning :
  (cutoff : Nat) →
  (contribution : Physical.PhysicalTriadIncidence → ℚ) →
  (p : Z3.FourierMode) →
  (rights : List Z3.FourierMode) →
  PairPay.selectedContributionInner
    (resonantOutputSelected cutoff)
    (pairContribution contribution)
    p rights
  ≡ foldFixedLeft cutoff contribution p rights
selectedInnerMeaning cutoff contribution p [] = refl
selectedInnerMeaning cutoff contribution p (q ∷ rest)
  with Physical.modeWithinCutoff cutoff (Z3.addMode p q)
... | true =
    cong
      (contribution (Physical.pairTriad (Cube.pair p q)) +_)
      (selectedInnerMeaning cutoff contribution p rest)
... | false =
    selectedInnerMeaning cutoff contribution p rest

foldCartesian :
  Nat →
  (Physical.PhysicalTriadIncidence → ℚ) →
  List Z3.FourierMode →
  List Z3.FourierMode → ℚ
foldCartesian cutoff contribution [] rights = 0ℚ
foldCartesian cutoff contribution (p ∷ rest) rights =
  foldFixedLeft cutoff contribution p rights
    + foldCartesian cutoff contribution rest rights

selectedCartesianMeaning :
  (cutoff : Nat) →
  (contribution : Physical.PhysicalTriadIncidence → ℚ) →
  (lefts rights : List Z3.FourierMode) →
  PairPay.selectedContributionSum
    (resonantOutputSelected cutoff)
    (pairContribution contribution)
    lefts rights
  ≡ foldCartesian cutoff contribution lefts rights
selectedCartesianMeaning cutoff contribution [] rights = refl
selectedCartesianMeaning cutoff contribution (p ∷ rest) rights =
  trans
    (cong
      (_+ PairPay.selectedContributionSum
        (resonantOutputSelected cutoff)
        (pairContribution contribution)
        rest rights)
      (selectedInnerMeaning cutoff contribution p rights))
    (cong
      (foldFixedLeft cutoff contribution p rights +_)
      (selectedCartesianMeaning cutoff contribution rest rights))

foldCartesianIsFoldPairList :
  (cutoff : Nat) →
  (contribution : Physical.PhysicalTriadIncidence → ℚ) →
  (lefts rights : List Z3.FourierMode) →
  foldCartesian cutoff contribution lefts rights
  ≡ foldPairList cutoff contribution (Cube.cartesian lefts rights)
foldCartesianIsFoldPairList cutoff contribution [] rights = refl
foldCartesianIsFoldPairList cutoff contribution (p ∷ rest) rights =
  trans
    (cong
      (foldFixedLeft cutoff contribution p rights +_)
      (foldCartesianIsFoldPairList cutoff contribution rest rights))
    (sym (foldPairListCartesianHead cutoff contribution p rest rights))

foldPairListCartesianHead :
  (cutoff : Nat) →
  (contribution : Physical.PhysicalTriadIncidence → ℚ) →
  (p : Z3.FourierMode) →
  (rest rights : List Z3.FourierMode) →
  foldPairList cutoff contribution
    (Cube.cartesian (p ∷ rest) rights)
  ≡
  foldFixedLeft cutoff contribution p rights
    + foldPairList cutoff contribution (Cube.cartesian rest rights)
foldPairListCartesianHead cutoff contribution p rest [] = refl
foldPairListCartesianHead cutoff contribution p rest (q ∷ rights)
  with Physical.modeWithinCutoff cutoff (Z3.addMode p q)
... | true =
    cong
      (contribution (Physical.pairTriad (Cube.pair p q)) +_)
      (foldPairListCartesianHead cutoff contribution p rest rights)
... | false =
    foldPairListCartesianHead cutoff contribution p rest rights

physicalTriadFoldIsSelectedOrderedPairFold :
  (cutoff : Nat) →
  (contribution : Physical.PhysicalTriadIncidence → ℚ) →
  foldTriads contribution (Physical.physicalTriadEnumeration cutoff)
  ≡
  PairPay.selectedContributionSum
    (resonantOutputSelected cutoff)
    (pairContribution contribution)
    (Cube.cutoffModes cutoff)
    (Cube.cutoffModes cutoff)
physicalTriadFoldIsSelectedOrderedPairFold cutoff contribution =
  let
    modes = Cube.cutoffModes cutoff
    pairs = Cube.cartesian modes modes
  in
  trans
    (foldEnumerateFromPairs cutoff contribution pairs)
    (trans
      (sym (foldCartesianIsFoldPairList cutoff contribution modes modes))
      (sym (selectedCartesianMeaning cutoff contribution modes modes)))

physicalTriadFoldUsesUniqueOrderedPairOutput : Bool
physicalTriadFoldUsesUniqueOrderedPairOutput = true

physicalTriadFoldAddsMultiplicityFactor : Bool
physicalTriadFoldAddsMultiplicityFactor = false

physicalTriadFoldUsesUniqueOrderedPairOutputIsTrue :
  physicalTriadFoldUsesUniqueOrderedPairOutput ≡ true
physicalTriadFoldUsesUniqueOrderedPairOutputIsTrue = refl

physicalTriadFoldAddsMultiplicityFactorIsFalse :
  physicalTriadFoldAddsMultiplicityFactor ≡ false
physicalTriadFoldAddsMultiplicityFactorIsFalse = refl
