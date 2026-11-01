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
open import Data.List.Base using (map; _++_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

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

foldPairListAppend :
  (cutoff : Nat) →
  (contribution : Physical.PhysicalTriadIncidence → ℚ) →
  (left right : List (Cube.Pair Z3.FourierMode Z3.FourierMode)) →
  foldPairList cutoff contribution (left ++ right)
  ≡ foldPairList cutoff contribution left
      + foldPairList cutoff contribution right
foldPairListAppend cutoff contribution [] right = refl
foldPairListAppend cutoff contribution (pair ∷ rest) right
  with Physical.modeWithinCutoff cutoff
    (Z3.addMode (Cube.first pair) (Cube.second pair))
... | true =
    trans
      (cong
        (contribution (Physical.pairTriad pair) +_)
        (foldPairListAppend cutoff contribution rest right))
      (solve
        ( contribution (Physical.pairTriad pair)
        ∷ foldPairList cutoff contribution rest
        ∷ foldPairList cutoff contribution right
        ∷ [] ))
... | false =
    foldPairListAppend cutoff contribution rest right

foldMappedLeft :
  (cutoff : Nat) →
  (contribution : Physical.PhysicalTriadIncidence → ℚ) →
  (p : Z3.FourierMode) →
  (rights : List Z3.FourierMode) →
  foldPairList cutoff contribution (map (λ q → Cube.pair p q) rights)
  ≡
  PairPay.selectedContributionInner
    (resonantOutputSelected cutoff)
    (pairContribution contribution)
    p rights
foldMappedLeft cutoff contribution p [] = refl
foldMappedLeft cutoff contribution p (q ∷ rest)
  with Physical.modeWithinCutoff cutoff (Z3.addMode p q)
... | true =
    cong
      (contribution (Physical.pairTriad (Cube.pair p q)) +_)
      (foldMappedLeft cutoff contribution p rest)
... | false =
    foldMappedLeft cutoff contribution p rest

foldCartesianIsSelectedContribution :
  (cutoff : Nat) →
  (contribution : Physical.PhysicalTriadIncidence → ℚ) →
  (lefts rights : List Z3.FourierMode) →
  foldPairList cutoff contribution (Cube.cartesian lefts rights)
  ≡
  PairPay.selectedContributionSum
    (resonantOutputSelected cutoff)
    (pairContribution contribution)
    lefts rights
foldCartesianIsSelectedContribution cutoff contribution [] rights = refl
foldCartesianIsSelectedContribution cutoff contribution (p ∷ rest) rights =
  trans
    (foldPairListAppend
      cutoff contribution
      (map (λ q → Cube.pair p q) rights)
      (Cube.cartesian rest rights))
    (cong₂ _+_
      (foldMappedLeft cutoff contribution p rights)
      (foldCartesianIsSelectedContribution
        cutoff contribution rest rights))

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
    (foldCartesianIsSelectedContribution
      cutoff contribution modes modes)

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
