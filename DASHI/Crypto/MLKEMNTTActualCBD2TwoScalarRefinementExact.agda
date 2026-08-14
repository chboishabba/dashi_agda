module DASHI.Crypto.MLKEMNTTActualCBD2TwoScalarRefinementExact where

------------------------------------------------------------------------
-- ACTUAL FIPS-203 CBD2 TWO-SCALAR REFINEMENT
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Round 17 already exhibits two distinct CBD2-supported source triples that
-- collide on the first constant NTT scalar (quadratic residue i=0).  Here we
-- evaluate the same two source triples at residue i=2.  FIPS gives
--   gamma_2 = zeta^(2*BitRev7(2)+1) = 17^65 = 2761 mod 3329.
-- For source degrees 0,8,12 the corresponding constant-component weights are
-- gamma_2^0=1, gamma_2^4=296, gamma_2^6=1010 mod 3329.
-- The two old colliding sources then map to 713 and 1311 respectively.
--
-- Thus one actual scalar leaves a two-element list on this finite CBD2 slice,
-- while adding a second actual FIPS scalar separates the list to one element.
-- This is local list geometry, not a key-recovery or ML-KEM break claim.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)
open import DASHI.Foundations.Base369Nat using (_%_)

import DASHI.Crypto.MLKEMNTTActualCBD2ScalarCollisionExact as First

q : Nat
q = 3329

powMod : Nat → Nat → Nat
powMod base zero = 1
powMod base (suc n) = (base * powMod base n) % q

gamma2 : Nat
gamma2 = powMod 17 65

gamma2Is2761 : gamma2 ≡ 2761
gamma2Is2761 = refl

weight2-0 weight2-4 weight2-6 : Nat
weight2-0 = powMod gamma2 0
weight2-4 = powMod gamma2 4
weight2-6 = powMod gamma2 6

weight2-0Is1 : weight2-0 ≡ 1
weight2-0Is1 = refl

weight2-4Is296 : weight2-4 ≡ 296
weight2-4Is296 = refl

weight2-6Is1010 : weight2-6 ≡ 1010
weight2-6Is1010 = refl

secondConstantNTTScalar : First.CBD2TripleSlice → Nat
secondConstantNTTScalar source =
  ( First.degree0 source * weight2-0
  + First.degree8 source * weight2-4
  + First.degree12 source * weight2-6
  ) % q

sourceASecondIs713 : secondConstantNTTScalar First.sourceA ≡ 713
sourceASecondIs713 = refl

sourceBSecondIs1311 : secondConstantNTTScalar First.sourceB ≡ 1311
sourceBSecondIs1311 = refl

secondScalarSeparatesOldCollision :
  secondConstantNTTScalar First.sourceA ≡ secondConstantNTTScalar First.sourceB → ⊥
secondScalarSeparatesOldCollision ()

------------------------------------------------------------------------
-- Exact finite list-size regression over the colliding two-point slice.
------------------------------------------------------------------------

data Candidate : Set where
  candidateA candidateB : Candidate

source : Candidate → First.CBD2TripleSlice
source candidateA = First.sourceA
source candidateB = First.sourceB

firstObservedScalar : Nat
firstObservedScalar = 2022

firstMatches : Candidate → Bool
firstMatches candidateA = true
firstMatches candidateB = true

secondObservedScalar : Nat
secondObservedScalar = 713

secondMatches : Candidate → Bool
secondMatches candidateA = true
secondMatches candidateB = false

firstCandidateMask : List Bool
firstCandidateMask = true ∷ true ∷ []

jointCandidateMask : List Bool
jointCandidateMask = true ∷ false ∷ []

liveCount : List Bool → Nat
liveCount [] = 0
liveCount (false ∷ xs) = liveCount xs
liveCount (true ∷ xs) = suc (liveCount xs)

oneScalarListSizeIs2 : liveCount firstCandidateMask ≡ 2
oneScalarListSizeIs2 = refl

twoScalarListSizeIs1 : liveCount jointCandidateMask ≡ 1
twoScalarListSizeIs1 = refl

firstScalarReallyCollides :
  First.firstConstantNTTScalar First.sourceA ≡
  First.firstConstantNTTScalar First.sourceB
firstScalarReallyCollides = First.actualCBD2SliceScalarCollision

secondScalarReallySeparates :
  secondConstantNTTScalar First.sourceA ≡ 713
secondScalarReallySeparates = sourceASecondIs713

record ActualConditionalListRefinement : Set where
  constructor actualConditionalListRefinement
  field
    beforeCount afterCount : Nat
    beforeIsTwo : beforeCount ≡ 2
    afterIsOne : afterCount ≡ 1
    firstCoordinateCollision :
      First.firstConstantNTTScalar First.sourceA ≡
      First.firstConstantNTTScalar First.sourceB
    secondCoordinateSeparates :
      secondConstantNTTScalar First.sourceA ≡
      secondConstantNTTScalar First.sourceB → ⊥

open ActualConditionalListRefinement public

actualCBD2TwoScalarRefinement : ActualConditionalListRefinement
actualCBD2TwoScalarRefinement =
  actualConditionalListRefinement
    2 1 refl refl
    firstScalarReallyCollides
    secondScalarSeparatesOldCollision
