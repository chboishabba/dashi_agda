module DASHI.NumberTheory.Collatz.SyracuseParityCylinderCompilerExact where

------------------------------------------------------------------------
-- GENERIC PARITY-CYLINDER INDUCTION COMPILER
--
-- This file factors the remaining C3/C5 arithmetic wall into literal one-step
-- residue laws.  Once those laws are supplied for the concrete recursive
-- residue candidate, the full arbitrary-length forward/reverse cylinder theorem
-- is compiled here by induction on BinaryWord.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.DivMod using (_%_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderCandidateExact as Candidate

record CylinderOneStepArithmetic : Set₁ where
  field
    baseResidue :
      (x : Syracuse.PositiveNat) →
      Syracuse.toNat x % Cylinder.pow2 zero
      ≡ Candidate.residueCandidate Binary.end

    candidateBounded :
      {m : Nat} →
      (word : Binary.BinaryWord m) →
      Candidate.residueCandidate word % Cylinder.pow2 m
      ≡ Candidate.residueCandidate word

    bit0Forward :
      {m : Nat} →
      (tail : Binary.BinaryWord m) →
      (x : Syracuse.PositiveNat) →
      Itinerary.parityWord (suc m) x ≡ Binary.bit0 tail →
      Syracuse.toNat (Syracuse.shortcutSyracuse x) % Cylinder.pow2 m
        ≡ Candidate.residueCandidate tail →
      Syracuse.toNat x % Cylinder.pow2 (suc m)
        ≡ Candidate.residueCandidate (Binary.bit0 tail)

    bit1Forward :
      {m : Nat} →
      (tail : Binary.BinaryWord m) →
      (x : Syracuse.PositiveNat) →
      Itinerary.parityWord (suc m) x ≡ Binary.bit1 tail →
      Syracuse.toNat (Syracuse.shortcutSyracuse x) % Cylinder.pow2 m
        ≡ Candidate.residueCandidate tail →
      Syracuse.toNat x % Cylinder.pow2 (suc m)
        ≡ Candidate.residueCandidate (Binary.bit1 tail)

    bit0Reverse :
      {m : Nat} →
      (tail : Binary.BinaryWord m) →
      (x : Syracuse.PositiveNat) →
      Syracuse.toNat x % Cylinder.pow2 (suc m)
        ≡ Candidate.residueCandidate (Binary.bit0 tail) →
      (Itinerary.parity x ≡ false)
      ×
      (Syracuse.toNat (Syracuse.shortcutSyracuse x) % Cylinder.pow2 m
        ≡ Candidate.residueCandidate tail)

    bit1Reverse :
      {m : Nat} →
      (tail : Binary.BinaryWord m) →
      (x : Syracuse.PositiveNat) →
      Syracuse.toNat x % Cylinder.pow2 (suc m)
        ≡ Candidate.residueCandidate (Binary.bit1 tail) →
      (Itinerary.parity x ≡ true)
      ×
      (Syracuse.toNat (Syracuse.shortcutSyracuse x) % Cylinder.pow2 m
        ≡ Candidate.residueCandidate tail)

    candidateInjective :
      {m : Nat} →
      (left right : Binary.BinaryWord m) →
      Candidate.residueCandidate left ≡ Candidate.residueCandidate right →
      left ≡ right

open CylinderOneStepArithmetic public

bit0TailFromWord :
  {m : Nat} →
  (tail : Binary.BinaryWord m) →
  (x : Syracuse.PositiveNat) →
  Itinerary.parityWord (suc m) x ≡ Binary.bit0 tail →
  Itinerary.parityWord m (Syracuse.shortcutSyracuse x) ≡ tail
bit0TailFromWord tail x whole with Itinerary.parity x
... | false with whole
... | refl = refl
... | true with whole
... | ()

bit1TailFromWord :
  {m : Nat} →
  (tail : Binary.BinaryWord m) →
  (x : Syracuse.PositiveNat) →
  Itinerary.parityWord (suc m) x ≡ Binary.bit1 tail →
  Itinerary.parityWord m (Syracuse.shortcutSyracuse x) ≡ tail
bit1TailFromWord tail x whole with Itinerary.parity x
... | false with whole
... | ()
... | true with whole
... | refl = refl

forwardClassification :
  (arithmetic : CylinderOneStepArithmetic) →
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (x : Syracuse.PositiveNat) →
  Itinerary.parityWord m x ≡ word →
  Syracuse.toNat x % Cylinder.pow2 m
    ≡ Candidate.residueCandidate word
forwardClassification arithmetic {zero} Binary.end x whole =
  baseResidue arithmetic x
forwardClassification arithmetic {suc m} (Binary.bit0 tail) x whole =
  bit0Forward arithmetic tail x whole
    (forwardClassification arithmetic tail
      (Syracuse.shortcutSyracuse x)
      (bit0TailFromWord tail x whole))
forwardClassification arithmetic {suc m} (Binary.bit1 tail) x whole =
  bit1Forward arithmetic tail x whole
    (forwardClassification arithmetic tail
      (Syracuse.shortcutSyracuse x)
      (bit1TailFromWord tail x whole))

reverseClassification :
  (arithmetic : CylinderOneStepArithmetic) →
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  (x : Syracuse.PositiveNat) →
  Syracuse.toNat x % Cylinder.pow2 m
    ≡ Candidate.residueCandidate word →
  Itinerary.parityWord m x ≡ word
reverseClassification arithmetic {zero} Binary.end x residue = refl
reverseClassification arithmetic {suc m} (Binary.bit0 tail) x residue =
  let
    step = bit0Reverse arithmetic tail x residue
    parityFalse = proj₁ step
    tailResidue = proj₂ step
    tailWord = reverseClassification arithmetic tail
      (Syracuse.shortcutSyracuse x) tailResidue
  in
  trans
    (Itinerary.firstParityFalse x parityFalse)
    (cong Binary.bit0 tailWord)
reverseClassification arithmetic {suc m} (Binary.bit1 tail) x residue =
  let
    step = bit1Reverse arithmetic tail x residue
    parityTrue = proj₁ step
    tailResidue = proj₂ step
    tailWord = reverseClassification arithmetic tail
      (Syracuse.shortcutSyracuse x) tailResidue
  in
  trans
    (Itinerary.firstParityTrue x parityTrue)
    (cong Binary.bit1 tailWord)

compileParityCylinderSource :
  CylinderOneStepArithmetic →
  Cylinder.ParityCylinderSource
compileParityCylinderSource arithmetic = record
  { Cylinder.residueOfParityWord = Candidate.residueCandidate
  ; Cylinder.residueBounded = candidateBounded arithmetic
  ; Cylinder.parityWordImpliesResidue = forwardClassification arithmetic
  ; Cylinder.residueImpliesParityWord = reverseClassification arithmetic
  ; Cylinder.residueOfParityWordInjective = candidateInjective arithmetic
  }

record CylinderCompilerBoundary : Set where
  constructor cylinderCompilerBoundary
  field
    arbitraryLengthInductionOwned : Nat
    wordHeadEliminationOwned : Nat
    oneStepArithmeticStillRequired : Nat
    cardinalityShortcutUsed : Nat

canonicalCylinderCompilerBoundary : CylinderCompilerBoundary
canonicalCylinderCompilerBoundary = cylinderCompilerBoundary 1 1 1 0
