module DASHI.NumberTheory.Collatz.SyracuseParityCylinderOneStepBaseExact where

------------------------------------------------------------------------
-- GENERICALLY PAID PART OF THE ONE-STEP CYLINDER ARITHMETIC
--
-- The residue-zero base case and candidate-reduction property do not depend on
-- Collatz-specific branch algebra.  They follow directly from the definitions
-- and the standard library modulo laws.  The remaining source record therefore
-- contains only the four branch transports plus injectivity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _-_)
open import Data.Nat.DivMod using (n%1≡0; m%n%n≡m%n)
open import Data.Product using (_×_)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderCandidateExact as Candidate
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderCompilerExact as Compiler
import DASHI.NumberTheory.Collatz.SyracusePow2ArithmeticExact as Pow2

baseResiduePaid :
  (x : Syracuse.PositiveNat) →
  Syracuse.toNat x % Cylinder.pow2 zero
  ≡ Candidate.residueCandidate Binary.end
baseResiduePaid x = n%1≡0 (Syracuse.toNat x)
  where open import Data.Nat.DivMod using (_%_)

candidateBoundedPaid :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Candidate.residueCandidate word % Cylinder.pow2 m
  ≡ Candidate.residueCandidate word
candidateBoundedPaid {zero} Binary.end = n%1≡0 zero
candidateBoundedPaid {suc m} (Binary.bit0 tail) =
  let
    instance pow2-nonzero = Pow2.pow2NonZero (suc m)
  in
  m%n%n≡m%n
    (2 * Candidate.residueCandidate tail)
    (Cylinder.pow2 (suc m))
candidateBoundedPaid {suc m} (Binary.bit1 tail) =
  let
    instance pow2-nonzero = Pow2.pow2NonZero (suc m)
    raw = Candidate.inv3Candidate (suc m)
      * ((2 * Candidate.residueCandidate tail + Cylinder.pow2 (suc m)) - 1)
  in
  m%n%n≡m%n raw (Cylinder.pow2 (suc m))

record CylinderHardArithmetic : Set₁ where
  field
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

open CylinderHardArithmetic public

compileOneStepArithmetic :
  CylinderHardArithmetic →
  Compiler.CylinderOneStepArithmetic
compileOneStepArithmetic hard = record
  { Compiler.baseResidue = baseResiduePaid
  ; Compiler.candidateBounded = candidateBoundedPaid
  ; Compiler.bit0Forward = bit0Forward hard
  ; Compiler.bit1Forward = bit1Forward hard
  ; Compiler.bit0Reverse = bit0Reverse hard
  ; Compiler.bit1Reverse = bit1Reverse hard
  ; Compiler.candidateInjective = candidateInjective hard
  }

record OneStepBaseBoundary : Set where
  constructor oneStepBaseBoundary
  field
    baseResidueOwned : Nat
    candidateModuloIdempotenceOwned : Nat
    branchTransportStillSourceSpecific : Nat
    candidateInjectivityStillSourceSpecific : Nat

canonicalOneStepBaseBoundary : OneStepBaseBoundary
canonicalOneStepBaseBoundary = oneStepBaseBoundary 1 1 1 1
