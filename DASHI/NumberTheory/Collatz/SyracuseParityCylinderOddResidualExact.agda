module DASHI.NumberTheory.Collatz.SyracuseParityCylinderOddResidualExact where

------------------------------------------------------------------------
-- ODD-ONLY RESIDUAL AFTER EXACT EVEN-BRANCH CLOSURE
--
-- The generic cylinder compiler originally exposed five source-specific fields:
-- bit0 forward/reverse, bit1 forward/reverse, and candidate injectivity.
-- `SyracuseParityCylinderEvenBranchExact` pays both bit0 fields from the
-- literal Syracuse even equation.  This owner makes the remaining frontier
-- exact: odd forward/reverse transport plus uniqueness of the recursive
-- residue code.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.DivMod using (_%_)
open import Data.Product using (_×_)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderCandidateExact as Candidate
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderCompilerExact as Compiler
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderOneStepBaseExact as Base
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderEvenBranchExact as Even

record OddCylinderResidual : Set₁ where
  field
    bit1Forward :
      {m : Nat} →
      (tail : Binary.BinaryWord m) →
      (x : Syracuse.PositiveNat) →
      Itinerary.parityWord (suc m) x ≡ Binary.bit1 tail →
      Syracuse.toNat (Syracuse.shortcutSyracuse x) % Cylinder.pow2 m
        ≡ Candidate.residueCandidate tail →
      Syracuse.toNat x % Cylinder.pow2 (suc m)
        ≡ Candidate.residueCandidate (Binary.bit1 tail)

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

open OddCylinderResidual public

compileHardArithmetic :
  OddCylinderResidual →
  Base.CylinderHardArithmetic
compileHardArithmetic odd = record
  { Base.bit0Forward = Even.bit0ForwardPaid
  ; Base.bit1Forward = bit1Forward odd
  ; Base.bit0Reverse = Even.bit0ReversePaid
  ; Base.bit1Reverse = bit1Reverse odd
  ; Base.candidateInjective = candidateInjective odd
  }

compileOneStepArithmetic :
  OddCylinderResidual →
  Compiler.CylinderOneStepArithmetic
compileOneStepArithmetic odd =
  Base.compileOneStepArithmetic (compileHardArithmetic odd)

compileParityCylinderSource :
  OddCylinderResidual →
  Cylinder.ParityCylinderSource
compileParityCylinderSource odd =
  Compiler.compileParityCylinderSource (compileOneStepArithmetic odd)

record OddResidualBoundary : Set where
  constructor oddResidualBoundary
  field
    evenForwardStillOpen : Nat
    evenReverseStillOpen : Nat
    oddForwardStillOpen : Nat
    oddReverseStillOpen : Nat
    candidateInjectivityStillOpen : Nat

canonicalOddResidualBoundary : OddResidualBoundary
canonicalOddResidualBoundary = oddResidualBoundary 0 0 1 1 1
