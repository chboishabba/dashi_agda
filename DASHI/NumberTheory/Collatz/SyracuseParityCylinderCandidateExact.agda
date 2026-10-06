module DASHI.NumberTheory.Collatz.SyracuseParityCylinderCandidateExact where

------------------------------------------------------------------------
-- CONCRETE RESIDUE CANDIDATE FOR SYRACUSE PARITY WORDS
--
-- Cross-pollination source:
--   Formalization.Spectral.SchreierConnectivity.three_mul_inv3
-- proves 3 is a unit in ZMod (2^n).  The recursion below is the exact Nat-side
-- candidate induced by solving the first Syracuse parity step backwards.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _-_)
open import Data.Nat.DivMod using (_%_)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder

------------------------------------------------------------------------
-- Inverse of 3 modulo 2^m.
--
-- inv3(1)=1, inv3(2)=3 and inv3(m+2)=4*inv3(m)-1.
-- The separate theorem source must prove
--   3 * inv3Candidate m ≡ 1 (mod 2^m).
------------------------------------------------------------------------

inv3Candidate : Nat → Nat
inv3Candidate zero = zero
inv3Candidate (suc zero) = 1
inv3Candidate (suc (suc zero)) = 3
inv3Candidate (suc (suc (suc m))) =
  4 * inv3Candidate (suc m) - 1

record Inv3Pow2Source : Set where
  field
    inverseLaw :
      (m : Nat) →
      (3 * inv3Candidate m) % Cylinder.pow2 m
      ≡ 1 % Cylinder.pow2 m

open Inv3Pow2Source public

------------------------------------------------------------------------
-- Recursive residue candidate.
--
-- If the first parity bit is 0, x=2*S(x).
-- If it is 1, 3x+1=2*S(x), hence
--   x = 3^{-1}(2*S(x)-1) mod 2^m.
------------------------------------------------------------------------

residueCandidate :
  {m : Nat} → Binary.BinaryWord m → Nat
residueCandidate Binary.end = zero
residueCandidate {suc m} (Binary.bit0 tail) =
  (2 * residueCandidate tail) % Cylinder.pow2 (suc m)
residueCandidate {suc m} (Binary.bit1 tail) =
  (inv3Candidate (suc m)
    * ((2 * residueCandidate tail + Cylinder.pow2 (suc m)) - 1))
  % Cylinder.pow2 (suc m)

record ResidueCandidateCorrect : Set₁ where
  field
    inv3Source : Inv3Pow2Source
    candidateSource : Cylinder.ParityCylinderSource
    sourceUsesCandidate :
      {m : Nat} → (word : Binary.BinaryWord m) →
      Cylinder.residueOfParityWord candidateSource word
      ≡ residueCandidate word

open ResidueCandidateCorrect public

record CandidateBoundary : Set where
  constructor candidateBoundary
  field
    concreteRecursiveCandidateOwned : Nat
    modularInverseProofStillRequired : Nat
    forwardReverseCylinderProofStillRequired : Nat
    finiteSpecimensPromoteToGeneralProof : Nat

canonicalCandidateBoundary : CandidateBoundary
canonicalCandidateBoundary = candidateBoundary 1 1 1 0
