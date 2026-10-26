module DASHI.Foundations.AutoformalisationBCH2026SCIInterface where

-- Bastounis, Circelli, Hansen (2026), arXiv:2610.08144v1:
-- Appendix A, Theorems A.3 and A.4. These assert Sigma^0_2
-- completeness and Sigma^0_l completeness for a uniform family of
-- Diophantine presupposition-existence problems (l >= 2, k >= 9).
-- The proofs invoke nine-unknown DPRM, computable polynomial coding,
-- completeness of the arithmetical hierarchy and Post's theorem.
--
-- This is a TYPE-CHECKABLE *UNPAID-OBLIGATION INTERFACE*, not a
-- formal proof of SCI=infinity. In particular, no constructors here
-- invent any of the essential mathematical witnesses.

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_)

-- A faithful "minimum n satisfying B n" cannot be admitted merely
-- by proving a subsequent algebraic identity. At least existence
-- of a witness must be provided before a minimum may be chosen.
record LeastNumberWitness (B : Nat → Set) : Set where
  constructor least-number-witness
  field
    value : Nat
    admissible : B value
    minimal : (m : Nat) → B m → value ≤ m

-- No constructor is provided for a specific source predicate without
-- proving admissibility and genuine minimum order; the Lean companion
-- also uses an existence-gated Nat.find construction.

-- Separate external proof owners, each independently demanded.
record AppendixA4ProofDebt
    (l : Nat)
    (SigmaComplete : Nat → Set)
    (DPRMReduction : Nat → Set)
    (PostHierarchy : Nat → Set) : Set where
  field
    actualSigmaCompleteness : SigmaComplete l
    actualNineUnknownPolynomialReduction : DPRMReduction l
    actualHierarchySeparation : PostHierarchy l

-- The only eliminator gives what an actual owner supplied; none of
-- the above conditions is fabricated by this file.
extractAppendixA4Debt :
  {l : Nat} →
  {SigmaComplete DPRMReduction PostHierarchy : Nat → Set} →
  AppendixA4ProofDebt l SigmaComplete DPRMReduction PostHierarchy →
  SigmaComplete l
extractAppendixA4Debt witness =
  AppendixA4ProofDebt.actualSigmaCompleteness witness
