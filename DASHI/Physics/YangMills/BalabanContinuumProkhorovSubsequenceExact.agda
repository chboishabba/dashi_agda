module DASHI.Physics.YangMills.BalabanContinuumProkhorovSubsequenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Yu. V. Prokhorov,
-- "Convergence of Random Processes and Limit Theorems in Probability Theory",
-- Theory of Probability and Its Applications 1 (1956), 157--214.
-- DOI: 10.1137/1101016.
--
-- Diego A. Rojas,
-- "Effective Weak Convergence and Tightness of Measures in Computable Polish
-- Spaces", Theory of Computing Systems 70 (2026), article 36.
-- DOI: 10.1007/s00224-026-10282-x.
--
-- DASHI CONTRIBUTION
--
-- Remove subsequence extraction itself from the Yang--Mills research frontier.
-- Once the actual renormalized Schwinger-family laws form a tight family of
-- probability measures on the chosen Polish distribution space, classical
-- Prokhorov gives a weakly convergent subsequence.  The 2026 effective theorem
-- identifies the stronger computable version when effective tightness data is
-- available.
--
-- This file is deliberately narrow.  It does NOT prove tightness of Yang--Mills
-- measures, uniqueness of the limit, OS axioms, Euclidean covariance, or
-- interacting survival.  Those remain physical continuum theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record ProkhorovSubsequenceAuthority (Measure Limit : Set) : Set₁ where
  field
    TightSequence : (Nat → Measure) → Set
    WeaklyConverges : (Nat → Measure) → Limit → Set
    StrictlyIncreasing : (Nat → Nat) → Set

    tightSequenceHasWeaklyConvergentSubsequence :
      ∀ sequence → TightSequence sequence →
      Σ Limit (λ limit →
        Σ (Nat → Nat) (λ subsequence →
          Product
            (StrictlyIncreasing subsequence)
            (WeaklyConverges (λ n → sequence (subsequence n)) limit)))

open ProkhorovSubsequenceAuthority public

-- Local products/sigma avoid importing a larger measure/topology hierarchy.
record Product (A B : Set) : Set where
  constructor _,_
  field first : A; second : B
open Product public

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B

record RenormalizedSchwingerTightness
    {Measure Limit : Set}
    (authority : ProkhorovSubsequenceAuthority Measure Limit) : Set₁ where
  field
    schwingerLawAtCutoff : Nat → Measure
    schwingerFamilyTight :
      TightSequence authority schwingerLawAtCutoff
open RenormalizedSchwingerTightness public

continuumSchwingerSubsequenceExists :
  ∀ {Measure Limit}
    (authority : ProkhorovSubsequenceAuthority Measure Limit)
    (physical : RenormalizedSchwingerTightness authority) →
  Σ Limit (λ limit →
    Σ (Nat → Nat) (λ subsequence →
      Product
        (StrictlyIncreasing authority subsequence)
        (WeaklyConverges authority
          (λ n → schwingerLawAtCutoff physical (subsequence n)) limit)))
continuumSchwingerSubsequenceExists authority physical =
  tightSequenceHasWeaklyConvergentSubsequence authority
    (schwingerLawAtCutoff physical)
    (schwingerFamilyTight physical)

prokhorovSubsequenceAuthorityLevel : ProofLevel
prokhorovSubsequenceAuthorityLevel = standardImported

continuumSubsequenceFromTightnessLevel : ProofLevel
continuumSubsequenceFromTightnessLevel = machineChecked

-- The actual frontier leaf: prove tightness for the SAME renormalized
-- gauge-invariant Schwinger family produced by the cutoff RG construction.
renormalizedYangMillsSchwingerTightnessLevel : ProofLevel
renormalizedYangMillsSchwingerTightnessLevel = conditional
