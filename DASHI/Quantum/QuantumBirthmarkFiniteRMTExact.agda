{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkFiniteRMTExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- FINITE-N UNIVERSAL QUANTUM BIRTHMARK FACTORS
--
-- Source lineage:
--   Graf et al., Phys. Rev. X 16, 031063 (2026), DOI 10.1103/dhzb-28rb.
--   Ivy Xiaoya, Anton M. Graf, Eric J. Heller, Joonas Keski-Rahkonen,
--   "Universal Quantum Birthmark: Ghost of the quantum past",
--   arXiv:2602.00891 (2026).
--
-- The companion RMT analysis gives finite accessible-Hilbert-space factors
--   GUE : 2N/(N+1)
--   GOE : 3N/(N+2)
-- approaching 2 and 3 respectively.  We retain these as exact numerator /
-- denominator data.  This module does not pretend to reconstruct the full
-- Dirichlet/Haar integration proof from the generic DASHI carrier.
------------------------------------------------------------------------

record ExactFraction : Set where
  constructor fraction
  field
    numerator : Nat
    denominator : Nat

open ExactFraction public

gueFiniteFactor : Nat → ExactFraction
gueFiniteFactor N = fraction (2 * N) (N + 1)

goeFiniteFactor : Nat → ExactFraction
goeFiniteFactor N = fraction (3 * N) (N + 2)

gueNumerator : (N : Nat) → numerator (gueFiniteFactor N) ≡ 2 * N
gueNumerator N = refl

gueDenominator : (N : Nat) → denominator (gueFiniteFactor N) ≡ N + 1
gueDenominator N = refl

goeNumerator : (N : Nat) → numerator (goeFiniteFactor N) ≡ 3 * N
goeNumerator N = refl

goeDenominator : (N : Nat) → denominator (goeFiniteFactor N) ≡ N + 2
goeDenominator N = refl

largeNLimitWithoutTRS : Nat
largeNLimitWithoutTRS = 2

largeNLimitWithTRS : Nat
largeNLimitWithTRS = 3

record RMTProofBoundary : Set where
  field
    finiteNFormulaSourceSupported : Bool
    dirichletCoefficientLawSourceSupported : Bool
    haarEquivalentDerivationsSourceSupported : Bool
    higherMomentPersistenceSourceSupported : Bool
    fullAnalyticIntegrationKernelProvedHere : Bool

rmtProofBoundary : RMTProofBoundary
rmtProofBoundary = record
  { finiteNFormulaSourceSupported = true
  ; dirichletCoefficientLawSourceSupported = true
  ; haarEquivalentDerivationsSourceSupported = true
  ; higherMomentPersistenceSourceSupported = true
  ; fullAnalyticIntegrationKernelProvedHere = false
  }

sourceIdentifier : String
sourceIdentifier = "arXiv:2602.00891"
