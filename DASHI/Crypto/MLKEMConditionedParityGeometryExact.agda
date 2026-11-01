module DASHI.Crypto.MLKEMConditionedParityGeometryExact where

------------------------------------------------------------------------
-- CONDITION ONE SOURCE-PARITY BLOCK: REMAINING SYSTEM GEOMETRY
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- The source CBD secret has 256*k coefficients.  Splitting by source parity
-- gives two blocks of 128*k coefficients.  If one block is conditioned, the
-- remaining block therefore has 128*k source coefficients.
--
-- The public NTT vector has k polynomials and 256 scalar entries/polynomial.
-- After subtracting the known conditioned contribution, BaseCase gives two
-- noisy scalar equations per quadratic residue, so the remaining block is
-- constrained by 256*k scalar public equations.  Hence the structural equation
-- count is exactly twice the remaining source-variable count.
--
-- This is a dimension/count theorem only: noise, modular rank, prior support and
-- reconciliation determine whether that overdetermined appearance is useful.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Product using (_×_; _,_)

import DASHI.Crypto.MLKEMFIPS203SourceExact as FIPS

sourceParityCoefficientsPerPolynomial : Nat
sourceParityCoefficientsPerPolynomial = 128

remainingParityUnknowns : FIPS.MLKEMParameters → Nat
remainingParityUnknowns p =
  sourceParityCoefficientsPerPolynomial * FIPS.k p

conditionedPublicScalarEquations : FIPS.MLKEMParameters → Nat
conditionedPublicScalarEquations p =
  FIPS.n * FIPS.k p

conditionedEquationsAreTwiceRemainingUnknowns :
  ∀ p → conditionedPublicScalarEquations p ≡ 2 * remainingParityUnknowns p
conditionedEquationsAreTwiceRemainingUnknowns p = refl

remaining512Unknowns : remainingParityUnknowns FIPS.params512 ≡ 256
remaining512Unknowns = refl

remaining768Unknowns : remainingParityUnknowns FIPS.params768 ≡ 384
remaining768Unknowns = refl

remaining1024Unknowns : remainingParityUnknowns FIPS.params1024 ≡ 512
remaining1024Unknowns = refl

conditioned512Equations : conditionedPublicScalarEquations FIPS.params512 ≡ 512
conditioned512Equations = refl

conditioned768Equations : conditionedPublicScalarEquations FIPS.params768 ≡ 768
conditioned768Equations = refl

conditioned1024Equations : conditionedPublicScalarEquations FIPS.params1024 ≡ 1024
conditioned1024Equations = refl

parameterGeometry512 :
  remainingParityUnknowns FIPS.params512 ≡ 256
  × conditionedPublicScalarEquations FIPS.params512 ≡ 512
parameterGeometry512 = refl , refl

------------------------------------------------------------------------
-- Boundary: equation surplus is not rank, uniqueness or algorithmic recovery.
------------------------------------------------------------------------

record ConditionedParityBoundary : Set where
  constructor conditionedParityBoundary
  field
    equationCountExceedsUnknownCount : Bool
    equationCountExceedsUnknownCountIsTrue :
      equationCountExceedsUnknownCount ≡ true
    equationSurplusProvesUniqueSecret : Bool
    equationSurplusProvesUniqueSecretIsFalse :
      equationSurplusProvesUniqueSecret ≡ false
    equationSurplusProvesPolynomialRecovery : Bool
    equationSurplusProvesPolynomialRecoveryIsFalse :
      equationSurplusProvesPolynomialRecovery ≡ false

open ConditionedParityBoundary public

canonicalConditionedParityBoundary : ConditionedParityBoundary
canonicalConditionedParityBoundary =
  conditionedParityBoundary true refl false refl false refl
