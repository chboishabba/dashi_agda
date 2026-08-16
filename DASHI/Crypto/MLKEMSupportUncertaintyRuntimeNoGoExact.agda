module DASHI.Crypto.MLKEMSupportUncertaintyRuntimeNoGoExact where

------------------------------------------------------------------------
-- ML-KEM: SUPPORT UNCERTAINTY DOES NOT BY ITSELF PROVE RUNTIME WORK
--
-- Primary cryptographic source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- FIPS 203, 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Finite-field uncertainty source:
-- Martino Borello; Patrick Sole,
-- "The uncertainty principle over finite fields",
-- Discrete Mathematics 345 (2022), 112670.
-- DOI: 10.1016/j.disc.2021.112670.
--
-- PURPOSE
--
-- The 128-point support theorem is a statement about localization, not an
-- automatic machine-time lower bound.  A cost model may assign one abstract
-- work unit to an operation whose semantic effect touches many residues.
-- Therefore the premise
--
--     survivingSupport <= verifierWork
--
-- used by MLKEMUncertaintyTransitionCostBridgeExact is a genuine additional
-- implementation/cost-model theorem; it cannot be deleted merely because the
-- support uncertainty theorem is true.
--
-- The finite witness below makes that separation exact:
--
--     changedSupport   = 1
--     survivingSupport = 128
--     singularBudget   = 0
--     verifierWork     = 1
--
-- has the sharp support product 1*128 = 128 while its abstract work product is
-- only 1*1 = 1.  This does NOT assert such a one-unit ML-KEM implementation
-- exists.  It proves only that support counts and an unconstrained work metric
-- are logically different coordinates, so a same-object cost domination
-- theorem is mandatory before claiming runtime hardness.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Empty using (⊥)

changedSupport survivingSupport singularBudget verifierWork : Nat
changedSupport = 1
survivingSupport = 128
singularBudget = 0
verifierWork = 1

supportProduct : Nat
supportProduct = changedSupport * survivingSupport

workProduct : Nat
workProduct = changedSupport * verifierWork

supportProductIs128 : supportProduct ≡ 128
supportProductIs128 = refl

workProductIs1 : workProduct ≡ 1
workProductIs1 = refl

-- The two products are definitionally different concrete naturals.
supportProductCannotEqualWorkProduct : supportProduct ≡ workProduct → ⊥
supportProductCannotEqualWorkProduct ()

record RuntimeBridgeAuthorityBoundary : Set where
  constructor runtime-bridge-authority-boundary
  field
    supportUncertaintyProvesRuntimeWithoutCostDomination : Set

open RuntimeBridgeAuthorityBoundary public

canonicalRuntimeBridgeAuthorityBoundary : RuntimeBridgeAuthorityBoundary
canonicalRuntimeBridgeAuthorityBoundary =
  runtime-bridge-authority-boundary (supportProduct ≡ workProduct)

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- The next useful producer is therefore not another uncertainty lemma.  It is
-- a concrete theorem for a chosen verifier implementation/cost measure showing
-- that its charged work dominates the surviving-support quantity (or a more
-- faithful operational quantity from which an analogous lower bound follows).
-- Batched/SIMD/FFT cost models may require a different theorem and a different
-- unit of work.  This file deliberately prevents support cardinality from being
-- silently relabelled as runtime.
------------------------------------------------------------------------
