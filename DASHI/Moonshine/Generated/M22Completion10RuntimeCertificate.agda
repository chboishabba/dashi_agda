module DASHI.Moonshine.Generated.M22Completion10RuntimeCertificate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- GENERATED RUNTIME RECEIPT.
--
-- Inputs:
-- * AtlasRep M22 ten-dimensional GF(2) involution screen;
-- * AtlasRep M24 p276 permutation module restricted to M22:2 and M22.
--
-- This certificate records runtime finite-group/module facts only.
-- It does NOT identify the M24 p276 module with the Carnahan--Urano
-- 2B Tate multiplicity.  That same-object weld remains false below.
------------------------------------------------------------------------

m22TenRepresentationCount : Nat
m22TenRepresentationCount = 2

m22InvolutionRowCount : Nat
m22InvolutionRowCount = 2

m22J2x5MatchCount : Nat
m22J2x5MatchCount = 0

m22HasJ2x5Match : Bool
m22HasJ2x5Match = false

m22FivePairBasisWitnessCount : Nat
m22FivePairBasisWitnessCount = 0

m22HasExplicitFivePairBasis : Bool
m22HasExplicitFivePairBasis = false

m24PermutationDegree : Nat
m24PermutationDegree = 276

m22d2Order : Nat
m22d2Order = 887040

m22Order : Nat
m22Order = 443520

m22d2CompositionDimensionSum : Nat
m22d2CompositionDimensionSum = 276

m22CompositionDimensionSum : Nat
m22CompositionDimensionSum = 276

m22d2TenFactorCount : Nat
m22d2TenFactorCount = 10

m22TenFactorCount : Nat
m22TenFactorCount = 10

m22AtlasRepIdentifiedTenFactorCount : Nat
m22AtlasRepIdentifiedTenFactorCount = 10

allObservedM22TenFactorsIdentified : Bool
allObservedM22TenFactorsIdentified = true

m22d2HasTenFactor : Bool
m22d2HasTenFactor = true

m22HasTenFactor : Bool
m22HasTenFactor = true

m24PermutationDegreeIs276 : m24PermutationDegree ≡ 276
m24PermutationDegreeIs276 = refl

m22d2CompositionCloses276 : m22d2CompositionDimensionSum ≡ 276
m22d2CompositionCloses276 = refl

m22CompositionCloses276 : m22CompositionDimensionSum ≡ 276
m22CompositionCloses276 = refl

-- Semantic promotion firewall.
sameObjectWithCarnahanUrano2BTate276Paid : Bool
sameObjectWithCarnahanUrano2BTate276Paid = false

completion10EmbeddingIntoActual2BTatePaid : Bool
completion10EmbeddingIntoActual2BTatePaid = false

runtimeM22FactorAndInvolutionEvidenceJointlySufficient : Bool
runtimeM22FactorAndInvolutionEvidenceJointlySufficient =
  false
