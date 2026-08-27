module DASHI.Core.FiniteTypedBranchingKernelExact where

------------------------------------------------------------------------
-- FINITE TYPED / MULTITYPE BRANCHING KERNEL
--
-- PRIMARY SOURCES
--
-- Theodore E. Harris,
-- "The Theory of Branching Processes", Springer, 1963.
-- DOI: 10.1007/978-3-642-51866-9.
--
-- E. Seneta,
-- "Non-negative Matrices and Markov Chains", 2nd ed., Springer, 1981.
-- DOI: 10.1007/0-387-32792-4.
--
-- SOURCE SCOPE
--
-- Harris supplies the classical branching-process distinction by mean
-- reproduction.  Seneta supplies the non-negative-matrix / Perron--Frobenius
-- background for heterogeneous finite type systems.
--
-- DASHI CONTRIBUTION
--
-- FiniteBranchingCriticalityExact owns the homogeneous scalar arithmetic.
-- This module adds the missing heterogeneous kernel surface requested by the
-- coarse/fine discussion: branch availability may depend on source type,
-- target type, and therefore on the current intersection/fine state.
--
-- It deliberately stops before a spectral-radius theorem, extinction theorem,
-- stochastic independence claim, or probability measure.  The exact content
-- here is finite enumeration, row-mass computation, and per-type regime
-- classification using the already-existing scaled comparator.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; _+_)

import DASHI.Core.FiniteBranchingCriticalityExact as Branch

------------------------------------------------------------------------
-- Generic finite typed kernel.
------------------------------------------------------------------------

record FiniteTypedBranchingKernel (Type : Set) : Set₁ where
  constructor finite-typed-branching-kernel
  field
    typeEnumeration : List Type
    scaledOffspring : Type → Type → Nat
    commonDenominator : Nat

open FiniteTypedBranchingKernel public

rowScaledMassFrom :
  ∀ {Type : Set} →
  FiniteTypedBranchingKernel Type →
  Type →
  List Type →
  Nat
rowScaledMassFrom kernel source [] = zero
rowScaledMassFrom kernel source (target ∷ rest) =
  scaledOffspring kernel source target
  + rowScaledMassFrom kernel source rest

rowScaledMass :
  ∀ {Type : Set} →
  FiniteTypedBranchingKernel Type →
  Type →
  Nat
rowScaledMass kernel source =
  rowScaledMassFrom kernel source (typeEnumeration kernel)

rowRegime :
  ∀ {Type : Set} →
  FiniteTypedBranchingKernel Type →
  Type →
  Branch.BranchingRegime
rowRegime kernel source =
  Branch.classifyScaled
    (rowScaledMass kernel source)
    (commonDenominator kernel)

------------------------------------------------------------------------
-- Concrete heterogeneous three-type witness.
--
-- denominator = 2
--   quiet row      : total 1/2  -> subcritical
--   critical row   : total 2/2  -> critical
--   expanding row  : total 3/2  -> supercritical
--
-- This proves that one global homogeneous availability scalar cannot describe
-- even this tiny finite typed system.
------------------------------------------------------------------------

data FineType : Set where
  quietType criticalType expandingType : FineType

fineTypes : List FineType
fineTypes = quietType ∷ criticalType ∷ expandingType ∷ []

heterogeneousOffspring : FineType → FineType → Nat
heterogeneousOffspring quietType quietType = 0
heterogeneousOffspring quietType criticalType = 1
heterogeneousOffspring quietType expandingType = 0
heterogeneousOffspring criticalType quietType = 1
heterogeneousOffspring criticalType criticalType = 1
heterogeneousOffspring criticalType expandingType = 0
heterogeneousOffspring expandingType quietType = 1
heterogeneousOffspring expandingType criticalType = 1
heterogeneousOffspring expandingType expandingType = 1

canonicalHeterogeneousKernel : FiniteTypedBranchingKernel FineType
canonicalHeterogeneousKernel =
  finite-typed-branching-kernel fineTypes heterogeneousOffspring 2

quietRowMassIsOne :
  rowScaledMass canonicalHeterogeneousKernel quietType ≡ 1
quietRowMassIsOne = refl

criticalRowMassIsTwo :
  rowScaledMass canonicalHeterogeneousKernel criticalType ≡ 2
criticalRowMassIsTwo = refl

expandingRowMassIsThree :
  rowScaledMass canonicalHeterogeneousKernel expandingType ≡ 3
expandingRowMassIsThree = refl

quietTypeIsSubcritical :
  rowRegime canonicalHeterogeneousKernel quietType ≡ Branch.subcritical
quietTypeIsSubcritical = refl

criticalTypeIsCritical :
  rowRegime canonicalHeterogeneousKernel criticalType ≡ Branch.critical
criticalTypeIsCritical = refl

expandingTypeIsSupercritical :
  rowRegime canonicalHeterogeneousKernel expandingType ≡ Branch.supercritical
expandingTypeIsSupercritical = refl

------------------------------------------------------------------------
-- Varying-environment surface: depth selects a kernel rather than pretending
-- that branch availability is stationary across every refinement level.
------------------------------------------------------------------------

record VaryingBranchEnvironment (Type : Set) : Set₁ where
  constructor varying-branch-environment
  field
    kernelAtDepth : Nat → FiniteTypedBranchingKernel Type

open VaryingBranchEnvironment public

constantEnvironment :
  ∀ {Type : Set} →
  FiniteTypedBranchingKernel Type →
  VaryingBranchEnvironment Type
constantEnvironment kernel =
  varying-branch-environment (λ _ → kernel)

canonicalConstantEnvironment : VaryingBranchEnvironment FineType
canonicalConstantEnvironment = constantEnvironment canonicalHeterogeneousKernel

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record FiniteTypedBranchingKernelBoundary : Set where
  constructor finite-typed-branching-kernel-boundary
  field
    typedKernelIsProbabilityMeasure : Bool
    typedKernelIsProbabilityMeasureIsFalse :
      typedKernelIsProbabilityMeasure ≡ false
    rowRegimeDeterminesGlobalExtinction : Bool
    rowRegimeDeterminesGlobalExtinctionIsFalse :
      rowRegimeDeterminesGlobalExtinction ≡ false
    perronFrobeniusSpectralRadiusTheoremConstructedHere : Bool
    perronFrobeniusSpectralRadiusTheoremConstructedHereIsFalse :
      perronFrobeniusSpectralRadiusTheoremConstructedHere ≡ false
    branchCountsAloneDetermineReachability : Bool
    branchCountsAloneDetermineReachabilityIsFalse :
      branchCountsAloneDetermineReachability ≡ false

canonicalFiniteTypedBranchingKernelBoundary :
  FiniteTypedBranchingKernelBoundary
canonicalFiniteTypedBranchingKernelBoundary =
  finite-typed-branching-kernel-boundary
    false refl
    false refl
    false refl
    false refl
