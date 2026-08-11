module DASHI.Physics.Closure.NSTriadKNMaximalUniformViscosityCoreRound27Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Structural precursor:
-- DASHI/Moonshine/Monster3BMaximalRegularCoreExact.agda, which proves a
-- maximal common core from exact sector reconstructions.
--
-- DASHI CONTRIBUTION
--
-- Apply the same maximal-core principle to the nine unique Navier--Stokes tax
-- owners.  A uniform-core decomposition reconstructs each owner's available
-- natural-number dissipation allocation as
--
--   allocation(owner) = commonCore + residual(owner).
--
-- If one canonical owner is pinned with zero residual, then the canonical core
-- equals that owner's allocation and dominates the core of every competing
-- decomposition of the same allocation vector.  Maximality is proved, not
-- selected by convention.
--
-- The analytic problem of producing the physical allocations and showing the
-- eventual rational eta budget is below one remains open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat.Base using (_≤_)
open import Data.Nat.Properties using (m≤m+n; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax

record OwnerDissipationAllocation : Set where
  constructor owner-dissipation-allocation
  field
    availableDissipation : Tax.TaxOwner → Nat

open OwnerDissipationAllocation public

record UniformViscosityCoreDecomposition
    (allocation : OwnerDissipationAllocation) : Set where
  constructor uniform-viscosity-core-decomposition
  field
    commonCore : Nat
    ownerResidual : Tax.TaxOwner → Nat
    reconstructOwner : ∀ owner →
      commonCore + ownerResidual owner
      ≡ availableDissipation allocation owner

open UniformViscosityCoreDecomposition public

candidateCoreBelowEveryOwner :
  ∀ {allocation} →
  (candidate : UniformViscosityCoreDecomposition allocation) →
  ∀ owner →
  commonCore candidate ≤ availableDissipation allocation owner
candidateCoreBelowEveryOwner candidate owner =
  subst
    (λ upper → commonCore candidate ≤ upper)
    (reconstructOwner candidate owner)
    (m≤m+n (commonCore candidate) (ownerResidual candidate owner))

record MaximalUniformCoreWitness
    (allocation : OwnerDissipationAllocation) : Set where
  constructor maximal-uniform-core-witness
  field
    canonicalDecomposition :
      UniformViscosityCoreDecomposition allocation
    pinnedOwner : Tax.TaxOwner
    pinnedResidualZero :
      ownerResidual canonicalDecomposition pinnedOwner ≡ 0

open MaximalUniformCoreWitness public

canonicalCoreEqualsPinnedAllocation :
  ∀ {allocation} →
  (witness : MaximalUniformCoreWitness allocation) →
  commonCore (canonicalDecomposition witness)
  ≡ availableDissipation allocation (pinnedOwner witness)
canonicalCoreEqualsPinnedAllocation witness =
  trans
    (sym (+-identityʳ
      (commonCore (canonicalDecomposition witness))))
    (trans
      (cong
        (commonCore (canonicalDecomposition witness) +_)
        (sym (pinnedResidualZero witness)))
      (reconstructOwner
        (canonicalDecomposition witness)
        (pinnedOwner witness)))
  where
  cong : ∀ {A B : Set} {x y : A} →
    (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

maximalUniformCoreDominatesEveryCandidate :
  ∀ {allocation} →
  (witness : MaximalUniformCoreWitness allocation) →
  (candidate : UniformViscosityCoreDecomposition allocation) →
  commonCore candidate
  ≤ commonCore (canonicalDecomposition witness)
maximalUniformCoreDominatesEveryCandidate witness candidate =
  subst
    (λ upper → commonCore candidate ≤ upper)
    (sym (canonicalCoreEqualsPinnedAllocation witness))
    (candidateCoreBelowEveryOwner candidate (pinnedOwner witness))

maximalCoreAttained :
  ∀ {allocation} →
  (witness : MaximalUniformCoreWitness allocation) →
  commonCore (canonicalDecomposition witness)
  ≡ commonCore (canonicalDecomposition witness)
maximalCoreAttained witness = refl

maximalUniformViscosityCoreTheoremClosed : Bool
maximalUniformViscosityCoreTheoremClosed = true

physicalOwnerAllocationsInstantiated : Bool
physicalOwnerAllocationsInstantiated = false

strictRationalViscosityMarginClosed : Bool
strictRationalViscosityMarginClosed = false
