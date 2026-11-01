module DASHI.Physics.Closure.NSTriadKNBoundaryZeroTaxOwnerRound45Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 29 already classified every cutoff-boundary atom by the mechanism by
-- which it disappears and proved that vanishing of the five subtype ledgers
-- forces the signed boundary total to vanish exactly.  The owner language did
-- not yet consume that theorem.
--
-- This file proves the highest-alpha consequence: once the *physical* boundary
-- production is identified with that classified total and all five physical
-- subtype limits are supplied, the boundary owner has exactly zero production
-- and therefore requires
--
--   eta_boundary = 0,
--   A_boundary = 0,
--   B_boundary = 0.
--
-- Thus boundary is a zero-tax owner, not a fixed positive viscosity cost.  The
-- still-open analysis is precisely the physical construction of the boundary
-- atoms and the five subtype vanishing theorems; no additional owner estimate
-- is required after those land.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax
import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNBoundaryVanishingClassificationRound29Exact as Boundary

record PhysicalBoundaryZeroTaxInput
    (environment : Owner.TaxEnvironment) : Set where
  field
    atoms : List Boundary.BoundaryAtom
    physicalBoundaryProduction : ℚ
    physicalBoundaryProductionNonnegative : 0ℚ ≤ physicalBoundaryProduction

    physicalBoundaryProductionIsClassifiedTotal :
      physicalBoundaryProduction ≡ Boundary.boundaryTotal atoms

    allPhysicalBoundarySubtypesVanish :
      Boundary.AllBoundarySubtypesVanish atoms

open PhysicalBoundaryZeroTaxInput public

physicalBoundaryProductionVanishes :
  ∀ {environment}
    (input : PhysicalBoundaryZeroTaxInput environment) →
  physicalBoundaryProduction input ≡ 0ℚ
physicalBoundaryProductionVanishes input =
  trans
    (physicalBoundaryProductionIsClassifiedTotal input)
    (Boundary.classifiedBoundaryTotalVanishes
      (atoms input) (allPhysicalBoundarySubtypesVanish input))

physicalBoundaryZeroTaxOwnerEstimate :
  ∀ {environment} →
  PhysicalBoundaryZeroTaxInput environment →
  Owner.AdmissibleOwnerEstimate environment
physicalBoundaryZeroTaxOwnerEstimate {environment} input =
  Owner.admissible-owner-estimate
    Tax.boundary
    (physicalBoundaryProduction input)
    0ℚ
    0ℚ
    0ℚ
    ownerBound
  where
  ownerBound :
    physicalBoundaryProduction input
    ≤ 0ℚ * Owner.dissipation environment
      + 0ℚ
      + 0ℚ * Owner.integralCritical environment
  ownerBound =
    subst
      (λ lower →
        lower
        ≤ 0ℚ * Owner.dissipation environment
          + 0ℚ
          + 0ℚ * Owner.integralCritical environment)
      (sym (physicalBoundaryProductionVanishes input))
      (subst
        (λ upper → 0ℚ ≤ upper)
        (sym (solve
          ( Owner.dissipation environment
          ∷ Owner.integralCritical environment
          ∷ [])))
        ℚP.≤-refl)

physicalBoundaryOwnerIdentity :
  ∀ {environment}
    (input : PhysicalBoundaryZeroTaxInput environment) →
  Owner.owner (physicalBoundaryZeroTaxOwnerEstimate input) ≡ Tax.boundary
physicalBoundaryOwnerIdentity input = refl

physicalBoundaryEtaZero :
  ∀ {environment}
    (input : PhysicalBoundaryZeroTaxInput environment) →
  Owner.eta (physicalBoundaryZeroTaxOwnerEstimate input) ≡ 0ℚ
physicalBoundaryEtaZero input = refl

boundaryOwnerIsZeroTaxAfterPhysicalSubtypeLimits : Bool
boundaryOwnerIsZeroTaxAfterPhysicalSubtypeLimits = true

boundaryOwnerIsZeroTaxAfterPhysicalSubtypeLimitsIsTrue :
  boundaryOwnerIsZeroTaxAfterPhysicalSubtypeLimits ≡ true
boundaryOwnerIsZeroTaxAfterPhysicalSubtypeLimitsIsTrue = refl
