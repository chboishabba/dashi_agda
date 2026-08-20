module DASHI.Physics.Closure.NSTriadKNHHBadPhysicalCapacityProductWeldRound68Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- ROUND 68 / PHYSICAL A2 CAPACITY PRODUCT WELD
--
-- Round62 turns the selected physical HH-bad profile plus unmasked charge
-- multiplicity into an admissible owner whose viscosity coefficient is exactly
--
--   2 C_* K_bad.
--
-- Round63 observes that the final scalar gate never consumes C_* and K_bad
-- separately; it consumes only
--
--   Lambda_bad = C_* K_bad.
--
-- This file identifies those two same-object quantities directly.  Therefore
-- the remaining HH-bad producer need not optimize two unrelated constants or
-- pass through another recurrence object.  It must prove one physical product
-- bound on the actual selected profile and charge multiplicity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNAdmissibleOwnerTaxLanguageRound28Exact as Owner
import DASHI.Physics.Closure.NSTriadKNHHBadSingleThresholdSufficesRound47Exact as Selected
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedProfileMultiplicityRound62Exact as Physical
import DASHI.Physics.Closure.NSTriadKNHHBadCapacityProductRound63Exact as Product

physicalBadCapacityProduct :
  ∀ {environment effectiveViscosity} →
  Physical.PhysicalSelectedProfileMultiplicityInput environment effectiveViscosity → ℚ
physicalBadCapacityProduct input =
  Product.badCapacityProduct
    (Selected.selectedProfileCeiling (Physical.selectedProfile input))
    (Physical.badChargeMultiplicity input)

physicalHHBadOwnerEtaFactorsThroughCapacityProduct :
  ∀ {environment effectiveViscosity}
    (input : Physical.PhysicalSelectedProfileMultiplicityInput
      environment effectiveViscosity)
    (shell : Nat) →
  Owner.eta (Physical.physicalHHBadOwnerWithMultiplicity input shell)
  ≡ Product.hhBadTaxFromCapacityProduct (physicalBadCapacityProduct input)
physicalHHBadOwnerEtaFactorsThroughCapacityProduct input shell = refl

record PhysicalBadCapacityProductBound
    {environment effectiveViscosity}
    (input : Physical.PhysicalSelectedProfileMultiplicityInput
      environment effectiveViscosity)
    (budget : ℚ) : Set where
  field
    capacityProductBelowBudget : physicalBadCapacityProduct input ≤ budget

round68PhysicalHHBadTargetIsSingleCapacityProduct : Bool
round68PhysicalHHBadTargetIsSingleCapacityProduct = true

round68PhysicalHHBadTargetIsSingleCapacityProductIsTrue :
  round68PhysicalHHBadTargetIsSingleCapacityProduct ≡ true
round68PhysicalHHBadTargetIsSingleCapacityProductIsTrue = refl
