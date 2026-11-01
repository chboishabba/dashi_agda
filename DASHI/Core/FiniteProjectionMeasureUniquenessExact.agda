module DASHI.Core.FiniteProjectionMeasureUniquenessExact where

------------------------------------------------------------------------
-- FINITE-PROJECTION / GLOBAL-STATE UNIQUENESS COMPILER
--
-- Generic x-pollination from the p-adic Gibbs lane.
--
-- Many inverse-limit systems are observed through a compatible family of
-- finite quotients.  Equality of every finite projected law determines the
-- global law once the finite cylinder observations are known to be
-- determining.  This file keeps that final extensionality receipt explicit
-- rather than pretending finite equality alone proves analytic measure equality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

record FiniteProjectionSystem : Set₂ where
  field
    GlobalState : Set
    FiniteState : Nat → Set
    project : (n : Nat) → GlobalState → FiniteState n

open FiniteProjectionSystem public

record ProjectedLawFamily (system : FiniteProjectionSystem) : Set₂ where
  field
    Law : Set
    projectLaw : (n : Nat) → Law → Set

open ProjectedLawFamily public

record FiniteProjectionUniquenessData : Set₂ where
  field
    system : FiniteProjectionSystem
    family : ProjectedLawFamily system
    leftLaw rightLaw : Law family

    allFiniteProjectedLawsEqual :
      (n : Nat) →
      projectLaw family n leftLaw ≡ projectLaw family n rightLaw

    finiteProjectionsDetermineGlobalLaw :
      ((n : Nat) →
        projectLaw family n leftLaw ≡ projectLaw family n rightLaw) →
      leftLaw ≡ rightLaw

open FiniteProjectionUniquenessData public

globalLawEqualityFromFiniteProjections :
  (data : FiniteProjectionUniquenessData) →
  leftLaw data ≡ rightLaw data
globalLawEqualityFromFiniteProjections data =
  finiteProjectionsDetermineGlobalLaw data
    (allFiniteProjectedLawsEqual data)

record PromotionBoundary : Set where
  constructor promotionBoundary
  field
    finiteProjectedEqualityAloneEnough : Bool
    determiningCylinderReceiptRequired : Bool
    compatibleInverseLimitArchitectureReusable : Bool
    measureTopologyHidden : Bool

canonicalPromotionBoundary : PromotionBoundary
canonicalPromotionBoundary =
  promotionBoundary false true true false

finiteEqualityDoesNotSkipExtensionality :
  PromotionBoundary.finiteProjectedEqualityAloneEnough
    canonicalPromotionBoundary
  ≡ false
finiteEqualityDoesNotSkipExtensionality = refl
