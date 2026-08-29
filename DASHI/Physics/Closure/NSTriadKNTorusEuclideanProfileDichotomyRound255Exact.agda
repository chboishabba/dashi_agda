module DASHI.Physics.Closure.NSTriadKNTorusEuclideanProfileDichotomyRound255Exact where

------------------------------------------------------------------------
-- ROUND255 / PERIODIC CRITICAL SEQUENCE -> TWO-BRANCH PROFILE CARRIER
--
-- Gallagher 2001 is an R^3 H^{1/2}-bounded profile theorem.  A periodic
-- critical sequence has a scale-one periodic branch and shrinking cores.
-- Therefore the safe bidi carrier is a dichotomy:
--   * periodic compact/weak profile at scale one;
--   * shrinking core, rescaled to an R^3 Gallagher profile.
-- We do not force the scale-one branch through an R^3 blow-up map.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Sum.Base using (_⊎_)

record PeriodicProfileBranch
    {ℓ : Level} (TorusState : Set ℓ) : Set (lsuc ℓ) where
  field
    profile : TorusState
    selectedSubsequence : Nat → Nat
    scaleOneCompactness : Set ℓ

record EuclideanBlowupProfileBranch
    {ℓ : Level}
    (TorusState EuclideanState : Set ℓ) : Set (lsuc ℓ) where
  field
    selectedSubsequence : Nat → Nat
    shrinkingScale : Nat → TorusState
    rescaledProfile : EuclideanState
    criticalNormTransport : Set ℓ
    divergenceFreeTransport : Set ℓ
    mixedDefectTransport : Set ℓ
    gallagherProfileDecomposition : Set ℓ

record TorusToProfileCarrier
    {ℓ : Level}
    (TorusState EuclideanState : Set ℓ) : Set (lsuc ℓ) where
  field
    branch :
      PeriodicProfileBranch TorusState
      ⊎ EuclideanBlowupProfileBranch TorusState EuclideanState

open TorusToProfileCarrier public

round255ScaleOnePeriodicBranchPreserved : Bool
round255ScaleOnePeriodicBranchPreserved = true

round255ShrinkingBranchUsesEuclideanBlowup : Bool
round255ShrinkingBranchUsesEuclideanBlowup = true

round255WholeTorusSequenceBlindlyIdentifiedWithR3 : Bool
round255WholeTorusSequenceBlindlyIdentifiedWithR3 = false

round255GallagherAnalyticInstanceKernelDerivedHere : Bool
round255GallagherAnalyticInstanceKernelDerivedHere = false

round255PackageAClosed : Bool
round255PackageAClosed = false

round255ScaleOnePeriodicBranchPreservedIsTrue :
  round255ScaleOnePeriodicBranchPreserved ≡ true
round255ScaleOnePeriodicBranchPreservedIsTrue = refl

round255WholeTorusSequenceBlindlyIdentifiedWithR3IsFalse :
  round255WholeTorusSequenceBlindlyIdentifiedWithR3 ≡ false
round255WholeTorusSequenceBlindlyIdentifiedWithR3IsFalse = refl
