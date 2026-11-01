module DASHI.Physics.YangMills.BalabanStepVCanonicalAnimalMarginExact where

------------------------------------------------------------------------
-- PRIMARY AUTHORITY
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization II: Localization, Exponentiation, and Bounds
-- for the R-Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- PURPOSE
--
-- The relevant numerical frontier is not an unnamed smallness token.  Once
-- P06 supplies the canonical rooted-animal constant C_anim and the physical
-- activity supplies decay kappa, the sharp scalar interface is
--
--   log(C_anim) < kappa,
--
-- equivalently C_anim * exp(-kappa) < 1 for a positive real exponential/log
-- backend.  This module owns the transport from the logarithmic margin to the
-- weighted-ratio certificate and packages the constants requested by the
-- physical Step-V influence lane.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy as Entropy
import DASHI.Physics.YangMills.BalabanP06CanonicalAnimalConstantExact as P06
import DASHI.Physics.YangMills.GraphCombinatorics as Graph
open import DASHI.Physics.YangMills.CompactLieProofLevel

record LogAnimalMarginKernel (Bound : Set) : Set₁ where
  field
    fromNat : Nat → Bound
    one : Bound
    multiply : Bound → Bound → Bound
    logarithm : Bound → Bound
    expNegative : Bound → Bound
    StrictlyLess : Bound → Bound → Set

    logMarginImpliesWeightedRatioBelowOne :
      ∀ (animalConstant : Nat) (kappa : Bound) →
      StrictlyLess (logarithm (fromNat animalConstant)) kappa →
      StrictlyLess
        (multiply (fromNat animalConstant) (expNegative kappa))
        one

open LogAnimalMarginKernel public

record CanonicalAnimalDecayMargin
    {Bound : Set}
    (kernel : LogAnimalMarginKernel Bound)
    (package : Entropy.P06ModelLeafDischargePackage) : Set₁ where
  field
    kappa : Bound

    logarithmicMargin :
      StrictlyLess kernel
        (logarithm kernel
          (fromNat kernel (P06.canonicalAnimalConstant package)))
        kappa

    weightedRatio : Bound
    weightedRatioMeaning :
      weightedRatio
        ≡ multiply kernel
            (fromNat kernel (P06.canonicalAnimalConstant package))
            (expNegative kernel kappa)

    weightedRatioBelowOne :
      StrictlyLess kernel weightedRatio (one kernel)

open CanonicalAnimalDecayMargin public

canonicalAnimalDecayMargin :
  ∀ {Bound : Set}
    {kernel : LogAnimalMarginKernel Bound}
    {package : Entropy.P06ModelLeafDischargePackage} →
  (kappa : Bound) →
  StrictlyLess kernel
    (logarithm kernel
      (fromNat kernel (P06.canonicalAnimalConstant package)))
    kappa →
  CanonicalAnimalDecayMargin kernel package
canonicalAnimalDecayMargin {kernel = kernel} {package = package}
  kappa logMargin = record
  { kappa = kappa
  ; logarithmicMargin = logMargin
  ; weightedRatio =
      multiply kernel
        (fromNat kernel (P06.canonicalAnimalConstant package))
        (expNegative kernel kappa)
  ; weightedRatioMeaning = refl
  ; weightedRatioBelowOne =
      logMarginImpliesWeightedRatioBelowOne kernel
        (P06.canonicalAnimalConstant package)
        kappa
        logMargin
  }

p06ComplexityLeaf :
  (package : Entropy.P06ModelLeafDischargePackage) →
  Graph.ReducedSkeletonComplexityControlledByDiameter
    (Entropy.BalabanGraphAdapter.supportGraph
      (Entropy.P06ModelLeafDischargePackage.graphAdapter package))
p06ComplexityLeaf package =
  Entropy.BalabanReducedSkeletonComplexityAdapter.reducedComplexityLeaf
    (Entropy.P06ModelLeafDischargePackage.reducedSkeletonComplexityAdapter
      package)

record StepVInfluenceConstantBundle
    {Bound : Set}
    (kernel : LogAnimalMarginKernel Bound) : Set₁ where
  field
    p06ModelLeaf : Entropy.P06ModelLeafDischargePackage

    K : Nat
    B : Nat
    C-skeleton : Nat
    C-decoration : Nat
    C-animal : Nat

    KIsCanonical :
      K ≡ Graph.ReducedSkeletonComplexityControlledByDiameter.K
        (p06ComplexityLeaf p06ModelLeaf)

    BIsCanonical :
      B ≡ Graph.ReducedSkeletonComplexityControlledByDiameter.B
        (p06ComplexityLeaf p06ModelLeaf)

    skeletonConstantIsCanonical :
      C-skeleton ≡ P06.canonicalSkeletonConstant p06ModelLeaf

    decorationConstantIsCanonical :
      C-decoration ≡ P06.canonicalDecorationConstant p06ModelLeaf

    animalConstantIsCanonical :
      C-animal ≡ P06.canonicalAnimalConstant p06ModelLeaf

    kappa kappaPrime oscillationConstant : Bound
    polynomialDegree : Nat

    animalDecayMargin :
      CanonicalAnimalDecayMargin kernel p06ModelLeaf

    OscillationProfile : Set
    oscillationProfile : OscillationProfile

    WeightedActivitySummabilityProfile : Set
    weightedActivitySummabilityProfile :
      WeightedActivitySummabilityProfile

open StepVInfluenceConstantBundle public

stepVInfluenceConstantBundle :
  ∀ {Bound : Set}
    {kernel : LogAnimalMarginKernel Bound} →
  (package : Entropy.P06ModelLeafDischargePackage) →
  (kappa kappaPrime oscillationConstant : Bound) →
  (polynomialDegree : Nat) →
  CanonicalAnimalDecayMargin kernel package →
  (OscillationProfile : Set) →
  OscillationProfile →
  (WeightedActivitySummabilityProfile : Set) →
  WeightedActivitySummabilityProfile →
  StepVInfluenceConstantBundle kernel
stepVInfluenceConstantBundle package kappa kappaPrime oscillationConstant
  polynomialDegree margin OscillationProfile oscillationProfile
  WeightedActivitySummabilityProfile weightedActivityProfile = record
  { p06ModelLeaf = package
  ; K = Graph.ReducedSkeletonComplexityControlledByDiameter.K
      (p06ComplexityLeaf package)
  ; B = Graph.ReducedSkeletonComplexityControlledByDiameter.B
      (p06ComplexityLeaf package)
  ; C-skeleton = P06.canonicalSkeletonConstant package
  ; C-decoration = P06.canonicalDecorationConstant package
  ; C-animal = P06.canonicalAnimalConstant package
  ; KIsCanonical = refl
  ; BIsCanonical = refl
  ; skeletonConstantIsCanonical = refl
  ; decorationConstantIsCanonical = refl
  ; animalConstantIsCanonical = refl
  ; kappa = kappa
  ; kappaPrime = kappaPrime
  ; oscillationConstant = oscillationConstant
  ; polynomialDegree = polynomialDegree
  ; animalDecayMargin = margin
  ; OscillationProfile = OscillationProfile
  ; oscillationProfile = oscillationProfile
  ; WeightedActivitySummabilityProfile =
      WeightedActivitySummabilityProfile
  ; weightedActivitySummabilityProfile = weightedActivityProfile
  }

stepVCanonicalAnimalMarginReductionLevel : ProofLevel
stepVCanonicalAnimalMarginReductionLevel = machineChecked

stepVPhysicalLogExpAndOscillationInputsLevel : ProofLevel
stepVPhysicalLogExpAndOscillationInputsLevel = conditional
