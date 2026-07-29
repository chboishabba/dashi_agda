module DASHI.Analysis.BishopFastCauchyCapabilityPackagesExact where

open import Agda.Builtin.Equality using (_≡_)

import Real as BishopReal
import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.BishopConstructedRealBackendExact as Bishop
import DASHI.Analysis.FastCauchyConstructedRealBackendExact as FastBackend
import DASHI.Analysis.ConstructiveRealCapabilityHierarchyExact as Capability
import DASHI.Analysis.ConstructiveRealTransportCapabilitiesExact as Transport
import DASHI.Analysis.ConstructiveCompleteRealPackageExact as Package
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Stable Bishop and FastCauchy complete-real capability packages.
--
-- Herman Geuvers and Milad Niqui,
-- "Constructive Reals in Coq: Axioms and Categoricity",
-- Types for Proofs and Programs, LNCS 2277 (2002), 79--95.
-- DOI: 10.1007/3-540-45842-5_6.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- Dalhousie University, April 2022, arXiv:2205.08354, no DOI.
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- 582c6afcdf805d06730c8c0aa970f4a6e033b611.
------------------------------------------------------------------------

record BishopCompleteRealCapabilityData
    (packaging : Bishop.BishopAlgebraOrderPackaging) : Set₂ where
  field
    constructiveField :
      Capability.ConstructiveOrderedFieldCapability
        (Bishop.bishopSetoidOrderedCompleteReal packaging)
    rationals :
      Capability.RationalEmbeddingStructure
        (Bishop.bishopSetoidOrderedCompleteReal packaging)
    rationalDensity :
      Capability.RationalDensityStructure
        (Bishop.bishopSetoidOrderedCompleteReal packaging) rationals
    naturalMajorization :
      Capability.NaturalMajorizationStructure
        (Bishop.bishopSetoidOrderedCompleteReal packaging)
    densityMajorizationBridge :
      Capability.DensityMajorizationBridge
        (Bishop.bishopSetoidOrderedCompleteReal packaging)
        rationals rationalDensity naturalMajorization
    effectiveConvergence :
      Capability.EffectiveConvergenceStructure
        (Bishop.bishopSetoidOrderedCompleteReal packaging)
    effectiveLogicalOrder :
      Transport.EffectiveLogicalOrderView
        (Bishop.bishopSetoidOrderedCompleteReal packaging)

open BishopCompleteRealCapabilityData public

bishopCompleteRealPackage :
  ∀ {packaging} →
  BishopCompleteRealCapabilityData packaging →
  Package.ConstructiveCompleteRealPackage
bishopCompleteRealPackage {packaging} dataSet = record
  { packageName = "Bishop regular rational-sequence complete reals"
  ; backend = Bishop.bishopConstructiveRealBackend packaging
  ; constructiveField = constructiveField dataSet
  ; rationals = rationals dataSet
  ; rationalDensity = rationalDensity dataSet
  ; naturalMajorization = naturalMajorization dataSet
  ; densityMajorizationBridge = densityMajorizationBridge dataSet
  ; effectiveConvergence = effectiveConvergence dataSet
  ; effectiveLogicalOrder = effectiveLogicalOrder dataSet
  }

record FastCauchyCompleteRealCapabilityData
    (A : Fast.RationalMetricAuthority)
    (operations : Fast.FastCauchyOperations A)
    (packaging : FastBackend.FastCauchyBackendPackaging A operations) : Set₂ where
  field
    constructiveField :
      Capability.ConstructiveOrderedFieldCapability
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations packaging)
    rationals :
      Capability.RationalEmbeddingStructure
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations packaging)
    rationalDensity :
      Capability.RationalDensityStructure
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations packaging)
        rationals
    naturalMajorization :
      Capability.NaturalMajorizationStructure
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations packaging)
    densityMajorizationBridge :
      Capability.DensityMajorizationBridge
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations packaging)
        rationals rationalDensity naturalMajorization
    effectiveConvergence :
      Capability.EffectiveConvergenceStructure
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations packaging)
    effectiveLogicalOrder :
      Transport.EffectiveLogicalOrderView
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations packaging)

open FastCauchyCompleteRealCapabilityData public

fastCauchyCompleteRealPackage :
  ∀ {A operations packaging} →
  FastCauchyCompleteRealCapabilityData A operations packaging →
  Package.ConstructiveCompleteRealPackage
fastCauchyCompleteRealPackage {operations = operations} {packaging = packaging} dataSet = record
  { packageName = "DASHI quotient-free FastCauchy complete reals"
  ; backend = FastBackend.fastCauchyConstructiveRealBackend operations packaging
  ; constructiveField = constructiveField dataSet
  ; rationals = rationals dataSet
  ; rationalDensity = rationalDensity dataSet
  ; naturalMajorization = naturalMajorization dataSet
  ; densityMajorizationBridge = densityMajorizationBridge dataSet
  ; effectiveConvergence = effectiveConvergence dataSet
  ; effectiveLogicalOrder = effectiveLogicalOrder dataSet
  }

record BishopFastCauchyPackagePair
    (A : Fast.RationalMetricAuthority)
    (operations : Fast.FastCauchyOperations A)
    (bishopPackaging : Bishop.BishopAlgebraOrderPackaging)
    (fastPackaging : FastBackend.FastCauchyBackendPackaging A operations) : Set₂ where
  field
    bishopCapabilities : BishopCompleteRealCapabilityData bishopPackaging
    fastCapabilities :
      FastCauchyCompleteRealCapabilityData A operations fastPackaging

    CommonQ : Set
    bishopQDecode :
      CommonQ → Capability.Q (BishopCompleteRealCapabilityData.rationals bishopCapabilities)
    fastQDecode :
      CommonQ → Capability.Q (FastCauchyCompleteRealCapabilityData.rationals fastCapabilities)

    commonRationalEmbeddingAgreement : Set
    packageCauchyDefinitionsCompatible : Set

open BishopFastCauchyPackagePair public

bishopCapabilityPackageAssemblyLevel : ProofLevel
bishopCapabilityPackageAssemblyLevel = machineChecked

fastCauchyCapabilityPackageAssemblyLevel : ProofLevel
fastCauchyCapabilityPackageAssemblyLevel = machineChecked

bishopFastCauchyCapabilityInstanceInputsLevel : ProofLevel
bishopFastCauchyCapabilityInstanceInputsLevel = conditional
