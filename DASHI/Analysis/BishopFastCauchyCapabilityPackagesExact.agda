module DASHI.Analysis.BishopFastCauchyCapabilityPackagesExact where

open import Agda.Builtin.Equality using (_≡_)

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
    bishopConstructiveField :
      Capability.ConstructiveOrderedFieldCapability
        (Bishop.bishopSetoidOrderedCompleteReal packaging)
    bishopRationals :
      Capability.RationalEmbeddingStructure
        (Bishop.bishopSetoidOrderedCompleteReal packaging)
    bishopRationalDensity :
      Capability.RationalDensityStructure
        (Bishop.bishopSetoidOrderedCompleteReal packaging) bishopRationals
    bishopNaturalMajorization :
      Capability.NaturalMajorizationStructure
        (Bishop.bishopSetoidOrderedCompleteReal packaging)
    bishopDensityMajorizationBridge :
      Capability.DensityMajorizationBridge
        (Bishop.bishopSetoidOrderedCompleteReal packaging)
        bishopRationals bishopRationalDensity bishopNaturalMajorization
    bishopEffectiveConvergence :
      Capability.EffectiveConvergenceStructure
        (Bishop.bishopSetoidOrderedCompleteReal packaging)
    bishopEffectiveLogicalOrder :
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
  ; constructiveField = bishopConstructiveField dataSet
  ; rationals = bishopRationals dataSet
  ; rationalDensity = bishopRationalDensity dataSet
  ; naturalMajorization = bishopNaturalMajorization dataSet
  ; densityMajorizationBridge = bishopDensityMajorizationBridge dataSet
  ; effectiveConvergence = bishopEffectiveConvergence dataSet
  ; effectiveLogicalOrder = bishopEffectiveLogicalOrder dataSet
  }

record FastCauchyCompleteRealCapabilityData
    (A : Fast.RationalMetricAuthority)
    (operations : Fast.FastCauchyOperations A)
    (packaging : FastBackend.FastCauchyBackendPackaging A operations) : Set₂ where
  field
    fastConstructiveField :
      Capability.ConstructiveOrderedFieldCapability
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations packaging)
    fastRationals :
      Capability.RationalEmbeddingStructure
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations packaging)
    fastRationalDensity :
      Capability.RationalDensityStructure
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations packaging)
        fastRationals
    fastNaturalMajorization :
      Capability.NaturalMajorizationStructure
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations packaging)
    fastDensityMajorizationBridge :
      Capability.DensityMajorizationBridge
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations packaging)
        fastRationals fastRationalDensity fastNaturalMajorization
    fastEffectiveConvergence :
      Capability.EffectiveConvergenceStructure
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations packaging)
    fastEffectiveLogicalOrder :
      Transport.EffectiveLogicalOrderView
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations packaging)

open FastCauchyCompleteRealCapabilityData public

fastCauchyCompleteRealPackage :
  ∀ {A operations packaging} →
  FastCauchyCompleteRealCapabilityData A operations packaging →
  Package.ConstructiveCompleteRealPackage
fastCauchyCompleteRealPackage
  {operations = operations} {packaging = packaging} dataSet = record
  { packageName = "DASHI quotient-free FastCauchy complete reals"
  ; backend = FastBackend.fastCauchyConstructiveRealBackend operations packaging
  ; constructiveField = fastConstructiveField dataSet
  ; rationals = fastRationals dataSet
  ; rationalDensity = fastRationalDensity dataSet
  ; naturalMajorization = fastNaturalMajorization dataSet
  ; densityMajorizationBridge = fastDensityMajorizationBridge dataSet
  ; effectiveConvergence = fastEffectiveConvergence dataSet
  ; effectiveLogicalOrder = fastEffectiveLogicalOrder dataSet
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
      CommonQ → Capability.Q (bishopRationals bishopCapabilities)
    fastQDecode :
      CommonQ → Capability.Q (fastRationals fastCapabilities)

    commonRationalEmbeddingAgreement : Set
    packageCauchyDefinitionsCompatible : Set

open BishopFastCauchyPackagePair public

bishopCapabilityPackageAssemblyLevel : ProofLevel
bishopCapabilityPackageAssemblyLevel = machineChecked

fastCauchyCapabilityPackageAssemblyLevel : ProofLevel
fastCauchyCapabilityPackageAssemblyLevel = machineChecked

bishopFastCauchyCapabilityInstanceInputsLevel : ProofLevel
bishopFastCauchyCapabilityInstanceInputsLevel = conditional
