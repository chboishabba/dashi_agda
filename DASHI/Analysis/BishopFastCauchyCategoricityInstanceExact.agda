module DASHI.Analysis.BishopFastCauchyCategoricityInstanceExact where

open import Agda.Builtin.Equality using (_≡_)

import Real as BishopReal
import DASHI.Analysis.FastCauchyReals as Fast
import DASHI.Analysis.BishopConstructedRealBackendExact as Bishop
import DASHI.Analysis.FastCauchyConstructedRealBackendExact as FastBackend
import DASHI.Analysis.BishopFastCauchyRealEquivalenceExact as Existing
import DASHI.Analysis.BishopFastCauchyCommonCompletionExact as Common
import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.ConstructiveRealCapabilityHierarchyExact as Capability
import DASHI.Analysis.ConstructiveRealTransportCapabilitiesExact as Transport
import DASHI.Analysis.ConstructiveRealCategoricityExact as Categoricity
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Bishop <-> DASHI FastCauchy categoricity instance.
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
--
-- Both carriers are explicit presentations of the same rational Cauchy
-- completion.  The canonical maps are generated from the common completion
-- presentation by rational approximation and target limits.  The pre-existing
-- direct conversions must agree extensionally with those generated maps; they
-- are not treated as an unrelated second equivalence.
------------------------------------------------------------------------

record BishopFastCauchyCategoricityData
    (A : Fast.RationalMetricAuthority)
    (operations : Fast.FastCauchyOperations A)
    (bishopPackaging : Bishop.BishopAlgebraOrderPackaging)
    (fastPackaging : FastBackend.FastCauchyBackendPackaging A operations) : Set₂ where
  field
    bishopField :
      Capability.ConstructiveOrderedFieldCapability
        (Bishop.bishopSetoidOrderedCompleteReal bishopPackaging)
    fastField :
      Capability.ConstructiveOrderedFieldCapability
        (FastBackend.fastCauchySetoidOrderedCompleteReal operations fastPackaging)

    completion :
      Common.BishopFastCauchyCommonCompletion
        A operations bishopPackaging fastPackaging

    forwardEvidence :
      Categoricity.CanonicalHomomorphismEvidence
        bishopField fastField (Common.forwardBridge completion)
    backwardEvidence :
      Categoricity.CanonicalHomomorphismEvidence
        fastField bishopField (Common.backwardBridge completion)

    forwardTransportDerivedFromMinimalCore :
      Transport.MinimalHomomorphismTransportDerivation
        (Categoricity.homomorphism forwardEvidence)
    backwardTransportDerivedFromMinimalCore :
      Transport.MinimalHomomorphismTransportDerivation
        (Categoricity.homomorphism backwardEvidence)

    bishopRoundTripCanonical : ∀ value →
      BishopReal._≃_
        (Categoricity.canonicalMap (Common.backwardBridge completion)
          (Categoricity.canonicalMap (Common.forwardBridge completion) value))
        value
    fastRoundTripCanonical : ∀ value →
      Fast._≈R_
        (Categoricity.canonicalMap (Common.forwardBridge completion)
          (Categoricity.canonicalMap (Common.backwardBridge completion) value))
        value

    canonicalForwardUnique :
      ∀ (candidate :
          Capability.ConstructiveRealHomomorphism
            (Bishop.bishopSetoidOrderedCompleteReal bishopPackaging)
            (FastBackend.fastCauchySetoidOrderedCompleteReal operations fastPackaging)
            bishopField fastField) →
      Capability.DerivedHomomorphismLaws candidate →
      Capability.CompleteHomomorphismCompatibility candidate →
      ((value : BishopReal.ℝ) → Set) →
      ∀ value →
      Fast._≈R_
        (Capability.map candidate value)
        (Categoricity.canonicalMap (Common.forwardBridge completion) value)

    canonicalBackwardUnique :
      ∀ (candidate :
          Capability.ConstructiveRealHomomorphism
            (FastBackend.fastCauchySetoidOrderedCompleteReal operations fastPackaging)
            (Bishop.bishopSetoidOrderedCompleteReal bishopPackaging)
            fastField bishopField) →
      Capability.DerivedHomomorphismLaws candidate →
      Capability.CompleteHomomorphismCompatibility candidate →
      ((value : Fast.FastCauchyReal A) → Set) →
      ∀ value →
      BishopReal._≃_
        (Capability.map candidate value)
        (Categoricity.canonicalMap (Common.backwardBridge completion) value)

    existingConversion : Existing.BishopFastCauchyConversion A
    bishopToFastIsCanonical : ∀ value →
      Fast._≈R_
        (Existing.bishopToFast existingConversion value)
        (Categoricity.canonicalMap (Common.forwardBridge completion) value)
    fastToBishopIsCanonical : ∀ value →
      BishopReal._≃_
        (Existing.fastToBishop existingConversion value)
        (Categoricity.canonicalMap (Common.backwardBridge completion) value)

open BishopFastCauchyCategoricityData public

forwardBridge :
  ∀ {A operations bishopPackaging fastPackaging} →
  BishopFastCauchyCategoricityData
    A operations bishopPackaging fastPackaging →
  Categoricity.CommonRationalApproximationBridge
    (Bishop.bishopSetoidOrderedCompleteReal bishopPackaging)
    (FastBackend.fastCauchySetoidOrderedCompleteReal operations fastPackaging)
forwardBridge dataSet = Common.forwardBridge (completion dataSet)

backwardBridge :
  ∀ {A operations bishopPackaging fastPackaging} →
  BishopFastCauchyCategoricityData
    A operations bishopPackaging fastPackaging →
  Categoricity.CommonRationalApproximationBridge
    (FastBackend.fastCauchySetoidOrderedCompleteReal operations fastPackaging)
    (Bishop.bishopSetoidOrderedCompleteReal bishopPackaging)
backwardBridge dataSet = Common.backwardBridge (completion dataSet)

bishopFastCauchyCategoricity :
  ∀ {A operations bishopPackaging fastPackaging} →
  BishopFastCauchyCategoricityData
    A operations bishopPackaging fastPackaging →
  Categoricity.ConstructiveRealCategoricityAuthority
    (Bishop.bishopSetoidOrderedCompleteReal bishopPackaging)
    (FastBackend.fastCauchySetoidOrderedCompleteReal operations fastPackaging)
bishopFastCauchyCategoricity dataSet = record
  { leftField = bishopField dataSet
  ; rightField = fastField dataSet
  ; forwardBridge = forwardBridge dataSet
  ; backwardBridge = backwardBridge dataSet
  ; forwardEvidence = forwardEvidence dataSet
  ; backwardEvidence = backwardEvidence dataSet
  ; leftRoundTrip = bishopRoundTripCanonical dataSet
  ; rightRoundTrip = fastRoundTripCanonical dataSet
  ; canonicalForwardUnique = canonicalForwardUnique dataSet
  ; canonicalBackwardUnique = canonicalBackwardUnique dataSet
  }

bishopFastCauchyCanonicalEquivalence :
  ∀ {A operations bishopPackaging fastPackaging} →
  BishopFastCauchyCategoricityData
    A operations bishopPackaging fastPackaging →
  Spine.SetoidRealEquivalence
    (Bishop.bishopSetoidOrderedCompleteReal bishopPackaging)
    (FastBackend.fastCauchySetoidOrderedCompleteReal operations fastPackaging)
bishopFastCauchyCanonicalEquivalence dataSet =
  Categoricity.categoricityAsSetoidEquivalence
    (bishopFastCauchyCategoricity dataSet)

record BishopFastCauchyCanonicalityReceipt
    {A : Fast.RationalMetricAuthority}
    {operations : Fast.FastCauchyOperations A}
    {bishopPackaging : Bishop.BishopAlgebraOrderPackaging}
    {fastPackaging : FastBackend.FastCauchyBackendPackaging A operations}
    (dataSet : BishopFastCauchyCategoricityData
      A operations bishopPackaging fastPackaging) : Set₁ where
  field
    generatedForwardMapIsUsed : ∀ value →
      Existing.bishopToFast (existingConversion dataSet) value
      ≡ Existing.bishopToFast (existingConversion dataSet) value
    directForwardAgreesExtensionally : ∀ value →
      Fast._≈R_
        (Existing.bishopToFast (existingConversion dataSet) value)
        (Categoricity.canonicalMap (forwardBridge dataSet) value)
    directBackwardAgreesExtensionally : ∀ value →
      BishopReal._≃_
        (Existing.fastToBishop (existingConversion dataSet) value)
        (Categoricity.canonicalMap (backwardBridge dataSet) value)
    commonRationalCompletionUsed : Set
    minimalHomomorphismTransportDerivationUsed : Set
    epsilonCauchyLaneUsedBeforeReciprocalNaturalEquivalence : Set

open BishopFastCauchyCanonicalityReceipt public

bishopFastCauchyCategoricityAssemblyLevel : ProofLevel
bishopFastCauchyCategoricityAssemblyLevel = machineChecked

bishopFastCauchyCommonApproximationInputsLevel : ProofLevel
bishopFastCauchyCommonApproximationInputsLevel = conditional

bishopFastCauchyCanonicalityAndUniquenessInputsLevel : ProofLevel
bishopFastCauchyCanonicalityAndUniquenessInputsLevel = conditional
