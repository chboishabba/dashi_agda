module DASHI.Analysis.AdelicSpectralClaimStrengthAuditExact where

------------------------------------------------------------------------
-- CLAIM-STRENGTH AUDIT FOR adelic-spectral-zeta
--
-- This is a source-facing fail-closed ledger.  It distinguishes theorem
-- existence from theorem strength and prevents a prose theorem label from
-- upgrading a weaker formal statement.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.NonArchimedeanSpectralOrbitHypervoxelExact as Spectral

record ClaimStrengthAudit : Set where
  constructor claimStrengthAudit
  field
    declaration : String
    sourcePath : String
    machineChecked : Bool
    provesAdvertisedStrength : Bool
    additionalHypothesisOrWeldRequired : Bool

------------------------------------------------------------------------
-- Strong spectral/algebraic lane.
------------------------------------------------------------------------

charActionAudit : ClaimStrengthAudit
charActionAudit = claimStrengthAudit
  "collatzDirMatrix_char_action"
  "formalization/Formalization/Dynamics/SpectralCircle.lean"
  true true false

cyclotomicProductAudit : ClaimStrengthAudit
cyclotomicProductAudit = claimStrengthAudit
  "W_1_mul_W_2_eq_two"
  "formalization/Formalization/Dynamics/CyclotomicProduct.lean"
  true true false

traceVanishingAudit : ClaimStrengthAudit
traceVanishingAudit = claimStrengthAudit
  "directed_trace_odd_vanishes"
  "formalization/Formalization/Spectral/SchreierDynamicalTrace.lean"
  true true false

spatialSpectralCircleAudit : ClaimStrengthAudit
spatialSpectralCircleAudit = claimStrengthAudit
  "spectral_circle"
  "formalization/Formalization/Dynamics/SpectralCircle.lean"
  true false true

------------------------------------------------------------------------
-- AF lane: the direct-limit embedding theorem is substantive and reusable,
-- but does not create a bridge to the spectral operator by itself.
------------------------------------------------------------------------

dyadicDimensionGroupAudit : ClaimStrengthAudit
dyadicDimensionGroupAudit = claimStrengthAudit
  "toRat_injective / mem_dyadicRationals_iff"
  "formalization/Formalization/Quantum/BratteliAF.lean"
  true true false

------------------------------------------------------------------------
-- RoPE lane: exact geometric invariance is real; transformer optimality is not
-- a consequence of the rotation identity alone.
------------------------------------------------------------------------

ropeRelativeInvarianceAudit : ClaimStrengthAudit
ropeRelativeInvarianceAudit = claimStrengthAudit
  "rope_medoid_relative_invariance"
  "formalization/Formalization/Analysis/RoPECoherence.lean"
  true true false

record RoPEInferenceBoundary : Set where
  constructor ropeInferenceBoundary
  field
    relativeRotationIdentityIsOwned : Bool
    keyAveragingCanAttenuateNormIsOwned : Bool
    medoidIsGloballyOptimalKVCompression : Bool
    modelQualityImprovementFollowsFromGeometryAlone : Bool

canonicalRoPEInferenceBoundary : RoPEInferenceBoundary
canonicalRoPEInferenceBoundary =
  ropeInferenceBoundary true true false false

------------------------------------------------------------------------
-- Holographic tensor-network lane.
--
-- The named theorem ryu_takayanagi_discrete has the shape
--   ∃ entropy, entropy = k * log 2
-- for a PerfectTensor argument.  That existential equality is machine checked,
-- but by itself does not establish that entropy is computed from the previously
-- defined contracted boundary state.  The same-object entropy weld therefore
-- remains explicit here.
------------------------------------------------------------------------

holographicAreaLawAudit : ClaimStrengthAudit
holographicAreaLawAudit = claimStrengthAudit
  "ryu_takayanagi_discrete"
  "formalization/Formalization/Quantum/HolographicTensorNetwork.lean"
  true false true

record HolographicSameObjectBoundary : Set where
  constructor holographicSameObjectBoundary
  field
    existentialEntropyValueExists : Bool
    entropyIsWeldedToContractedBoundaryState : Bool
    areaLawImpliesAdSCFT : Bool

canonicalHolographicSameObjectBoundary : HolographicSameObjectBoundary
canonicalHolographicSameObjectBoundary =
  holographicSameObjectBoundary true false false

------------------------------------------------------------------------
-- Multi-prime routing lane.
--
-- dag_treewidth_covering is a valid consumer theorem, but its decomposition
-- hypothesis contains edge_covered for every graph edge.  Thus it proves that
-- a supplied cover covers; it does not prove arbitrary DAGs admit such covers.
--
-- activeFraction_le_one proves only activeFraction p r <= 1.  It is not the
-- advertised depth-decaying p^(-r) sparsity theorem.
------------------------------------------------------------------------

multiPrimeCoverAudit : ClaimStrengthAudit
multiPrimeCoverAudit = claimStrengthAudit
  "dag_treewidth_covering"
  "formalization/Formalization/Analysis/MultiPrimeCover.lean"
  true false true

activeFractionAudit : ClaimStrengthAudit
activeFractionAudit = claimStrengthAudit
  "activeFraction_le_one"
  "formalization/Formalization/Analysis/MultiPrimeCover.lean"
  true false true

record MultiPrimeBoundary : Set where
  constructor multiPrimeBoundary
  field
    suppliedDecompositionImpliesCoverage : Bool
    arbitraryDAGAdmitsRequiredDecomposition : Bool
    activeFractionLeOneIsOwned : Bool
    activeFractionLeOneImpliesDepthExponentialSparsity : Bool
    proseSparsityClaimMayBePromoted : Bool

canonicalMultiPrimeBoundary : MultiPrimeBoundary
canonicalMultiPrimeBoundary =
  multiPrimeBoundary true false true false false

------------------------------------------------------------------------
-- Cross-fibre bridge discipline.
------------------------------------------------------------------------

record CrossFibreBridgeBoundary : Set where
  constructor crossFibreBridgeBoundary
  field
    spectralToAFBridgeIsAutomatic : Bool
    spectralToRoPEBridgeIsAutomatic : Bool
    spectralToHolographyBridgeIsAutomatic : Bool
    spectralToMultiPrimeRoutingBridgeIsAutomatic : Bool
    architecturalAnalogyMayBeRecorded : Bool
    theoremTransportNeedsTypedWeld : Bool

canonicalCrossFibreBridgeBoundary : CrossFibreBridgeBoundary
canonicalCrossFibreBridgeBoundary =
  crossFibreBridgeBoundary false false false false true true

multiPrimePromotionIsFailClosed :
  MultiPrimeBoundary.proseSparsityClaimMayBePromoted canonicalMultiPrimeBoundary
  ≡ false
multiPrimePromotionIsFailClosed = refl

holographicSameObjectIsFailClosed :
  HolographicSameObjectBoundary.entropyIsWeldedToContractedBoundaryState
    canonicalHolographicSameObjectBoundary
  ≡ false
holographicSameObjectIsFailClosed = refl

crossFibreAutomaticTransportIsRejected :
  CrossFibreBridgeBoundary.spectralToRoPEBridgeIsAutomatic
    canonicalCrossFibreBridgeBoundary
  ≡ false
crossFibreAutomaticTransportIsRejected = refl
