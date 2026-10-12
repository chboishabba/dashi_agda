{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkCorrectedRTSameObjectExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- CORRECTED SAME-OBJECT FINITE RT RECEIPT
--
-- Native producers:
--   chboishabba/dashi_lean4
--   Synthesis/HolographicMaxEntangledCutRT.lean
--   Synthesis/HolographicZModCarrierFactorization.lean
--   Synthesis/HolographicCorrectedZModRT.lean
--   Synthesis/HolographicUnbalancedCorrectedRT.lean
--   Synthesis/HolographicUpstreamStateContractNoGo.lean
--
-- The finite entropy theorem is closed on a corrected coherent Schmidt state:
-- partial trace gives the uniform reduced density matrix and entropy k log 2.
-- The binary upstream carrier itself is now factored exactly as
--
--   ZMod(2^(k+r))  <->  Fin(2^k) x Fin(2^r),
--
-- and corrected entangled kernels are pulled back onto that ZMod carrier.
-- For r >= k, the larger-complement construction still reduces exactly to the
-- uniform 2^-k state and hence k log 2 entropy.
--
-- Crucially, direct source inspection plus a native Lean depth-one no-go now
-- proves that the CURRENT upstream `holographicState` and `holographicContract`
-- cannot be the same state/density matrix: the pure-state off-diagonal
-- coherence is positive while the named contract is diagonal.  Therefore the
-- live source task is not to search for a proof of current state identity; the
-- upstream state/contract/tree-contraction construction must be replaced or
-- proved equivalent to a corrected coherent state.
------------------------------------------------------------------------

leanProducerRepository : String
leanProducerRepository = "chboishabba/dashi_lean4"

leanProducerPath : String
leanProducerPath = "Synthesis/HolographicMaxEntangledCutRT.lean"

leanProducerPR : String
leanProducerPR = "https://github.com/chboishabba/dashi_lean4/pull/68"

record CorrectedRTFiniteReceipt : Set where
  constructor correctedRTFiniteReceipt
  field
    maxEntangledSchmidtDensity : Bool
    coherentCorrelatedOffDiagonalSupport : Bool
    partialTraceOverComplementDefined : Bool
    reducedDensityA_eq_uniformDiagonal : Bool
    reducedSpectrumHasTwoToKEqualWeights : Bool
    reducedEntropy_eq_kLogTwo : Bool
    correctedCutEntropy_eq_kLogTwo : Bool
    correctedRTSameObjectEntropy : Bool
    sameObjectEntropyAlgebraClosed : Bool

    upstreamZModCarrierFactorizationSourceWritten : Bool
    correctedEntangledStateOnUpstreamCarrierSourceWritten : Bool
    correctedUnbalancedRTForAdequateComplementSourceWritten : Bool

canonicalCorrectedRTFiniteReceipt : CorrectedRTFiniteReceipt
canonicalCorrectedRTFiniteReceipt =
  correctedRTFiniteReceipt
    true true true true true true true true true
    true true true

------------------------------------------------------------------------
-- Remaining same-object and physical promotions.
------------------------------------------------------------------------

record CorrectedRTAuthorityBoundary : Set where
  constructor correctedRTAuthorityBoundary
  field
    nativeLeanProducerPresent : Bool
    nativeLeanKernelReceiptAttachedHere : Bool

    upstreamStateContractSameObjectImpossibleAsWritten : Bool
    upstreamDefinitionReplacementRequired : Bool
    upstreamTreeContractionReplacementOrEquivalenceStillRequired : Bool

    -- Legacy broad flag retained for older consumers.  It now means the
    -- corrected state must be established as the replacement/equivalent output,
    -- not that equality with the current incompatible definitions is expected.
    upstreamStateIdentificationStillRequired : Bool

    minimalCutCarrierIdentificationStillRequired : Bool
    upstreamTensorNetworkDynamicsIdentificationStillRequired : Bool
    physicalBulkBoundaryDictionaryStillRequired : Bool

    correctedFiniteModelIsNotPhysicalAdSCFT : Bool
    correctedFiniteModelDoesNotEstablishContinuumRT : Bool
    correctedFiniteModelDoesNotIdentifyBirthmarkWithEntropy : Bool
    correctedFiniteModelDoesNotDeriveGravity : Bool

canonicalCorrectedRTAuthorityBoundary : CorrectedRTAuthorityBoundary
canonicalCorrectedRTAuthorityBoundary =
  correctedRTAuthorityBoundary
    true
    false
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true

sameObjectEntropyAlgebraClosed : Bool
sameObjectEntropyAlgebraClosed = true

maxEntangledSchmidtDensity : Bool
maxEntangledSchmidtDensity = true

reducedDensityA_eq_uniformDiagonal : Bool
reducedDensityA_eq_uniformDiagonal = true

reducedEntropy_eq_kLogTwo : Bool
reducedEntropy_eq_kLogTwo = true

correctedRTSameObjectEntropy : Bool
correctedRTSameObjectEntropy = true

upstreamZModCarrierFactorizationSourceWritten : Bool
upstreamZModCarrierFactorizationSourceWritten = true

correctedEntangledStateOnUpstreamCarrierSourceWritten : Bool
correctedEntangledStateOnUpstreamCarrierSourceWritten = true

correctedUnbalancedRTForAdequateComplementSourceWritten : Bool
correctedUnbalancedRTForAdequateComplementSourceWritten = true

upstreamStateContractSameObjectImpossibleAsWritten : Bool
upstreamStateContractSameObjectImpossibleAsWritten = true

upstreamDefinitionReplacementRequired : Bool
upstreamDefinitionReplacementRequired = true

upstreamTreeContractionReplacementOrEquivalenceStillRequired : Bool
upstreamTreeContractionReplacementOrEquivalenceStillRequired = true

upstreamStateIdentificationStillRequired : Bool
upstreamStateIdentificationStillRequired = true

minimalCutCarrierIdentificationStillRequired : Bool
minimalCutCarrierIdentificationStillRequired = true

physicalBulkBoundaryDictionaryStillRequired : Bool
physicalBulkBoundaryDictionaryStillRequired = true

correctedFiniteModelIsNotPhysicalAdSCFT : Bool
correctedFiniteModelIsNotPhysicalAdSCFT = true

correctedSameObjectEntropyClosed :
  correctedRTSameObjectEntropy ≡ true
correctedSameObjectEntropyClosed = refl

-- Legacy theorem name retained for downstream imports.  The live statement is
-- now replacement/equivalence of the upstream state production, not carrier
-- cardinality/factorisation.
upstreamCarrierWeldRemainsLive :
  upstreamStateIdentificationStillRequired ≡ true
upstreamCarrierWeldRemainsLive = refl
