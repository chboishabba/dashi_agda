module DASHI.Physics.YangMills.BalabanConcreteStepVSuppression where

------------------------------------------------------------------------
-- Concrete Step V factorization.
--
-- The weighted polymer sum is bounded by an entropy factor times a large-field
-- suppression factor times a transfer-cut factor.  A second estimate compares
-- that explicit product with the Kotecky--Preiss threshold.  The conversion to
-- the repository Step V certificate is checked here.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanStepVKPClosure as StepV

record ConcreteStepVSuppressionData
    (Site Polymer Bound : Set) : Set₁ where
  field
    contains : Site → Polymer → Set
    activityWeight : Polymer → Bound
    weightedSumAt : Site → Bound

    entropyFactor : Site → Bound
    largeFieldFactor : Site → Bound
    transferCutFactor : Site → Bound
    kpThreshold : Bound

    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    weightedSumBelowFactors : ∀ site →
      LessEqual (weightedSumAt site)
        (multiply (entropyFactor site)
          (multiply (largeFieldFactor site) (transferCutFactor site)))

    factorsBelowThreshold : ∀ site →
      LessEqual
        (multiply (entropyFactor site)
          (multiply (largeFieldFactor site) (transferCutFactor site)))
        kpThreshold

    DiameterEntropyControlled : Set
    AnisotropicDiameterCompatible : Set
    TransferCutCompatible : Set
    LargeFieldSuppressed : Set
    ClusterDecompositionAvailable : Set

    diameterEntropyControlled : DiameterEntropyControlled
    anisotropicDiameterCompatible : AnisotropicDiameterCompatible
    transferCutCompatible : TransferCutCompatible
    largeFieldSuppressed : LargeFieldSuppressed
    clusterDecompositionAvailable : ClusterDecompositionAvailable

open ConcreteStepVSuppressionData public

stepVMajorant :
  ∀ {Site Polymer Bound : Set} →
  ConcreteStepVSuppressionData Site Polymer Bound → Site → Bound
stepVMajorant dataSet site =
  multiply dataSet (entropyFactor dataSet site)
    (multiply dataSet
      (largeFieldFactor dataSet site)
      (transferCutFactor dataSet site))

toKoteckyPreissProblem :
  ∀ {Site Polymer Bound : Set} →
  ConcreteStepVSuppressionData Site Polymer Bound →
  StepV.KoteckyPreissProblem Site Polymer Bound
toKoteckyPreissProblem dataSet = record
  { contains = contains dataSet
  ; activityWeight = activityWeight dataSet
  ; weightedSumAt = weightedSumAt dataSet
  ; entropyMajorant = entropyFactor dataSet
  ; suppressionMajorant = λ site →
      multiply dataSet
        (largeFieldFactor dataSet site)
        (transferCutFactor dataSet site)
  ; combinedMajorant = stepVMajorant dataSet
  ; kpThreshold = kpThreshold dataSet
  ; LessEqual = LessEqual dataSet
  ; transitive = transitive dataSet
  ; activitySumBelowCombined = weightedSumBelowFactors dataSet
  ; entropySuppressionCombine = factorsBelowThreshold dataSet
  }

toStepVSpatialInputs :
  ∀ {Site Polymer Bound : Set} →
  ConcreteStepVSuppressionData Site Polymer Bound →
  StepV.StepVSpatialInputs Site Polymer Bound
toStepVSpatialInputs dataSet = record
  { kpProblem = toKoteckyPreissProblem dataSet
  ; DiameterEntropyControlled = DiameterEntropyControlled dataSet
  ; AnisotropicDiameterCompatible = AnisotropicDiameterCompatible dataSet
  ; TransferCutCompatible = TransferCutCompatible dataSet
  ; LargeFieldSuppressed = LargeFieldSuppressed dataSet
  ; ClusterDecompositionAvailable = ClusterDecompositionAvailable dataSet
  ; diameterEntropyControlled = diameterEntropyControlled dataSet
  ; anisotropicDiameterCompatible = anisotropicDiameterCompatible dataSet
  ; transferCutCompatible = transferCutCompatible dataSet
  ; largeFieldSuppressed = largeFieldSuppressed dataSet
  ; clusterDecompositionAvailable = clusterDecompositionAvailable dataSet
  }

concreteStepVCertificate :
  ∀ {Site Polymer Bound : Set} →
  ConcreteStepVSuppressionData Site Polymer Bound →
  StepV.StepVSpatialCertificate Site Polymer Bound
concreteStepVCertificate dataSet =
  StepV.assembleStepVSpatial (toStepVSpatialInputs dataSet)

concreteStepVBridgeLevel : ProofLevel
concreteStepVBridgeLevel = machineChecked

concreteStepVAnalyticInputsLevel : ProofLevel
concreteStepVAnalyticInputsLevel = conjectural
