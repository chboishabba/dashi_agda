module DASHI.Physics.YangMills.BalabanExplicitStepVLargeField where

------------------------------------------------------------------------
-- Explicit Step V / large-field theorem chain.
--
-- This module does not hide the analytic frontier behind five unrelated
-- propositions.  It records the named H1--H10 estimates, proves the two
-- transitive majorant steps, and packages the resulting KP, convergence,
-- decay, and connected-correlation conclusions.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

record StepVLargeFieldData
    (Site Polymer Bound Cluster Observable : Set) : Set₁ where
  field
    activity : Polymer → Bound
    weight : Polymer → Bound
    size diameter anisotropicNorm : Polymer → Bound
    actionPenalty : Polymer → Bound
    weightedSumAt : Site → Bound
    entropyMajorantAt sizeMajorantAt diameterMajorantAt : Site → Bound
    kpThreshold : Bound

    LessEqual : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    LargeFieldActionPenalty : Set
    LargeFieldActivitySuppression : Set
    PolymerDiameterEntropy : Set
    SizeSuppressionDominatesEntropy : Set
    DiameterSuppressionDominatesEntropy : Set
    AnisotropicDiameterDomination : Set
    TransferCutSuppression : Set
    ClusterExpansionConvergence : Set
    ClusterWeightExponentialDecay : Set
    ConnectedCorrelationClusterEstimate : Set

    largeFieldActionLowerBoundInput : LargeFieldActionPenalty
    largeFieldPolymerSuppressedInput : LargeFieldActivitySuppression
    polymerDiameterEntropyBoundInput : PolymerDiameterEntropy
    sizeSuppressionBeatsEntropyInput : SizeSuppressionDominatesEntropy
    diameterSuppressionBeatsEntropyInput : DiameterSuppressionDominatesEntropy
    anisotropicNormDominatesPolymerDiameterInput :
      AnisotropicDiameterDomination
    polymerCrossingTransferCutControlledInput : TransferCutSuppression

    weightedSumBelowEntropy : ∀ site →
      LessEqual (weightedSumAt site) (entropyMajorantAt site)
    entropyBelowSizeMajorant : ∀ site →
      LessEqual (entropyMajorantAt site) (sizeMajorantAt site)
    sizeBelowDiameterMajorant : ∀ site →
      LessEqual (sizeMajorantAt site) (diameterMajorantAt site)
    diameterMajorantBelowKP : ∀ site →
      LessEqual (diameterMajorantAt site) kpThreshold

    kpImpliesClusterExpansionConvergesInput :
      (∀ site → LessEqual (weightedSumAt site) kpThreshold) →
      ClusterExpansionConvergence
    convergenceImpliesClusterWeightsExponentiallyDecay :
      ClusterExpansionConvergence → ClusterWeightExponentialDecay
    decayImpliesConnectedCorrelationsClusterBound :
      ClusterWeightExponentialDecay → ConnectedCorrelationClusterEstimate

open StepVLargeFieldData public

largeFieldActionLowerBound :
  ∀ {Site Polymer Bound Cluster Observable : Set} →
  (dataSet : StepVLargeFieldData Site Polymer Bound Cluster Observable) →
  LargeFieldActionPenalty dataSet
largeFieldActionLowerBound = largeFieldActionLowerBoundInput

largeFieldPolymerSuppressed :
  ∀ {Site Polymer Bound Cluster Observable : Set} →
  (dataSet : StepVLargeFieldData Site Polymer Bound Cluster Observable) →
  LargeFieldActivitySuppression dataSet
largeFieldPolymerSuppressed = largeFieldPolymerSuppressedInput

polymerDiameterEntropyBound :
  ∀ {Site Polymer Bound Cluster Observable : Set} →
  (dataSet : StepVLargeFieldData Site Polymer Bound Cluster Observable) →
  PolymerDiameterEntropy dataSet
polymerDiameterEntropyBound = polymerDiameterEntropyBoundInput

sizeSuppressionBeatsEntropy :
  ∀ {Site Polymer Bound Cluster Observable : Set} →
  (dataSet : StepVLargeFieldData Site Polymer Bound Cluster Observable) →
  SizeSuppressionDominatesEntropy dataSet
sizeSuppressionBeatsEntropy = sizeSuppressionBeatsEntropyInput

diameterSuppressionBeatsEntropy :
  ∀ {Site Polymer Bound Cluster Observable : Set} →
  (dataSet : StepVLargeFieldData Site Polymer Bound Cluster Observable) →
  DiameterSuppressionDominatesEntropy dataSet
diameterSuppressionBeatsEntropy = diameterSuppressionBeatsEntropyInput

anisotropicNormDominatesPolymerDiameter :
  ∀ {Site Polymer Bound Cluster Observable : Set} →
  (dataSet : StepVLargeFieldData Site Polymer Bound Cluster Observable) →
  AnisotropicDiameterDomination dataSet
anisotropicNormDominatesPolymerDiameter =
  anisotropicNormDominatesPolymerDiameterInput

polymerCrossingTransferCutControlled :
  ∀ {Site Polymer Bound Cluster Observable : Set} →
  (dataSet : StepVLargeFieldData Site Polymer Bound Cluster Observable) →
  TransferCutSuppression dataSet
polymerCrossingTransferCutControlled =
  polymerCrossingTransferCutControlledInput

concreteKoteckyPreiss :
  ∀ {Site Polymer Bound Cluster Observable : Set} →
  (dataSet : StepVLargeFieldData Site Polymer Bound Cluster Observable) →
  ∀ site → LessEqual dataSet (weightedSumAt dataSet site) (kpThreshold dataSet)
concreteKoteckyPreiss dataSet site =
  transitive dataSet
    (weightedSumBelowEntropy dataSet site)
    (transitive dataSet
      (entropyBelowSizeMajorant dataSet site)
      (transitive dataSet
        (sizeBelowDiameterMajorant dataSet site)
        (diameterMajorantBelowKP dataSet site)))

kpImpliesClusterExpansionConverges :
  ∀ {Site Polymer Bound Cluster Observable : Set} →
  (dataSet : StepVLargeFieldData Site Polymer Bound Cluster Observable) →
  ClusterExpansionConvergence dataSet
kpImpliesClusterExpansionConverges dataSet =
  kpImpliesClusterExpansionConvergesInput dataSet
    (concreteKoteckyPreiss dataSet)

clusterWeightsExponentiallyDecay :
  ∀ {Site Polymer Bound Cluster Observable : Set} →
  (dataSet : StepVLargeFieldData Site Polymer Bound Cluster Observable) →
  ClusterWeightExponentialDecay dataSet
clusterWeightsExponentiallyDecay dataSet =
  convergenceImpliesClusterWeightsExponentiallyDecay dataSet
    (kpImpliesClusterExpansionConverges dataSet)

connectedCorrelationsClusterBound :
  ∀ {Site Polymer Bound Cluster Observable : Set} →
  (dataSet : StepVLargeFieldData Site Polymer Bound Cluster Observable) →
  ConnectedCorrelationClusterEstimate dataSet
connectedCorrelationsClusterBound dataSet =
  decayImpliesConnectedCorrelationsClusterBound dataSet
    (clusterWeightsExponentiallyDecay dataSet)

record ExplicitStepVCertificate
    (Site Polymer Bound Cluster Observable : Set) : Set₁ where
  field
    dataSet : StepVLargeFieldData Site Polymer Bound Cluster Observable
    actionPenalty : LargeFieldActionPenalty dataSet
    activitySuppression : LargeFieldActivitySuppression dataSet
    diameterEntropy : PolymerDiameterEntropy dataSet
    sizeBeatsEntropy : SizeSuppressionDominatesEntropy dataSet
    diameterBeatsEntropy : DiameterSuppressionDominatesEntropy dataSet
    anisotropicDomination : AnisotropicDiameterDomination dataSet
    transferCutControl : TransferCutSuppression dataSet
    kpAtEverySite : ∀ site →
      LessEqual dataSet (weightedSumAt dataSet site) (kpThreshold dataSet)
    clusterExpansionConverges : ClusterExpansionConvergence dataSet
    clusterWeightsDecay : ClusterWeightExponentialDecay dataSet
    connectedCorrelationsBound : ConnectedCorrelationClusterEstimate dataSet

open ExplicitStepVCertificate public

assembleExplicitStepV :
  ∀ {Site Polymer Bound Cluster Observable : Set} →
  (dataSet : StepVLargeFieldData Site Polymer Bound Cluster Observable) →
  ExplicitStepVCertificate Site Polymer Bound Cluster Observable
assembleExplicitStepV dataSet = record
  { dataSet = dataSet
  ; actionPenalty = largeFieldActionLowerBound dataSet
  ; activitySuppression = largeFieldPolymerSuppressed dataSet
  ; diameterEntropy = polymerDiameterEntropyBound dataSet
  ; sizeBeatsEntropy = sizeSuppressionBeatsEntropy dataSet
  ; diameterBeatsEntropy = diameterSuppressionBeatsEntropy dataSet
  ; anisotropicDomination = anisotropicNormDominatesPolymerDiameter dataSet
  ; transferCutControl = polymerCrossingTransferCutControlled dataSet
  ; kpAtEverySite = concreteKoteckyPreiss dataSet
  ; clusterExpansionConverges = kpImpliesClusterExpansionConverges dataSet
  ; clusterWeightsDecay = clusterWeightsExponentiallyDecay dataSet
  ; connectedCorrelationsBound = connectedCorrelationsClusterBound dataSet
  }

explicitStepVAssemblyLevel : ProofLevel
explicitStepVAssemblyLevel = machineChecked

explicitStepVAnalyticInputsLevel : ProofLevel
explicitStepVAnalyticInputsLevel = conditional
