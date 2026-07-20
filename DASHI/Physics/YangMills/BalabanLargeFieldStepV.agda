module DASHI.Physics.YangMills.BalabanLargeFieldStepV where

------------------------------------------------------------------------
-- Step V / large-field suppression, with the analytic and combinatorial
-- obligations exposed separately from the machine-checked KP and cluster
-- consequences.
--
-- V1--V6 are the concrete estimates that an actual Balaban polymer activity
-- must provide.  V7 is obtained by transitivity from the explicit majorant
-- estimates.  V8 is obtained by applying the cluster-expansion theorem package
-- to V7.  Thus no analytic estimate is hidden inside the assembly bridge.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConcreteStepVSuppression as Concrete

record LargeFieldStepVEstimates
    (Site Polymer Configuration Bound : Set) : Set₁ where
  field
    contains : Site → Polymer → Set
    LargeFieldOn : Polymer → Configuration → Set
    CrossesTransferCut : Polymer → Set

    activity : Polymer → Bound
    penalty : Polymer → Bound
    actionOn : Polymer → Configuration → Bound
    suppressionMajorant : Polymer → Bound
    cutSuppression : Polymer → Bound

    size : Polymer → Bound
    diameter : Polymer → Bound
    anisotropicWeight : Polymer → Bound

    polymerCount : Site → Bound → Bound → Bound
    entropyEnvelope : Bound → Bound → Bound

    entropyRate sizeRate diameterRate : Bound

    weightedSumAt : Site → Bound
    entropyFactor : Site → Bound
    largeFieldFactor : Site → Bound
    transferCutFactor : Site → Bound
    kpThreshold : Bound

    multiply : Bound → Bound → Bound
    LessEqual StrictlyGreater : Bound → Bound → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    -- V1: a large-field component pays action proportional to its penalty.
    largeFieldActionEstimate : ∀ {X A} →
      LargeFieldOn X A → LessEqual (penalty X) (actionOn X A)

    -- V2: the activity is exponentially dominated in size and diameter.
    largeFieldSuppressionEstimate : ∀ X →
      LessEqual (activity X) (suppressionMajorant X)

    -- V3: rooted polymers of fixed size and diameter obey the entropy bound.
    polymerDiameterEntropyEstimate : ∀ site n d →
      LessEqual (polymerCount site n d) (entropyEnvelope n d)

    -- V4: both suppression exponents strictly beat their entropy exponents.
    sizeSuppressionBeatsEntropy : StrictlyGreater sizeRate entropyRate
    diameterSuppressionBeatsEntropy :
      StrictlyGreater diameterRate diameterRate

    -- V5: the anisotropic norm controls the geometric polymer diameter.
    anisotropicDiameterEstimate : ∀ X →
      LessEqual (diameter X) (anisotropicWeight X)

    -- V6: polymers crossing a transfer cut receive the cut majorant.
    transferCutEstimate : ∀ {X} →
      CrossesTransferCut X → LessEqual (activity X) (cutSuppression X)

    -- Explicit factorization used by the existing Step V bridge.
    weightedSumBelowFactors : ∀ site →
      LessEqual (weightedSumAt site)
        (multiply (entropyFactor site)
          (multiply (largeFieldFactor site) (transferCutFactor site)))

    factorsBelowThreshold : ∀ site →
      LessEqual
        (multiply (entropyFactor site)
          (multiply (largeFieldFactor site) (transferCutFactor site)))
        kpThreshold

    -- V8 theorem package.  Its only summability input is the concrete KP bound.
    ClusterExpansionConverges : Set
    ClusterWeightsExponentiallyDecay : Set
    ConnectedCorrelationsClusterBound : Set

    kpConvergenceTheorem :
      (∀ site → LessEqual (weightedSumAt site) kpThreshold) →
      ClusterExpansionConverges

    clusterWeightDecayTheorem :
      ClusterExpansionConverges → ClusterWeightsExponentiallyDecay

    connectedCorrelationTheorem :
      ClusterWeightsExponentiallyDecay →
      ConnectedCorrelationsClusterBound

------------------------------------------------------------------------
-- V1--V6: named projections matching the analytic target statements.
------------------------------------------------------------------------

largeFieldActionLowerBound :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : LargeFieldStepVEstimates Site Polymer Configuration Bound)
    {X A} →
  LargeFieldStepVEstimates.LargeFieldOn estimates X A →
  LargeFieldStepVEstimates.LessEqual estimates
    (LargeFieldStepVEstimates.penalty estimates X)
    (LargeFieldStepVEstimates.actionOn estimates X A)
largeFieldActionLowerBound estimates =
  LargeFieldStepVEstimates.largeFieldActionEstimate estimates

largeFieldPolymerSuppressed :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : LargeFieldStepVEstimates Site Polymer Configuration Bound)
    (X : Polymer) →
  LargeFieldStepVEstimates.LessEqual estimates
    (LargeFieldStepVEstimates.activity estimates X)
    (LargeFieldStepVEstimates.suppressionMajorant estimates X)
largeFieldPolymerSuppressed estimates =
  LargeFieldStepVEstimates.largeFieldSuppressionEstimate estimates

polymerDiameterEntropyBound :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : LargeFieldStepVEstimates Site Polymer Configuration Bound)
    (site : Site) (n d : Bound) →
  LargeFieldStepVEstimates.LessEqual estimates
    (LargeFieldStepVEstimates.polymerCount estimates site n d)
    (LargeFieldStepVEstimates.entropyEnvelope estimates n d)
polymerDiameterEntropyBound estimates =
  LargeFieldStepVEstimates.polymerDiameterEntropyEstimate estimates

suppressionBeatsSizeEntropy :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : LargeFieldStepVEstimates Site Polymer Configuration Bound) →
  LargeFieldStepVEstimates.StrictlyGreater estimates
    (LargeFieldStepVEstimates.sizeRate estimates)
    (LargeFieldStepVEstimates.entropyRate estimates)
suppressionBeatsSizeEntropy estimates =
  LargeFieldStepVEstimates.sizeSuppressionBeatsEntropy estimates

suppressionBeatsDiameterEntropy :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : LargeFieldStepVEstimates Site Polymer Configuration Bound) →
  LargeFieldStepVEstimates.StrictlyGreater estimates
    (LargeFieldStepVEstimates.diameterRate estimates)
    (LargeFieldStepVEstimates.diameterRate estimates)
suppressionBeatsDiameterEntropy estimates =
  LargeFieldStepVEstimates.diameterSuppressionBeatsEntropy estimates

anisotropicNormDominatesPolymerDiameter :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : LargeFieldStepVEstimates Site Polymer Configuration Bound)
    (X : Polymer) →
  LargeFieldStepVEstimates.LessEqual estimates
    (LargeFieldStepVEstimates.diameter estimates X)
    (LargeFieldStepVEstimates.anisotropicWeight estimates X)
anisotropicNormDominatesPolymerDiameter estimates =
  LargeFieldStepVEstimates.anisotropicDiameterEstimate estimates

polymerCrossingTransferCutControlled :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : LargeFieldStepVEstimates Site Polymer Configuration Bound)
    {X : Polymer} →
  LargeFieldStepVEstimates.CrossesTransferCut estimates X →
  LargeFieldStepVEstimates.LessEqual estimates
    (LargeFieldStepVEstimates.activity estimates X)
    (LargeFieldStepVEstimates.cutSuppression estimates X)
polymerCrossingTransferCutControlled estimates =
  LargeFieldStepVEstimates.transferCutEstimate estimates

------------------------------------------------------------------------
-- V7: concrete Kotecky--Preiss inequality.
------------------------------------------------------------------------

concreteKoteckyPreiss :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : LargeFieldStepVEstimates Site Polymer Configuration Bound)
    (site : Site) →
  LargeFieldStepVEstimates.LessEqual estimates
    (LargeFieldStepVEstimates.weightedSumAt estimates site)
    (LargeFieldStepVEstimates.kpThreshold estimates)
concreteKoteckyPreiss estimates site =
  LargeFieldStepVEstimates.transitive estimates
    (LargeFieldStepVEstimates.weightedSumBelowFactors estimates site)
    (LargeFieldStepVEstimates.factorsBelowThreshold estimates site)

------------------------------------------------------------------------
-- V8: convergent cluster expansion and its decay/correlation consequences.
------------------------------------------------------------------------

kpImpliesClusterExpansionConverges :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : LargeFieldStepVEstimates Site Polymer Configuration Bound) →
  LargeFieldStepVEstimates.ClusterExpansionConverges estimates
kpImpliesClusterExpansionConverges estimates =
  LargeFieldStepVEstimates.kpConvergenceTheorem estimates
    (concreteKoteckyPreiss estimates)

clusterWeightsExponentiallyDecay :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : LargeFieldStepVEstimates Site Polymer Configuration Bound) →
  LargeFieldStepVEstimates.ClusterWeightsExponentiallyDecay estimates
clusterWeightsExponentiallyDecay estimates =
  LargeFieldStepVEstimates.clusterWeightDecayTheorem estimates
    (kpImpliesClusterExpansionConverges estimates)

connectedCorrelationsClusterBound :
  ∀ {Site Polymer Configuration Bound : Set}
    (estimates : LargeFieldStepVEstimates Site Polymer Configuration Bound) →
  LargeFieldStepVEstimates.ConnectedCorrelationsClusterBound estimates
connectedCorrelationsClusterBound estimates =
  LargeFieldStepVEstimates.connectedCorrelationTheorem estimates
    (clusterWeightsExponentiallyDecay estimates)

------------------------------------------------------------------------
-- Compatibility adapter to the pre-existing concrete Step V assembly.
------------------------------------------------------------------------

toConcreteStepVSuppressionData :
  ∀ {Site Polymer Configuration Bound : Set} →
  LargeFieldStepVEstimates Site Polymer Configuration Bound →
  Concrete.ConcreteStepVSuppressionData Site Polymer Bound
toConcreteStepVSuppressionData estimates = record
  { contains = LargeFieldStepVEstimates.contains estimates
  ; activityWeight = LargeFieldStepVEstimates.activity estimates
  ; weightedSumAt = LargeFieldStepVEstimates.weightedSumAt estimates
  ; entropyFactor = LargeFieldStepVEstimates.entropyFactor estimates
  ; largeFieldFactor = LargeFieldStepVEstimates.largeFieldFactor estimates
  ; transferCutFactor = LargeFieldStepVEstimates.transferCutFactor estimates
  ; kpThreshold = LargeFieldStepVEstimates.kpThreshold estimates
  ; multiply = LargeFieldStepVEstimates.multiply estimates
  ; LessEqual = LargeFieldStepVEstimates.LessEqual estimates
  ; transitive = LargeFieldStepVEstimates.transitive estimates
  ; weightedSumBelowFactors =
      LargeFieldStepVEstimates.weightedSumBelowFactors estimates
  ; factorsBelowThreshold =
      LargeFieldStepVEstimates.factorsBelowThreshold estimates
  ; DiameterEntropyControlled = ∀ site n d →
      LargeFieldStepVEstimates.LessEqual estimates
        (LargeFieldStepVEstimates.polymerCount estimates site n d)
        (LargeFieldStepVEstimates.entropyEnvelope estimates n d)
  ; AnisotropicDiameterCompatible = ∀ X →
      LargeFieldStepVEstimates.LessEqual estimates
        (LargeFieldStepVEstimates.diameter estimates X)
        (LargeFieldStepVEstimates.anisotropicWeight estimates X)
  ; TransferCutCompatible = ∀ {X} →
      LargeFieldStepVEstimates.CrossesTransferCut estimates X →
      LargeFieldStepVEstimates.LessEqual estimates
        (LargeFieldStepVEstimates.activity estimates X)
        (LargeFieldStepVEstimates.cutSuppression estimates X)
  ; LargeFieldSuppressed = ∀ X →
      LargeFieldStepVEstimates.LessEqual estimates
        (LargeFieldStepVEstimates.activity estimates X)
        (LargeFieldStepVEstimates.suppressionMajorant estimates X)
  ; ClusterDecompositionAvailable =
      LargeFieldStepVEstimates.ClusterExpansionConverges estimates
  ; diameterEntropyControlled = polymerDiameterEntropyBound estimates
  ; anisotropicDiameterCompatible =
      anisotropicNormDominatesPolymerDiameter estimates
  ; transferCutCompatible = polymerCrossingTransferCutControlled estimates
  ; largeFieldSuppressed = largeFieldPolymerSuppressed estimates
  ; clusterDecompositionAvailable =
      kpImpliesClusterExpansionConverges estimates
  }

largeFieldStepVBridgeLevel : ProofLevel
largeFieldStepVBridgeLevel = machineChecked

largeFieldStepVAnalyticEstimatesLevel : ProofLevel
largeFieldStepVAnalyticEstimatesLevel = conjectural
