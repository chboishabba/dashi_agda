module DASHI.Physics.YangMills.BalabanStepVKPClosure where

------------------------------------------------------------------------
-- Step V / large-field closure.  Entropy and suppression are kept separate;
-- once their weighted sum is below the KP threshold, summability follows by
-- transitivity rather than by an opaque Step-V premise.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

record KoteckyPreissProblem
    (Site Polymer Bound : Set) : Set₁ where
  field
    contains : Site → Polymer → Set
    activityWeight : Polymer → Bound
    weightedSumAt : Site → Bound

    entropyMajorant : Site → Bound
    suppressionMajorant : Site → Bound
    combinedMajorant : Site → Bound
    kpThreshold : Bound

    LessEqual : Bound → Bound → Set
    transitive : ∀ {a b c} → LessEqual a b → LessEqual b c → LessEqual a c

    activitySumBelowCombined : ∀ site →
      LessEqual (weightedSumAt site) (combinedMajorant site)
    entropySuppressionCombine : ∀ site →
      LessEqual (combinedMajorant site) kpThreshold

open KoteckyPreissProblem public

kpSummable :
  ∀ {Site Polymer Bound : Set} →
  (problem : KoteckyPreissProblem Site Polymer Bound) →
  ∀ site → LessEqual problem (weightedSumAt problem site) (kpThreshold problem)
kpSummable problem site =
  transitive problem
    (activitySumBelowCombined problem site)
    (entropySuppressionCombine problem site)

record StepVSpatialInputs
    (Site Polymer Bound : Set) : Set₁ where
  field
    kpProblem : KoteckyPreissProblem Site Polymer Bound
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

open StepVSpatialInputs public

record StepVSpatialCertificate
    (Site Polymer Bound : Set) : Set₁ where
  field
    inputs : StepVSpatialInputs Site Polymer Bound
    kpAtEverySite : ∀ site →
      LessEqual (kpProblem inputs)
        (weightedSumAt (kpProblem inputs) site)
        (kpThreshold (kpProblem inputs))

open StepVSpatialCertificate public

assembleStepVSpatial :
  ∀ {Site Polymer Bound : Set} →
  (inputs : StepVSpatialInputs Site Polymer Bound) →
  StepVSpatialCertificate Site Polymer Bound
assembleStepVSpatial inputs = record
  { inputs = inputs
  ; kpAtEverySite = kpSummable (kpProblem inputs)
  }

stepVKPBridgeLevel : ProofLevel
stepVKPBridgeLevel = machineChecked

stepVSpatialInputsLevel : ProofLevel
stepVSpatialInputsLevel = conjectural
