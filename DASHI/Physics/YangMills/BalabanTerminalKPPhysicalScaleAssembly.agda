module DASHI.Physics.YangMills.BalabanTerminalKPPhysicalScaleAssembly where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanExplicitStepVLargeField as StepV
import DASHI.Physics.YangMills.BalabanTerminalScalePhysicalClustering as Terminal

------------------------------------------------------------------------
-- Exact terminal Step-V/KP to physical-clustering assembly.
--
-- The Step-V certificate already contains the connected-correlation cluster
-- estimate.  This module prevents that estimate from being replaced by a new
-- unrelated premise: one explicit adapter identifies it with the terminal
-- correlation inequality, after which the bounded terminal physical-scale
-- comparison produces the exact data consumed by OS reconstruction.
------------------------------------------------------------------------

record TerminalKPPhysicalScaleData
    (Site Polymer Cluster Observable Time Scalar Bound Hamiltonian : Set)
    : Set₁ where
  field
    stepVCertificate :
      StepV.ExplicitStepVCertificate
        Site Polymer Bound Cluster Observable

    connectedCorrelation : Observable → Observable → Time → Scalar
    absoluteValue : Scalar → Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    lessEqualTransitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    correlationConstant : Observable → Observable → Bound
    terminalDecay : Time → Bound
    physicalDecay : Bound → Time → Bound

    terminalRate terminalSpacingUpper physicalRate : Bound
    Positive : Bound → Set
    terminalRatePositive : Positive terminalRate
    terminalSpacingUpperPositive : Positive terminalSpacingUpper
    physicalRatePositive : Positive physicalRate

    hamiltonian : Hamiltonian

    clusterEstimateToTerminalPolymerClustering :
      StepV.ConnectedCorrelationClusterEstimate
        (StepV.dataSet stepVCertificate) →
      ∀ A B t →
      LessEqual
        (absoluteValue (connectedCorrelation A B t))
        (multiply (correlationConstant A B) (terminalDecay t))

    terminalDecayBelowPhysicalDecay : ∀ A B t →
      LessEqual
        (multiply (correlationConstant A B) (terminalDecay t))
        (multiply (correlationConstant A B)
          (physicalDecay physicalRate t))

open TerminalKPPhysicalScaleData public

terminalPolymerClusteringFromStepV :
  ∀ {Site Polymer Cluster Observable Time Scalar Bound Hamiltonian}
    (dataSet :
      TerminalKPPhysicalScaleData
        Site Polymer Cluster Observable Time Scalar Bound Hamiltonian) →
  ∀ A B t →
  LessEqual dataSet
    (absoluteValue dataSet (connectedCorrelation dataSet A B t))
    (multiply dataSet
      (correlationConstant dataSet A B)
      (terminalDecay dataSet t))
terminalPolymerClusteringFromStepV dataSet =
  clusterEstimateToTerminalPolymerClustering dataSet
    (StepV.connectedCorrelationsBound (StepV.dataSet (stepVCertificate dataSet)))

terminalScalePhysicalClusteringData :
  ∀ {Site Polymer Cluster Observable Time Scalar Bound Hamiltonian} →
  TerminalKPPhysicalScaleData
    Site Polymer Cluster Observable Time Scalar Bound Hamiltonian →
  Terminal.TerminalScalePhysicalClusteringData
    Observable Time Scalar Bound Hamiltonian
terminalScalePhysicalClusteringData dataSet = record
  { connectedCorrelation = connectedCorrelation dataSet
  ; absoluteValue = absoluteValue dataSet
  ; multiply = multiply dataSet
  ; LessEqual = LessEqual dataSet
  ; lessEqualTransitive = lessEqualTransitive dataSet
  ; correlationConstant = correlationConstant dataSet
  ; terminalDecay = terminalDecay dataSet
  ; physicalDecay = physicalDecay dataSet
  ; terminalRate = terminalRate dataSet
  ; terminalSpacingUpper = terminalSpacingUpper dataSet
  ; physicalRate = physicalRate dataSet
  ; Positive = Positive dataSet
  ; terminalRatePositive = terminalRatePositive dataSet
  ; terminalSpacingUpperPositive = terminalSpacingUpperPositive dataSet
  ; physicalRatePositive = physicalRatePositive dataSet
  ; hamiltonian = hamiltonian dataSet
  ; terminalPolymerClustering = terminalPolymerClusteringFromStepV dataSet
  ; terminalDecayBelowPhysicalDecay = terminalDecayBelowPhysicalDecay dataSet
  }

terminalKPProducesUniformPhysicalClustering :
  ∀ {Site Polymer Cluster Observable Time Scalar Bound Hamiltonian}
    (dataSet :
      TerminalKPPhysicalScaleData
        Site Polymer Cluster Observable Time Scalar Bound Hamiltonian) →
  ∀ A B t →
  Terminal.LessEqual (terminalScalePhysicalClusteringData dataSet)
    (Terminal.absoluteValue (terminalScalePhysicalClusteringData dataSet)
      (Terminal.connectedCorrelation
        (terminalScalePhysicalClusteringData dataSet) A B t))
    (Terminal.multiply (terminalScalePhysicalClusteringData dataSet)
      (Terminal.correlationConstant
        (terminalScalePhysicalClusteringData dataSet) A B)
      (Terminal.physicalDecay
        (terminalScalePhysicalClusteringData dataSet)
        (Terminal.physicalRate (terminalScalePhysicalClusteringData dataSet))
        t))
terminalKPProducesUniformPhysicalClustering dataSet =
  Terminal.terminalScalePolymerGapProducesUniformPhysicalClustering
    (terminalScalePhysicalClusteringData dataSet)

terminalKPPhysicalScaleAssemblyLevel : ProofLevel
terminalKPPhysicalScaleAssemblyLevel = machineChecked

stepVClusterEstimateCarrierMatchingLevel : ProofLevel
stepVClusterEstimateCarrierMatchingLevel = conditional

boundedTerminalPhysicalScaleInputLevel : ProofLevel
boundedTerminalPhysicalScaleInputLevel = conditional
