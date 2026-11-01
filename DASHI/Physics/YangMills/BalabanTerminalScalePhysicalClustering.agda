module DASHI.Physics.YangMills.BalabanTerminalScalePhysicalClustering where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSReconstructionMassGapProduction as OS

------------------------------------------------------------------------
-- Terminal-scale dimensional-transmutation bridge.
--
-- This module does not assume a continuum spectral gap.  It isolates the two
-- estimates that must be supplied by the all-scale RG construction:
--
--   1. terminal polymer clustering with a cutoff-independent decay μ0;
--   2. comparison of terminal lattice distance with physical distance through
--      a uniformly bounded terminal physical spacing.
--
-- Their transitive composition is the uniform physical clustering estimate
-- consumed by the existing OS semigroup/spectral-support theorem.
------------------------------------------------------------------------

record TerminalScalePhysicalClusteringData
    (Observable Time Scalar Bound Hamiltonian : Set) : Set₁ where
  field
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

    -- Produced by the terminal Step-V/KP cluster expansion.
    terminalPolymerClustering : ∀ A B t →
      LessEqual
        (absoluteValue (connectedCorrelation A B t))
        (multiply (correlationConstant A B) (terminalDecay t))

    -- Produced by the bounded terminal physical scale:
    -- physicalRate = terminalRate / terminalSpacingUpper, together with the
    -- terminal-distance lower bound.  The exact representation of exp and
    -- distance is deliberately owned by the selected analytic carrier.
    terminalDecayBelowPhysicalDecay : ∀ A B t →
      LessEqual
        (multiply (correlationConstant A B) (terminalDecay t))
        (multiply (correlationConstant A B)
          (physicalDecay physicalRate t))

open TerminalScalePhysicalClusteringData public

terminalScalePolymerGapProducesUniformPhysicalClustering :
  ∀ {Observable Time Scalar Bound Hamiltonian}
    (dataSet :
      TerminalScalePhysicalClusteringData
        Observable Time Scalar Bound Hamiltonian) →
  ∀ A B t →
  LessEqual dataSet
    (absoluteValue dataSet (connectedCorrelation dataSet A B t))
    (multiply dataSet
      (correlationConstant dataSet A B)
      (physicalDecay dataSet (physicalRate dataSet) t))
terminalScalePolymerGapProducesUniformPhysicalClustering dataSet A B t =
  lessEqualTransitive dataSet
    (terminalPolymerClustering dataSet A B t)
    (terminalDecayBelowPhysicalDecay dataSet A B t)

terminalScaleToOSCorrelationDecayData :
  ∀ {Observable Time Scalar Bound Hamiltonian} →
  TerminalScalePhysicalClusteringData
    Observable Time Scalar Bound Hamiltonian →
  OS.UniformConnectedCorrelationDecayData
    Observable Time Scalar Bound Hamiltonian
terminalScaleToOSCorrelationDecayData dataSet = record
  { connectedCorrelation = connectedCorrelation dataSet
  ; absoluteValue = absoluteValue dataSet
  ; multiply = multiply dataSet
  ; exponentialDecay = physicalDecay dataSet
  ; LessEqual = LessEqual dataSet
  ; correlationConstant = correlationConstant dataSet
  ; mStar = physicalRate dataSet
  ; Positive = Positive dataSet
  ; mStarPositive = physicalRatePositive dataSet
  ; hamiltonian = hamiltonian dataSet
  ; uniformConnectedCorrelationDecayWitness =
      terminalScalePolymerGapProducesUniformPhysicalClustering dataSet
  }

terminalPhysicalClusteringAssemblyLevel : ProofLevel
terminalPhysicalClusteringAssemblyLevel = machineChecked

terminalPolymerClusteringInputLevel : ProofLevel
terminalPolymerClusteringInputLevel = conditional

terminalPhysicalScaleComparisonInputLevel : ProofLevel
terminalPhysicalScaleComparisonInputLevel = conditional

terminalClusteringToOSSpectralTransferLevel : ProofLevel
terminalClusteringToOSSpectralTransferLevel = standardImported
