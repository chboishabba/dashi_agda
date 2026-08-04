module DASHI.Physics.YangMills.BalabanClayHighestAlphaReuseExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- Pietro Menotti and Andrea Pelissetto,
-- "General Proof of Osterwalder-Schrader Positivity for the Wilson Action",
-- Communications in Mathematical Physics 113 (1987), 369--373.
-- DOI: 10.1007/BF01221251.
--
-- O. Penrose and J. L. Lebowitz,
-- "On the Exponential Decay of Correlation Functions",
-- Communications in Mathematical Physics 39 (1974), 165--184.
-- DOI: 10.1007/BF01614239.
--
-- DASHI CONTRIBUTION
--
-- Reuse the repository's substantive Clay-facing theorem chains instead of
-- rebuilding them behind new endpoint records.  Given one physical one-step
-- RG package, the checked Gate-4 induction supplies every finite scale and its
-- uniform partition bound.  Given convergence of complete reflected Gram
-- forms, the checked T5 topology theorem supplies continuum reflection
-- positivity.  Given the existing OS4/spectral interpretation, the checked
-- slow-mode contradiction supplies a positive transfer gap.
--
-- The only compatibility map retained here identifies the concrete Gram-form
-- OS2 proposition with the OS2 proposition used by the finite-to-continuum
-- closure.  No RG, positivity, clustering or spectral conclusion is accepted
-- as an independent field of the output.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4CombinedRGUVIterationExact as UV
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as GramOS
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record HighestAlphaYMInputs
    (State Bound Measure Observable Scalar Schwinger Energy : Set) : Set₂ where
  field
    ultravioletPackage : UV.Gate4UVCompletionPackage State Bound

    gramConvergence :
      Gram.PhysicalMeasureToOSGramData Measure Observable Scalar

    continuumClosure : Limit.FiniteToContinuumOSClosure Measure Schwinger

    clusteringSpectrum :
      Gap.ReconstructedClusteringSpectrum Observable Energy Bound

    os4SpectralInterpretation :
      Gap.OS4SpectralInterpretation
        continuumClosure clusteringSpectrum

    gramOS2MatchesContinuumOS2 :
      GramOS.GramReflectionPositive
        (Gram.physicalMeasureTopologyControlsOSGram gramConvergence)
        (Gram.continuumMeasure
          (Gram.convergenceData gramConvergence)) →
      Limit.ReflectionPositive continuumClosure
        (Limit.schwinger continuumClosure
          (Limit.continuumMeasure continuumClosure))

open HighestAlphaYMInputs public

allScalePhysicalAdmissibility :
  ∀ {State Bound Measure Observable Scalar Schwinger Energy}
    (inputs : HighestAlphaYMInputs
      State Bound Measure Observable Scalar Schwinger Energy)
    scale →
  UV.AdmissibleRGState
    (UV.admissibility (ultravioletPackage inputs))
    (UV.stateAt
      (UV.normData (ultravioletPackage inputs))
      (UV.initial (ultravioletPackage inputs))
      scale)
allScalePhysicalAdmissibility inputs =
  UV.packageAllScaleAdmissible (ultravioletPackage inputs)

allScalePartitionFunctionBound :
  ∀ {State Bound Measure Observable Scalar Schwinger Energy}
    (inputs : HighestAlphaYMInputs
      State Bound Measure Observable Scalar Schwinger Energy)
    scale →
  UV.PartitionFunctionUniformlyBounded
    (UV.consequences (ultravioletPackage inputs))
    (UV.stateAt
      (UV.normData (ultravioletPackage inputs))
      (UV.initial (ultravioletPackage inputs))
      scale)
allScalePartitionFunctionBound inputs =
  UV.packagePartitionFunctionUniformBound (ultravioletPackage inputs)

continuumGramReflectionPositive :
  ∀ {State Bound Measure Observable Scalar Schwinger Energy}
    (inputs : HighestAlphaYMInputs
      State Bound Measure Observable Scalar Schwinger Energy) →
  GramOS.GramReflectionPositive
    (Gram.physicalMeasureTopologyControlsOSGram
      (gramConvergence inputs))
    (Gram.continuumMeasure
      (Gram.convergenceData (gramConvergence inputs)))
continuumGramReflectionPositive inputs =
  Gram.physicalContinuumReflectionPositive (gramConvergence inputs)

continuumOS2FromCompleteGramLimits :
  ∀ {State Bound Measure Observable Scalar Schwinger Energy}
    (inputs : HighestAlphaYMInputs
      State Bound Measure Observable Scalar Schwinger Energy) →
  Limit.ReflectionPositive (continuumClosure inputs)
    (Limit.schwinger (continuumClosure inputs)
      (Limit.continuumMeasure (continuumClosure inputs)))
continuumOS2FromCompleteGramLimits inputs =
  gramOS2MatchesContinuumOS2 inputs
    (continuumGramReflectionPositive inputs)

positivePhysicalTransferGap :
  ∀ {State Bound Measure Observable Scalar Schwinger Energy}
    (inputs : HighestAlphaYMInputs
      State Bound Measure Observable Scalar Schwinger Energy) →
  Gap.PositiveTransferGap (clusteringSpectrum inputs)
positivePhysicalTransferGap inputs =
  Gap.positiveTransferGapFromOS4
    (os4SpectralInterpretation inputs)
    (Limit.continuumClustered (continuumClosure inputs))

record HighestAlphaYMConsequences
    (State Bound Measure Observable Scalar Schwinger Energy : Set) : Set₂ where
  field
    inputs : HighestAlphaYMInputs
      State Bound Measure Observable Scalar Schwinger Energy

  admissibleAtEveryScale : ∀ scale →
    UV.AdmissibleRGState
      (UV.admissibility (ultravioletPackage inputs))
      (UV.stateAt
        (UV.normData (ultravioletPackage inputs))
        (UV.initial (ultravioletPackage inputs))
        scale)
  admissibleAtEveryScale = allScalePhysicalAdmissibility inputs

  partitionBoundAtEveryScale : ∀ scale →
    UV.PartitionFunctionUniformlyBounded
      (UV.consequences (ultravioletPackage inputs))
      (UV.stateAt
        (UV.normData (ultravioletPackage inputs))
        (UV.initial (ultravioletPackage inputs))
        scale)
  partitionBoundAtEveryScale = allScalePartitionFunctionBound inputs

  continuumOS2 :
    Limit.ReflectionPositive (continuumClosure inputs)
      (Limit.schwinger (continuumClosure inputs)
        (Limit.continuumMeasure (continuumClosure inputs)))
  continuumOS2 = continuumOS2FromCompleteGramLimits inputs

  transferGap : Gap.PositiveTransferGap (clusteringSpectrum inputs)
  transferGap = positivePhysicalTransferGap inputs

open HighestAlphaYMConsequences public

assembleHighestAlphaYMConsequences :
  ∀ {State Bound Measure Observable Scalar Schwinger Energy} →
  HighestAlphaYMInputs
    State Bound Measure Observable Scalar Schwinger Energy →
  HighestAlphaYMConsequences
    State Bound Measure Observable Scalar Schwinger Energy
assembleHighestAlphaYMConsequences physicalInputs = record
  { inputs = physicalInputs }

highestAlphaAllScaleReuseLevel : ProofLevel
highestAlphaAllScaleReuseLevel = machineChecked

highestAlphaContinuumOS2ReuseLevel : ProofLevel
highestAlphaContinuumOS2ReuseLevel = machineChecked

highestAlphaTransferGapReuseLevel : ProofLevel
highestAlphaTransferGapReuseLevel = machineChecked
