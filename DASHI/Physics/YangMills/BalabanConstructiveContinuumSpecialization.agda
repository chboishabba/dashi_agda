module DASHI.Physics.YangMills.BalabanConstructiveContinuumSpecialization where

-- Specialization of the generic constructive Yang--Mills frontier to the
-- concrete Balaban/SU(N) stack assembled on this branch.
--
-- Finite algebraic assembly and induction are reused directly.  The remaining
-- analytic obligations are kept as fields: no continuum OS or mass-gap input is
-- manufactured by this module.

open import Agda.Primitive using (Setω)

open import DASHI.Physics.YangMills.BalabanOneStepRGClosure as RG1
open import DASHI.Physics.YangMills.BalabanStepVKPClosure as StepV
open import DASHI.Physics.YangMills.BalabanAllScaleRGClosure as RG∞
open import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
open import DASHI.Physics.YangMills.FiniteReflectionPositivity as FRP
open import DASHI.Physics.YangMills.CompactLieYangMillsFrontier as Frontier
open import DASHI.Physics.YangMills.CompactLieProofLevel

record BalabanConstructiveInputs
    (Field EffectiveAction Polymer Bound Site State ErrorBound
     Observable Index Scalar Point Hamiltonian : Set)
    (positiveScalar : FRP.PositiveAdditiveScalar Scalar) : Setω where
  field
    oneStepInputs : RG1.OneStepRGInputs Field EffectiveAction Polymer Bound
    stepVInputs : StepV.StepVSpatialInputs Site Polymer Bound
    invariantDomain : RG∞.RGInvariantDomain State
    summableErrors : RG∞.SummableRGErrors ErrorBound

    reflectionFactorization :
      FRP.ReflectionSquareFactorization Observable Index Scalar positiveScalar

    continuumSchwingerSystem :
      OSGap.ContinuumSchwingerSystem Observable Point Scalar

    osReconstruction :
      OSGap.OSReconstructionAuthority
        Observable Point Scalar continuumSchwingerSystem

    uniformClustering :
      OSGap.UniformClusteringData Observable Point Bound

    clusteringToGap :
      OSGap.ClusteringToGapAuthority
        Observable Point Bound Hamiltonian uniformClustering

record BalabanConstructiveCertificates
    (Field EffectiveAction Polymer Bound Site State ErrorBound
     Observable Index Scalar Point Hamiltonian : Set)
    (positiveScalar : FRP.PositiveAdditiveScalar Scalar) : Setω where
  field
    inputs :
      BalabanConstructiveInputs
        Field EffectiveAction Polymer Bound Site State ErrorBound
        Observable Index Scalar Point Hamiltonian positiveScalar

  oneStep : RG1.OneStepRGCertificate Field EffectiveAction Polymer Bound
  oneStep = RG1.assembleOneStepRG
    (BalabanConstructiveInputs.oneStepInputs inputs)

  stepV : StepV.StepVSpatialCertificate Site Polymer Bound
  stepV = StepV.assembleStepVSpatial
    (BalabanConstructiveInputs.stepVInputs inputs)

  allScale : RG∞.AllScaleRGCertificate State ErrorBound
  allScale = RG∞.assembleAllScaleRG
    (BalabanConstructiveInputs.invariantDomain inputs)
    (BalabanConstructiveInputs.summableErrors inputs)

  finiteOS2 : FRP.FiniteReflectionPositive Observable Scalar positiveScalar
  finiteOS2 = FRP.factorizationToReflectionPositive
    (BalabanConstructiveInputs.reflectionFactorization inputs)

  physicalGap : OSGap.PhysicalMassGapCertificate Hamiltonian Bound
  physicalGap = OSGap.clusteringToPhysicalMassGap
    (BalabanConstructiveInputs.uniformClustering inputs)
    (BalabanConstructiveInputs.clusteringToGap inputs)

-- Exact specialization of the generic frontier target.  The fields below are
-- the unresolved continuum-strength estimates, not aliases for finite results.
record BalabanContinuumFrontierInputs
    (Index State Bound Polymer Scale EffectiveTheory
     SchwingerFamily Hamiltonian Gap : Set) : Setω where
  field
    uniformResidualContraction :
      Frontier.UniformResidualContractionTarget Index State Bound
    fourDimensionalStepV :
      Frontier.LargeFieldStepVTarget Polymer Bound
    allScaleRG :
      Frontier.AllScaleRGTarget Scale EffectiveTheory
    continuumOS :
      Frontier.ContinuumOSTarget SchwingerFamily
    positivePhysicalGap :
      Frontier.PhysicalMassGapTarget Hamiltonian Gap

record BalabanSpecializedFrontier
    (Index State Bound Polymer Scale EffectiveTheory
     SchwingerFamily Hamiltonian Gap : Set) : Setω where
  field
    inputs :
      BalabanContinuumFrontierInputs
        Index State Bound Polymer Scale EffectiveTheory
        SchwingerFamily Hamiltonian Gap

  fullFrontier :
    Frontier.FullCompactLieYangMillsClosure
      Set State Set Index Bound Polymer Scale EffectiveTheory
      SchwingerFamily Hamiltonian Gap
      (λ x → x) (λ _ → Set)
  fullFrontier =
    record
      { background = record
          { backgroundField = λ _ → _
          ; gaugeTransform = λ _ x → x
          ; criticalMap = λ x → x
          ; CriticalMinimizer = λ _ → Set
          ; backgroundSolvesCriticalPoint = λ _ → Set
          ; criticalPointUniqueOnSlice = λ _ _ → Set
          ; backgroundMinimizes = λ _ → Set
          ; minimizerUniqueUpToGauge = λ _ _ → Set
          }
      ; residualContraction =
          BalabanContinuumFrontierInputs.uniformResidualContraction inputs
      ; largeFieldStepV =
          BalabanContinuumFrontierInputs.fourDimensionalStepV inputs
      ; allScaleRG =
          BalabanContinuumFrontierInputs.allScaleRG inputs
      ; continuumOS =
          BalabanContinuumFrontierInputs.continuumOS inputs
      ; physicalMassGap =
          BalabanContinuumFrontierInputs.positivePhysicalGap inputs
      }

finiteAssemblyLevel : ProofLevel
finiteAssemblyLevel = machineChecked

continuumSpecializationInputsLevel : ProofLevel
continuumSpecializationInputsLevel = conjectural
