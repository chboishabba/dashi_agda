module DASHI.Physics.YangMills.BalabanUniformToMassGapChain where

------------------------------------------------------------------------
-- End-to-end constructive Yang--Mills dependency chain.
--
-- Every derived certificate below is a checked consequence of the named input
-- package. The package deliberately retains the unresolved analytic data; it
-- is not a constructor for those data and cannot promote the Clay target.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.CompactLieYangMillsFrontier as Frontier
import DASHI.Physics.YangMills.BalabanUniformGreenNonlinearProduct as Uniform
import DASHI.Physics.YangMills.BalabanOneStepPolymerEstimate as PolymerEstimate
import DASHI.Physics.YangMills.BalabanConcreteOneStepRG as OneStep
import DASHI.Physics.YangMills.BalabanOneStepRGClosure as RG1
import DASHI.Physics.YangMills.BalabanConcreteStepVSuppression as StepVConcrete
import DASHI.Physics.YangMills.BalabanStepVKPClosure as StepV
import DASHI.Physics.YangMills.BalabanQuantitativeAllScaleInvariant as AllScaleConcrete
import DASHI.Physics.YangMills.BalabanAllScaleRGClosure as AllScale
import DASHI.Physics.YangMills.BalabanContinuumOSLimit as OSLimit
import DASHI.Physics.YangMills.BalabanInfiniteVolumeContinuumLimits as ContinuumConcrete
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.BalabanMassGapSurvival as GapSurvival

record UniformToMassGapInputs
    (Volume Scale Background Patch State Bound
     Field EffectiveAction Polymer Site ErrorBound
     Cutoff Observable Point Scalar Hamiltonian : Set) : Setω where
  field
    contractionData :
      Uniform.UniformGreenNonlinearProduct
        Volume Scale Background Patch State Bound

    oneStepStructure : OneStep.OneStepRGStructure Field EffectiveAction
    polymerEstimate :
      PolymerEstimate.OneStepPolymerEstimateData Field Polymer Bound

    stepVSuppression :
      StepVConcrete.ConcreteStepVSuppressionData Site Polymer Bound

    allScaleInputs :
      AllScaleConcrete.QuantitativeAllScaleInputs State ErrorBound

    osLimitProblem :
      OSLimit.SchwingerLimitProblem Cutoff Observable Point Scalar
    osLimitClosure : OSLimit.OSAxiomsClosedUnderLimit osLimitProblem

    uniformCutoffGap :
      GapSurvival.UniformCutoffGapData Cutoff Hamiltonian Bound
    gapSurvival :
      GapSurvival.GapSurvivesContinuumAuthority uniformCutoffGap

open UniformToMassGapInputs public

record UniformToMassGapCertificates
    (Volume Scale Background Patch State Bound
     Field EffectiveAction Polymer Site ErrorBound
     Cutoff Observable Point Scalar Hamiltonian : Set) : Setω where
  field
    inputs :
      UniformToMassGapInputs
        Volume Scale Background Patch State Bound
        Field EffectiveAction Polymer Site ErrorBound
        Cutoff Observable Point Scalar Hamiltonian

  residualContraction :
    Frontier.UniformResidualContractionTarget
      (Uniform.BalabanPatchIndex Volume Scale Background Patch) State Bound
  residualContraction =
    Uniform.toUniformResidualContractionTarget (contractionData inputs)

  oneStepRG : RG1.OneStepRGCertificate Field EffectiveAction Polymer Bound
  oneStepRG =
    OneStep.concreteOneStepRGCertificate
      (oneStepStructure inputs) (polymerEstimate inputs)

  stepV : StepV.StepVSpatialCertificate Site Polymer Bound
  stepV = StepVConcrete.concreteStepVCertificate (stepVSuppression inputs)

  largeFieldTarget : Frontier.LargeFieldStepVTarget Polymer Bound
  largeFieldTarget =
    StepVConcrete.toLargeFieldStepVTarget (stepVSuppression inputs)

  allScales : AllScale.AllScaleRGCertificate State ErrorBound
  allScales =
    AllScaleConcrete.quantitativeAllScaleCertificate (allScaleInputs inputs)

  continuumOS : OSGap.ContinuumSchwingerSystem Observable Point Scalar
  continuumOS =
    OSLimit.continuumOSFromLimit (osLimitProblem inputs) (osLimitClosure inputs)

  continuumOSTarget :
    Frontier.ContinuumOSTarget (Observable → Point → Point → Scalar)
  continuumOSTarget =
    OSLimit.toContinuumOSTarget (osLimitProblem inputs) (osLimitClosure inputs)

  physicalMassGap : OSGap.PhysicalMassGapCertificate Hamiltonian Bound
  physicalMassGap =
    GapSurvival.survivingPhysicalMassGap
      (uniformCutoffGap inputs) (gapSurvival inputs)

  physicalMassGapTarget : Frontier.PhysicalMassGapTarget Hamiltonian Bound
  physicalMassGapTarget =
    GapSurvival.toPhysicalMassGapTarget
      (uniformCutoffGap inputs) (gapSurvival inputs)

open UniformToMassGapCertificates public

assembleUniformToMassGap :
  ∀ {Volume Scale Background Patch State Bound
     Field EffectiveAction Polymer Site ErrorBound
     Cutoff Observable Point Scalar Hamiltonian : Set} →
  UniformToMassGapInputs
    Volume Scale Background Patch State Bound
    Field EffectiveAction Polymer Site ErrorBound
    Cutoff Observable Point Scalar Hamiltonian →
  UniformToMassGapCertificates
    Volume Scale Background Patch State Bound
    Field EffectiveAction Polymer Site ErrorBound
    Cutoff Observable Point Scalar Hamiltonian
assembleUniformToMassGap inputs = record { inputs = inputs }

uniformToMassGapAssemblyLevel : ProofLevel
uniformToMassGapAssemblyLevel = machineChecked

uniformToMassGapAnalyticInputsLevel : ProofLevel
uniformToMassGapAnalyticInputsLevel = conjectural
