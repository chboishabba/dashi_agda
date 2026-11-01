module DASHI.Physics.YangMills.BalabanConstructiveCompletionSpine where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Fail-closed completion spine.
--
-- This module does not manufacture any analytic result.  It gives one exact
-- dependency chain from the finite-background endpoint through one-step RG,
-- Step V, all-scale control, thermodynamic/continuum limits, OS
-- reconstruction, and a physical spectral gap.  Every transition consumes
-- the output of the preceding stage, preventing unrelated witnesses from
-- being assembled into a nominal completion certificate.
------------------------------------------------------------------------

record ConstructiveCompletionStages : Set₁ where
  field
    FiniteBackground OneStepRG StepV AllScale InfiniteVolume ContinuumOS
      ReconstructedTheory PhysicalMassGap CompactSimpleCoverage : Set

    finiteBackground : FiniteBackground

    finiteBackgroundImpliesOneStep : FiniteBackground → OneStepRG
    oneStepImpliesStepV : OneStepRG → StepV
    stepVImpliesAllScale : StepV → AllScale
    allScaleImpliesInfiniteVolume : AllScale → InfiniteVolume
    infiniteVolumeImpliesContinuumOS : InfiniteVolume → ContinuumOS
    continuumOSImpliesReconstruction : ContinuumOS → ReconstructedTheory
    reconstructionImpliesMassGap : ReconstructedTheory → PhysicalMassGap

    compactSimpleCoverage : CompactSimpleCoverage

open ConstructiveCompletionStages public

record ConstructiveCompletionCertificate
    (stages : ConstructiveCompletionStages) : Set₁ where
  field
    finiteBackgroundCertificate : FiniteBackground stages
    oneStepCertificate : OneStepRG stages
    stepVCertificate : StepV stages
    allScaleCertificate : AllScale stages
    infiniteVolumeCertificate : InfiniteVolume stages
    continuumOSCertificate : ContinuumOS stages
    reconstructedTheoryCertificate : ReconstructedTheory stages
    physicalMassGapCertificate : PhysicalMassGap stages
    compactSimpleCoverageCertificate : CompactSimpleCoverage stages

open ConstructiveCompletionCertificate public

assembleConstructiveCompletion :
  (stages : ConstructiveCompletionStages) →
  ConstructiveCompletionCertificate stages
assembleConstructiveCompletion stages = record
  { finiteBackgroundCertificate = finiteBackground stages
  ; oneStepCertificate =
      finiteBackgroundImpliesOneStep stages (finiteBackground stages)
  ; stepVCertificate =
      oneStepImpliesStepV stages
        (finiteBackgroundImpliesOneStep stages (finiteBackground stages))
  ; allScaleCertificate =
      stepVImpliesAllScale stages
        (oneStepImpliesStepV stages
          (finiteBackgroundImpliesOneStep stages (finiteBackground stages)))
  ; infiniteVolumeCertificate =
      allScaleImpliesInfiniteVolume stages
        (stepVImpliesAllScale stages
          (oneStepImpliesStepV stages
            (finiteBackgroundImpliesOneStep stages (finiteBackground stages))))
  ; continuumOSCertificate =
      infiniteVolumeImpliesContinuumOS stages
        (allScaleImpliesInfiniteVolume stages
          (stepVImpliesAllScale stages
            (oneStepImpliesStepV stages
              (finiteBackgroundImpliesOneStep stages
                (finiteBackground stages)))))
  ; reconstructedTheoryCertificate =
      continuumOSImpliesReconstruction stages
        (infiniteVolumeImpliesContinuumOS stages
          (allScaleImpliesInfiniteVolume stages
            (stepVImpliesAllScale stages
              (oneStepImpliesStepV stages
                (finiteBackgroundImpliesOneStep stages
                  (finiteBackground stages))))))
  ; physicalMassGapCertificate =
      reconstructionImpliesMassGap stages
        (continuumOSImpliesReconstruction stages
          (infiniteVolumeImpliesContinuumOS stages
            (allScaleImpliesInfiniteVolume stages
              (stepVImpliesAllScale stages
                (oneStepImpliesStepV stages
                  (finiteBackgroundImpliesOneStep stages
                    (finiteBackground stages)))))))
  ; compactSimpleCoverageCertificate = compactSimpleCoverage stages
  }

------------------------------------------------------------------------
-- Submission gate: formal assembly is not itself mathematical completion.
------------------------------------------------------------------------

record ConstructiveSubmissionGate
    (stages : ConstructiveCompletionStages) : Set₁ where
  field
    completion : ConstructiveCompletionCertificate stages

    FocusedAgdaTypechecks ProofLevelAuditPasses NoHiddenProofEscape : Set
    focusedAgdaTypechecks : FocusedAgdaTypechecks
    proofLevelAuditPasses : ProofLevelAuditPasses
    noHiddenProofEscape : NoHiddenProofEscape

    ExternalMathematicalReview PublicationReady : Set
    externalMathematicalReview : ExternalMathematicalReview
    publicationReady : PublicationReady

open ConstructiveSubmissionGate public

constructiveCompletionSpineAssemblyLevel : ProofLevel
constructiveCompletionSpineAssemblyLevel = machineChecked

constructiveCompletionStageInputsLevel : ProofLevel
constructiveCompletionStageInputsLevel = conditional

constructiveSubmissionReviewInputsLevel : ProofLevel
constructiveSubmissionReviewInputsLevel = conditional
