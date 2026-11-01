module DASHI.Physics.YangMills.BalabanPeriodicConstructiveCompletionSpine where

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicBulkHessianGreenClosure as Bulk
import DASHI.Physics.YangMills.BalabanPeriodicPatchGreenTransfer as Patch
import DASHI.Physics.YangMills.BalabanPatchResidualSmallness as Residual
import DASHI.Physics.YangMills.BalabanOneStepAllScaleAnalyticInhabitation as RG
import DASHI.Physics.YangMills.BalabanThermodynamicContinuumOSAnalyticInhabitation as Continuum
import DASHI.Physics.YangMills.BalabanUniformPhysicalMassGapAnalyticInhabitation as Gap

------------------------------------------------------------------------
-- One fail-closed physical completion owner above the periodic bulk certificate.
--
-- The detailed theorem-facing owners for the critical map, one-step RG, Step V,
-- all-scale control, thermodynamic/continuum OS construction and physical gap
-- already exist.  This record prevents the newly concrete periodic bulk/patch
-- lane from terminating in a disconnected certificate: one inhabitant must carry
-- the selected bulk certificate, all four patch regimes, one strict common
-- residual witness, and the complete downstream analytic owners together.
--
-- No downstream analytic field is manufactured here.  This is dependency and
-- witness coherence only; the proof-level ledger below remains fail-closed.
------------------------------------------------------------------------

record PeriodicConstructiveCompletionSpine
    (BoundaryPatch InterfacePatch CornerPatch NestedPatch
      Index State Bound Kernel : Set) : Set₁ where
  field
    selectedIndex : Index

    bulkCertificate : Bulk.PeriodicBulkHessianGreenCertificate
      Index State Bound Kernel

    patchTransferFamily : Patch.FourPhysicalPatchTransferFamily
      BoundaryPatch InterfacePatch CornerPatch NestedPatch
      Index State Bound Kernel bulkCertificate selectedIndex

    residualData : Residual.PatchResidualSmallnessData Bound
    residualWitness : Residual.PatchResidualWitness residualData

    oneStepAllScaleInputs : RG.OneStepAllScaleAnalyticInputs
    thermodynamicContinuumInputs :
      Continuum.ThermodynamicContinuumOSAnalyticInputs
    physicalMassGapInputs : Gap.UniformPhysicalMassGapAnalyticInputs

open PeriodicConstructiveCompletionSpine public

record PeriodicConstructiveCompletionEndpoints
    (BoundaryPatch InterfacePatch CornerPatch NestedPatch
      Index State Bound Kernel : Set)
    (spine : PeriodicConstructiveCompletionSpine
      BoundaryPatch InterfacePatch CornerPatch NestedPatch
      Index State Bound Kernel) : Set₁ where
  field
    bulk : Bulk.PeriodicBulkHessianGreenCertificate Index State Bound Kernel
    patches : Patch.FourPhysicalPatchTransferFamily
      BoundaryPatch InterfacePatch CornerPatch NestedPatch
      Index State Bound Kernel bulk (selectedIndex spine)
    strictResidual : Residual.PatchResidualWitness (residualData spine)
    oneStepAllScale : RG.OneStepAllScaleAnalyticInputs
    thermodynamicContinuum : Continuum.ThermodynamicContinuumOSAnalyticInputs
    physicalGap : Gap.UniformPhysicalMassGapAnalyticInputs

open PeriodicConstructiveCompletionEndpoints public

projectPeriodicConstructiveCompletionEndpoints :
  ∀ {BoundaryPatch InterfacePatch CornerPatch NestedPatch
      Index State Bound Kernel}
    (spine : PeriodicConstructiveCompletionSpine
      BoundaryPatch InterfacePatch CornerPatch NestedPatch
      Index State Bound Kernel) →
    PeriodicConstructiveCompletionEndpoints
      BoundaryPatch InterfacePatch CornerPatch NestedPatch
      Index State Bound Kernel spine
projectPeriodicConstructiveCompletionEndpoints spine = record
  { bulk = bulkCertificate spine
  ; patches = patchTransferFamily spine
  ; strictResidual = residualWitness spine
  ; oneStepAllScale = oneStepAllScaleInputs spine
  ; thermodynamicContinuum = thermodynamicContinuumInputs spine
  ; physicalGap = physicalMassGapInputs spine
  }

periodicConstructiveCompletionSpineAssemblyLevel : ProofLevel
periodicConstructiveCompletionSpineAssemblyLevel = machineChecked

periodicPatchResidualInputLevel : ProofLevel
periodicPatchResidualInputLevel = conditional

periodicOneStepAllScaleInputLevel : ProofLevel
periodicOneStepAllScaleInputLevel = conditional

periodicThermodynamicContinuumInputLevel : ProofLevel
periodicThermodynamicContinuumInputLevel = conjectural

periodicPhysicalGapInputLevel : ProofLevel
periodicPhysicalGapInputLevel = conjectural
