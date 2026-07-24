module DASHI.Physics.YangMills.BalabanPeriodicPatchGreenTransfer where

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanExactPatchTransferCalculus as Patch
import DASHI.Physics.YangMills.BalabanPeriodicBulkHessianGreenClosure as Bulk

------------------------------------------------------------------------
-- Exact bulk-to-patch transfer for G, nabla G and nabla^2 G.
--
-- The physical extension/restriction maps remain geometry-dependent inputs.
-- Once one retract, its weighted norm bounds and the exact intertwining identity
-- are supplied, the patch operator estimate is derived from the selected bulk
-- certificate.  The same calculus is instantiated coherently for all three
-- propagator families and all four patch regimes.
------------------------------------------------------------------------

record PhysicalPatchOperatorTransfer
    (PatchState Index State Bound Kernel : Set)
    (certificate : Bulk.PeriodicBulkHessianGreenCertificate
      Index State Bound Kernel)
    (index : Index)
    (bulkOperator : State → State)
    (bulkConstant : Bound) : Set₁ where
  field
    extension : PatchState → State
    restriction : State → PatchState
    patchNorm : PatchState → Bound
    CE CR Cpatch : Bound

    restrictionAfterExtension : ∀ h → restriction (extension h) ≡ h

    extensionNormBound : ∀ h →
      Bulk.LessEqual certificate
        (Bulk.weightedNorm certificate (extension h))
        (Bulk.multiplyBound certificate CE (patchNorm h))

    restrictionNormBound : ∀ h →
      Bulk.LessEqual certificate
        (patchNorm (restriction h))
        (Bulk.multiplyBound certificate CR
          (Bulk.weightedNorm certificate h))

    patchOperator : PatchState → PatchState
    operatorTransferIdentity : ∀ f →
      patchOperator f ≡ restriction (bulkOperator (extension f))

    lessEqualTransitive : ∀ {a b c} →
      Bulk.LessEqual certificate a b →
      Bulk.LessEqual certificate b c →
      Bulk.LessEqual certificate a c

    equalityLeft : ∀ {a b c} → a ≡ b →
      Bulk.LessEqual certificate b c →
      Bulk.LessEqual certificate a c

    multiplyMonotoneLeft : ∀ c {a b} →
      Bulk.LessEqual certificate a b →
      Bulk.LessEqual certificate
        (Bulk.multiplyBound certificate c a)
        (Bulk.multiplyBound certificate c b)

    bulkOperatorBound : ∀ f →
      Bulk.LessEqual certificate
        (Bulk.weightedNorm certificate (bulkOperator f))
        (Bulk.multiplyBound certificate bulkConstant
          (Bulk.weightedNorm certificate f))

    constantTransport : ∀ f →
      Bulk.LessEqual certificate
        (Bulk.multiplyBound certificate CR
          (Bulk.multiplyBound certificate bulkConstant
            (Bulk.multiplyBound certificate CE (patchNorm f))))
        (Bulk.multiplyBound certificate Cpatch (patchNorm f))

open PhysicalPatchOperatorTransfer public

asPatchRetract :
  ∀ {PatchState Index State Bound Kernel}
    {certificate : Bulk.PeriodicBulkHessianGreenCertificate
      Index State Bound Kernel}
    {index : Index} {bulkOperator : State → State} {bulkConstant : Bound} →
    PhysicalPatchOperatorTransfer PatchState Index State Bound Kernel
      certificate index bulkOperator bulkConstant →
    Patch.PatchRetract PatchState State Bound
asPatchRetract {certificate = certificate} dataSet = record
  { Patch.extension = extension dataSet
  ; Patch.restriction = restriction dataSet
  ; Patch.patchNorm = patchNorm dataSet
  ; Patch.bulkNorm = Bulk.weightedNorm certificate
  ; Patch.LessEqual = Bulk.LessEqual certificate
  ; Patch.multiply = Bulk.multiplyBound certificate
  ; Patch.CE = CE dataSet
  ; Patch.CR = CR dataSet
  ; Patch.restrictionAfterExtension = restrictionAfterExtension dataSet
  ; Patch.extensionNormBound = extensionNormBound dataSet
  ; Patch.restrictionNormBound = restrictionNormBound dataSet
  }

asExactOperatorTransfer :
  ∀ {PatchState Index State Bound Kernel}
    {certificate : Bulk.PeriodicBulkHessianGreenCertificate
      Index State Bound Kernel}
    {index : Index} {bulkOperator : State → State} {bulkConstant : Bound} →
    (dataSet : PhysicalPatchOperatorTransfer PatchState Index State Bound Kernel
      certificate index bulkOperator bulkConstant) →
    Patch.ExactGreenPatchTransfer PatchState State Bound
asExactOperatorTransfer {bulkOperator = bulkOperator} dataSet = record
  { Patch.retract = asPatchRetract dataSet
  ; Patch.bulkGreen = bulkOperator
  ; Patch.patchGreen = patchOperator dataSet
  ; Patch.greenTransferIdentity = operatorTransferIdentity dataSet
  }

asPatchBoundTransport :
  ∀ {PatchState Index State Bound Kernel}
    {certificate : Bulk.PeriodicBulkHessianGreenCertificate
      Index State Bound Kernel}
    {index : Index} {bulkOperator : State → State} {bulkConstant : Bound} →
    (dataSet : PhysicalPatchOperatorTransfer PatchState Index State Bound Kernel
      certificate index bulkOperator bulkConstant) →
    Patch.GreenPatchBoundTransport PatchState State Bound
asPatchBoundTransport {bulkConstant = bulkConstant} dataSet = record
  { Patch.transfer = asExactOperatorTransfer dataSet
  ; Patch.transitive = lessEqualTransitive dataSet
  ; Patch.equalityLeft = equalityLeft dataSet
  ; Patch.multiplyMonotoneLeft = multiplyMonotoneLeft dataSet
  ; Patch.Cbulk = bulkConstant
  ; Patch.Cpatch = Cpatch dataSet
  ; Patch.bulkGreenBound = bulkOperatorBound dataSet
  ; Patch.constantTransport = constantTransport dataSet
  }

physicalPatchOperatorBound :
  ∀ {PatchState Index State Bound Kernel}
    {certificate : Bulk.PeriodicBulkHessianGreenCertificate
      Index State Bound Kernel}
    {index : Index} {bulkOperator : State → State} {bulkConstant : Bound} →
    (dataSet : PhysicalPatchOperatorTransfer PatchState Index State Bound Kernel
      certificate index bulkOperator bulkConstant) →
    ∀ f →
    Bulk.LessEqual certificate
      (patchNorm dataSet (patchOperator dataSet f))
      (Bulk.multiplyBound certificate (Cpatch dataSet) (patchNorm dataSet f))
physicalPatchOperatorBound dataSet =
  Patch.patchGreenBound (asPatchBoundTransport dataSet)

record PhysicalPatchTripleTransfer
    (PatchState Index State Bound Kernel : Set)
    (certificate : Bulk.PeriodicBulkHessianGreenCertificate
      Index State Bound Kernel)
    (index : Index) : Set₁ where
  field
    greenTransfer : PhysicalPatchOperatorTransfer
      PatchState Index State Bound Kernel certificate index
      (Bulk.green certificate index) (Bulk.CG certificate)
    gradientGreenTransfer : PhysicalPatchOperatorTransfer
      PatchState Index State Bound Kernel certificate index
      (Bulk.gradientGreen certificate index) (Bulk.CGradG certificate)
    secondGradientGreenTransfer : PhysicalPatchOperatorTransfer
      PatchState Index State Bound Kernel certificate index
      (Bulk.secondGradientGreen certificate index) (Bulk.CSecondGradG certificate)

open PhysicalPatchTripleTransfer public

record PhysicalPatchTripleBounds
    (PatchState Index State Bound Kernel : Set)
    (certificate : Bulk.PeriodicBulkHessianGreenCertificate
      Index State Bound Kernel)
    (index : Index)
    (dataSet : PhysicalPatchTripleTransfer
      PatchState Index State Bound Kernel certificate index) : Set₁ where
  field
    greenBound : ∀ f →
      Bulk.LessEqual certificate
        (patchNorm (greenTransfer dataSet)
          (patchOperator (greenTransfer dataSet) f))
        (Bulk.multiplyBound certificate (Cpatch (greenTransfer dataSet))
          (patchNorm (greenTransfer dataSet) f))
    gradientGreenBound : ∀ f →
      Bulk.LessEqual certificate
        (patchNorm (gradientGreenTransfer dataSet)
          (patchOperator (gradientGreenTransfer dataSet) f))
        (Bulk.multiplyBound certificate (Cpatch (gradientGreenTransfer dataSet))
          (patchNorm (gradientGreenTransfer dataSet) f))
    secondGradientGreenBound : ∀ f →
      Bulk.LessEqual certificate
        (patchNorm (secondGradientGreenTransfer dataSet)
          (patchOperator (secondGradientGreenTransfer dataSet) f))
        (Bulk.multiplyBound certificate (Cpatch (secondGradientGreenTransfer dataSet))
          (patchNorm (secondGradientGreenTransfer dataSet) f))

open PhysicalPatchTripleBounds public

assemblePhysicalPatchTripleBounds :
  ∀ {PatchState Index State Bound Kernel}
    {certificate : Bulk.PeriodicBulkHessianGreenCertificate
      Index State Bound Kernel}
    {index : Index}
    (dataSet : PhysicalPatchTripleTransfer
      PatchState Index State Bound Kernel certificate index) →
    PhysicalPatchTripleBounds
      PatchState Index State Bound Kernel certificate index dataSet
assemblePhysicalPatchTripleBounds dataSet = record
  { greenBound = physicalPatchOperatorBound (greenTransfer dataSet)
  ; gradientGreenBound =
      physicalPatchOperatorBound (gradientGreenTransfer dataSet)
  ; secondGradientGreenBound =
      physicalPatchOperatorBound (secondGradientGreenTransfer dataSet)
  }

record FourPhysicalPatchTransferFamily
    (BoundaryPatch InterfacePatch CornerPatch NestedPatch
      Index State Bound Kernel : Set)
    (certificate : Bulk.PeriodicBulkHessianGreenCertificate
      Index State Bound Kernel)
    (index : Index) : Set₁ where
  field
    boundary : PhysicalPatchTripleTransfer
      BoundaryPatch Index State Bound Kernel certificate index
    interface : PhysicalPatchTripleTransfer
      InterfacePatch Index State Bound Kernel certificate index
    corner : PhysicalPatchTripleTransfer
      CornerPatch Index State Bound Kernel certificate index
    nested : PhysicalPatchTripleTransfer
      NestedPatch Index State Bound Kernel certificate index

open FourPhysicalPatchTransferFamily public

periodicPatchTransferAssemblyLevel : ProofLevel
periodicPatchTransferAssemblyLevel = machineChecked

periodicConcretePatchGeometryInputLevel : ProofLevel
periodicConcretePatchGeometryInputLevel = conditional
