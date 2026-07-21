module DASHI.Physics.YangMills.BalabanExactPatchTransferCalculus where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact patch-transfer calculus.
------------------------------------------------------------------------

record PatchRetract (Patch Bulk Bound : Set) : Set₁ where
  field
    extension : Patch → Bulk
    restriction : Bulk → Patch
    patchNorm : Patch → Bound
    bulkNorm : Bulk → Bound
    LessEqual : Bound → Bound → Set
    multiply : Bound → Bound → Bound
    CE CR : Bound
    restrictionAfterExtension : ∀ h → restriction (extension h) ≡ h
    extensionNormBound : ∀ h →
      LessEqual (bulkNorm (extension h)) (multiply CE (patchNorm h))
    restrictionNormBound : ∀ h →
      LessEqual (patchNorm (restriction h)) (multiply CR (bulkNorm h))
open PatchRetract public

record ConstraintPreservingPatchRetract
    (Patch Bulk Bound : Set) : Set₁ where
  field
    retract : PatchRetract Patch Bulk Bound
    PatchConstraint : Patch → Set
    BulkConstraint : Bulk → Set
    extensionPreservesConstraints : ∀ h →
      PatchConstraint h → BulkConstraint (extension retract h)
open ConstraintPreservingPatchRetract public

boundaryRestrictionAfterExtension interfaceRestrictionAfterExtension
  cornerRestrictionAfterExtension nestedRestrictionAfterExtension :
  ∀ {Patch Bulk Bound} (d : PatchRetract Patch Bulk Bound) h →
  restriction d (extension d h) ≡ h
boundaryRestrictionAfterExtension d = restrictionAfterExtension d
interfaceRestrictionAfterExtension d = restrictionAfterExtension d
cornerRestrictionAfterExtension d = restrictionAfterExtension d
nestedRestrictionAfterExtension d = restrictionAfterExtension d

boundaryExtensionPreservesConstraints interfaceExtensionPreservesConstraints
  cornerExtensionPreservesConstraints nestedExtensionPreservesConstraints :
  ∀ {Patch Bulk Bound}
    (d : ConstraintPreservingPatchRetract Patch Bulk Bound) h →
  PatchConstraint d h → BulkConstraint d (extension (retract d) h)
boundaryExtensionPreservesConstraints d = extensionPreservesConstraints d
interfaceExtensionPreservesConstraints d = extensionPreservesConstraints d
cornerExtensionPreservesConstraints d = extensionPreservesConstraints d
nestedExtensionPreservesConstraints d = extensionPreservesConstraints d

boundaryExtensionNormBound interfaceExtensionNormBound
  cornerExtensionNormBound nestedExtensionNormBound :
  ∀ {Patch Bulk Bound} (d : PatchRetract Patch Bulk Bound) h →
  LessEqual d (bulkNorm d (extension d h))
    (multiply d (CE d) (patchNorm d h))
boundaryExtensionNormBound d = extensionNormBound d
interfaceExtensionNormBound d = extensionNormBound d
cornerExtensionNormBound d = extensionNormBound d
nestedExtensionNormBound d = extensionNormBound d

boundaryRestrictionNormBound interfaceRestrictionNormBound
  cornerRestrictionNormBound nestedRestrictionNormBound :
  ∀ {Patch Bulk Bound} (d : PatchRetract Patch Bulk Bound) h →
  LessEqual d (patchNorm d (restriction d h))
    (multiply d (CR d) (bulkNorm d h))
boundaryRestrictionNormBound d = restrictionNormBound d
interfaceRestrictionNormBound d = restrictionNormBound d
cornerRestrictionNormBound d = restrictionNormBound d
nestedRestrictionNormBound d = restrictionNormBound d

record PatchEnergyTransfer (Patch Bulk Bound : Set) : Set₁ where
  field
    retract : PatchRetract Patch Bulk Bound
    patchEnergy : Patch → Bound
    bulkEnergy : Bulk → Bound
    energyComparedToBulk : ∀ h →
      LessEqual retract (bulkEnergy (extension retract h)) (patchEnergy h)
open PatchEnergyTransfer public

boundaryEnergyComparedToBulk interfaceEnergyComparedToBulk
  cornerEnergyComparedToBulk nestedEnergyComparedToBulk :
  ∀ {Patch Bulk Bound} (d : PatchEnergyTransfer Patch Bulk Bound) h →
  LessEqual (retract d)
    (bulkEnergy d (extension (retract d) h)) (patchEnergy d h)
boundaryEnergyComparedToBulk d = energyComparedToBulk d
interfaceEnergyComparedToBulk d = energyComparedToBulk d
cornerEnergyComparedToBulk d = energyComparedToBulk d
nestedEnergyComparedToBulk d = energyComparedToBulk d

record ExactGreenPatchTransfer (Patch Bulk Bound : Set) : Set₁ where
  field
    retract : PatchRetract Patch Bulk Bound
    bulkGreen : Bulk → Bulk
    patchGreen : Patch → Patch
    greenTransferIdentity : ∀ f →
      patchGreen f ≡ restriction retract (bulkGreen (extension retract f))
open ExactGreenPatchTransfer public

boundaryGreenTransferIdentity interfaceGreenTransferIdentity
  cornerGreenTransferIdentity nestedGreenTransferIdentity :
  ∀ {Patch Bulk Bound} (d : ExactGreenPatchTransfer Patch Bulk Bound) f →
  patchGreen d f ≡
  restriction (retract d) (bulkGreen d (extension (retract d) f))
boundaryGreenTransferIdentity d = greenTransferIdentity d
interfaceGreenTransferIdentity d = greenTransferIdentity d
cornerGreenTransferIdentity d = greenTransferIdentity d
nestedGreenTransferIdentity d = greenTransferIdentity d

record GreenPatchBoundTransport (Patch Bulk Bound : Set) : Set₁ where
  field
    transfer : ExactGreenPatchTransfer Patch Bulk Bound
    transitive : ∀ {a b c} →
      LessEqual (retract transfer) a b →
      LessEqual (retract transfer) b c →
      LessEqual (retract transfer) a c
    equalityLeft : ∀ {a b c} → a ≡ b →
      LessEqual (retract transfer) b c →
      LessEqual (retract transfer) a c
    multiplyMonotoneLeft : ∀ c {a b} →
      LessEqual (retract transfer) a b →
      LessEqual (retract transfer)
        (multiply (retract transfer) c a)
        (multiply (retract transfer) c b)
    Cbulk Cpatch : Bound
    bulkGreenBound : ∀ f →
      LessEqual (retract transfer)
        (bulkNorm (retract transfer) (bulkGreen transfer f))
        (multiply (retract transfer) Cbulk
          (bulkNorm (retract transfer) f))
    constantTransport : ∀ f →
      LessEqual (retract transfer)
        (multiply (retract transfer) (CR (retract transfer))
          (multiply (retract transfer) Cbulk
            (multiply (retract transfer) (CE (retract transfer))
              (patchNorm (retract transfer) f))))
        (multiply (retract transfer) Cpatch
          (patchNorm (retract transfer) f))
open GreenPatchBoundTransport public

patchGreenControlledByBulk :
  ∀ {Patch Bulk Bound} (d : GreenPatchBoundTransport Patch Bulk Bound) f →
  LessEqual (retract (transfer d))
    (patchNorm (retract (transfer d)) (patchGreen (transfer d) f))
    (multiply (retract (transfer d)) (CR (retract (transfer d)))
      (bulkNorm (retract (transfer d))
        (bulkGreen (transfer d) (extension (retract (transfer d)) f))))
patchGreenControlledByBulk d f = equalityLeft d
  (greenTransferIdentity (transfer d) f)
  (restrictionNormBound (retract (transfer d))
    (bulkGreen (transfer d) (extension (retract (transfer d)) f)))

patchGreenBound :
  ∀ {Patch Bulk Bound} (d : GreenPatchBoundTransport Patch Bulk Bound) f →
  LessEqual (retract (transfer d))
    (patchNorm (retract (transfer d)) (patchGreen (transfer d) f))
    (multiply (retract (transfer d)) (Cpatch d)
      (patchNorm (retract (transfer d)) f))
patchGreenBound d f = transitive d
  (patchGreenControlledByBulk d f)
  (transitive d
    (multiplyMonotoneLeft d (CR (retract (transfer d)))
      (bulkGreenBound d (extension (retract (transfer d)) f)))
    (transitive d
      (multiplyMonotoneLeft d (CR (retract (transfer d)))
        (multiplyMonotoneLeft d (Cbulk d)
          (extensionNormBound (retract (transfer d)) f)))
      (constantTransport d f)))

boundaryGreenControlledByBulk interfaceGreenControlledByBulk
  cornerGreenControlledByBulk nestedGreenControlledByBulk :
  ∀ {Patch Bulk Bound} (d : GreenPatchBoundTransport Patch Bulk Bound) f →
  LessEqual (retract (transfer d))
    (patchNorm (retract (transfer d)) (patchGreen (transfer d) f))
    (multiply (retract (transfer d)) (Cpatch d)
      (patchNorm (retract (transfer d)) f))
boundaryGreenControlledByBulk d = patchGreenBound d
interfaceGreenControlledByBulk d = patchGreenBound d
cornerGreenControlledByBulk d = patchGreenBound d
nestedGreenControlledByBulk d = patchGreenBound d

record FourPatchTransferFamily
    (BoundaryPatch InterfacePatch CornerPatch NestedPatch Bulk Bound : Set) : Set₁ where
  field
    boundaryTransfer : GreenPatchBoundTransport BoundaryPatch Bulk Bound
    interfaceTransfer : GreenPatchBoundTransport InterfacePatch Bulk Bound
    cornerTransfer : GreenPatchBoundTransport CornerPatch Bulk Bound
    nestedTransfer : GreenPatchBoundTransport NestedPatch Bulk Bound
open FourPatchTransferFamily public

patchTransferAlgebraAssemblyLevel : ProofLevel
patchTransferAlgebraAssemblyLevel = machineChecked

concretePatchGeometryInputLevel : ProofLevel
concretePatchGeometryInputLevel = conditional
