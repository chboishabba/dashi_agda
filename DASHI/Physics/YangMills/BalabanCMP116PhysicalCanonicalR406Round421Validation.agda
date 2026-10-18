{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PhysicalCanonicalR406Round421Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116PhysicalCanonicalR406Round421Exact as R421
open import DASHI.Physics.YangMills.CompactLieProofLevel

physicalCanonicalR406CompilerMachineChecked :
  R421.round421PhysicalCanonicalR406CompilerLevel ≡ machineChecked
physicalCanonicalR406CompilerMachineChecked = refl

independentPhysicalCoordinateWeldsPruned :
  R421.round421IndependentPhysicalCoordinateWeldsRequired ≡ false
independentPhysicalCoordinateWeldsPruned = refl

noAdditionalDecayTheorem :
  R421.round421AdditionalDecayTheoremRequired ≡ false
noAdditionalDecayTheorem = refl


outerFiniteSummationCompilerOwned :
  R421.round421OuterSourceSummabilityLevel ≡ machineChecked
outerFiniteSummationCompilerOwned = refl

residualCMP116SummabilityCompilerOwned :
  R421.round421ResidualCMP116SummabilityLevel ≡ machineChecked
residualCMP116SummabilityCompilerOwned = refl

selectedCMP116ResidualCarrierAttachmentRemainsPhysical :
  R421.round421SelectedCMP116ResidualCarrierAttachmentLevel ≡ conditional
selectedCMP116ResidualCarrierAttachmentRemainsPhysical = refl

pointwiseMarkedResidualFactorizationCompilerOwned :
  R421.round421PointwiseMarkedResidualFactorizationLevel ≡ machineChecked
pointwiseMarkedResidualFactorizationCompilerOwned = refl

literalChargeGeometryRemainsPhysical :
  R421.round421LiteralChargeGeometryAttachmentLevel ≡ conditional
literalChargeGeometryRemainsPhysical = refl
