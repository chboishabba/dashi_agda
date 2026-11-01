module DASHI.Biology.Protein.ProteinConsumerFamilyRefinementKernelValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Biology.Protein.ProteinConsumerProjectionAdequacyExact as Portfolio
import DASHI.Biology.Protein.ProteinConsumerFamilyRefinementKernelExact as Kernel

thermalSelection : Kernel.ProteinCoordinateModel
thermalSelection = Kernel.selectedModel Portfolio.thermalResponseConsumer

thermalSelectionExpected :
  thermalSelection ≡ Kernel.identityPlusResidue
thermalSelectionExpected = refl

conformationSelectionExpected :
  Kernel.selectedModel Portfolio.resolvedConformationConsumer ≡
  Kernel.sequencePlusEnvironment
conformationSelectionExpected = refl

rateSelectionExpected :
  Kernel.selectedModel Portfolio.transitionRateConsumer ≡
  Kernel.topologyPlusRate
rateSelectionExpected = refl

thiolSelectionExpected :
  Kernel.selectedModel Portfolio.thiolModificationConsumer ≡
  Kernel.cysteinePlusAccessibility
thiolSelectionExpected = refl

thermalMinimal :
  MDL.MinimalEligibleDescription
    (Kernel.problemFor Portfolio.thermalResponseConsumer)
    Kernel.identityPlusResidue
thermalMinimal = Kernel.minimalFor Portfolio.thermalResponseConsumer

conformationMinimal :
  MDL.MinimalEligibleDescription
    (Kernel.problemFor Portfolio.resolvedConformationConsumer)
    Kernel.sequencePlusEnvironment
conformationMinimal = Kernel.minimalFor Portfolio.resolvedConformationConsumer

rateMinimal :
  MDL.MinimalEligibleDescription
    (Kernel.problemFor Portfolio.transitionRateConsumer)
    Kernel.topologyPlusRate
rateMinimal = Kernel.minimalFor Portfolio.transitionRateConsumer

thiolMinimal :
  MDL.MinimalEligibleDescription
    (Kernel.problemFor Portfolio.thiolModificationConsumer)
    Kernel.cysteinePlusAccessibility
thiolMinimal = Kernel.minimalFor Portfolio.thiolModificationConsumer

attributionBoundaryRetained : Bool
attributionBoundaryRetained =
  Kernel.sourceAttributionRemainsDomainLocal

crossQueryPromotionBlocked : Bool
crossQueryPromotionBlocked =
  Kernel.crossQueryPromotionAllowed
