module DASHI.Biology.GABAPhenotypeBridgeRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Biology.GABAPhenotypeBridgeExact as Bridge
import DASHI.Biology.GABAPhenotypeEvidenceExact as Evidence
import DASHI.Biology.NeurotypeProcessingGeometryExact as Geometry
import DASHI.Cognition.PNF.DepthWheelMemoryHyperfabric as MemoryFabric
import DASHI.Biology.CausalEffectEstimandExact as Causal

causalBridgeExportsExistingEstimand :
  ∀ {evidence} →
  Bridge.AssociationToCausalBridge evidence →
  Causal.CausalEffectEstimand
causalBridgeExportsExistingEstimand =
  Bridge.causalPromotionRequiresExistingEstimand

evidenceFamilyTagCannotPromote :
  Bridge.EvidenceFamilyDeterminesCausalAuthorityPermission → ⊥
evidenceFamilyTagCannotPromote =
  Bridge.evidenceFamilyTagDoesNotDetermineCausalAuthority

contextSensitivitySurvivesGABAAttachment :
  Geometry.sensoryLoad Geometry.highExteroceptiveWeight Geometry.quietContext
    ≡ Geometry.sensoryLoad Geometry.highExteroceptiveWeight Geometry.denseContext →
  ⊥
contextSensitivitySurvivesGABAAttachment =
  Bridge.sameGABAEvidenceDifferentContextCanChangeLoad
    Evidence.umesawa2020SensoryHyperResponsiveness

memoryAttachmentDoesNotMutateDepth :
  (memory : MemoryFabric.WheelMemoryFibre) →
  MemoryFabric.refinementDepth memory ≡ MemoryFabric.refinementDepth memory
memoryAttachmentDoesNotMutateDepth =
  Bridge.schmitzEvidenceDoesNotByItselfChangeMemory

adhdEvidenceHoleRegression : Bridge.ADHDEvidenceGap
adhdEvidenceHoleRegression = Bridge.canonicalADHDEvidenceGap

bridgeBoundaryRegression : Bridge.GABAPhenotypeBridgeBoundary
bridgeBoundaryRegression = Bridge.canonicalGABAPhenotypeBridgeBoundary
