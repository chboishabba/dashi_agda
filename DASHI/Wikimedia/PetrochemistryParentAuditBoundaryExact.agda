module DASHI.Wikimedia.PetrochemistryParentAuditBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- THIN PETROCHEMISTRY PARENT AUDIT BOUNDARY
--
-- This module is intentionally self-contained and dependency-light.
-- It exposes the non-factorability witness and boundary flags without
-- importing chemistry, biology deep-time, or Wikimedia snowball networks.
------------------------------------------------------------------------

data PetroleumStageCase : Set where
  petroleumInGeologicalReservoir : PetroleumStageCase
  petroleumAsExtractedFeedstock : PetroleumStageCase
  petroleumAsPetrochemicalInput : PetroleumStageCase
  petroleumCarbonAfterCombustion : PetroleumStageCase

data PetroleumSurface : Set where
  samePetroleumLabel : PetroleumSurface

data LifecycleStage : Set where
  geologicalReservoirStage : LifecycleStage
  extractedFeedStage : LifecycleStage
  industrialInputStage : LifecycleStage
  surfaceCarbonReturnStage : LifecycleStage

petroleumSurface : PetroleumStageCase → PetroleumSurface
petroleumSurface _ = samePetroleumLabel

lifecycleStage : PetroleumStageCase → LifecycleStage
lifecycleStage petroleumInGeologicalReservoir = geologicalReservoirStage
lifecycleStage petroleumAsExtractedFeedstock = extractedFeedStage
lifecycleStage petroleumAsPetrochemicalInput = industrialInputStage
lifecycleStage petroleumCarbonAfterCombustion = surfaceCarbonReturnStage

petroleumStageDefect : INF.NonFactorabilityWitness petroleumSurface lifecycleStage
petroleumStageDefect = INF.nonFactorabilityWitness
  petroleumInGeologicalReservoir petroleumAsExtractedFeedstock refl (λ ())

petroleumLabelCannotFactorLifecycleStage :
  INF.FactorsThrough petroleumSurface lifecycleStage → ⊥
petroleumLabelCannotFactorLifecycleStage =
  INF.witnessRulesOutEveryFlatFactorisation petroleumStageDefect

record PetrochemistryParentAuditBoundary : Set where
  constructor petrochemistry-parent-audit-boundary
  field
    qidsAttached : Bool
    deweyNavigationOnly : Bool
    doiSourceRolesRetained : Bool
    deepTimeCarrierAlreadyExists : Bool
    industrialTransformationCarrierAlreadyExists : Bool
    lifecycleStageSeparationAdded : Bool
    newParallelPetrochemistryOntologyNeeded : Bool
    remainingWorkConsumerSpecific : Bool

open PetrochemistryParentAuditBoundary public

canonicalPetrochemistryParentAuditBoundary : PetrochemistryParentAuditBoundary
canonicalPetrochemistryParentAuditBoundary = petrochemistry-parent-audit-boundary
  true true true true true true false true
