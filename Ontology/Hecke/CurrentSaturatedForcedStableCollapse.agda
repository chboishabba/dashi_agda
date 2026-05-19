module Ontology.Hecke.CurrentSaturatedForcedStableCollapse where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.ShiftContractCollapseTime as SCT
  using
    ( GeneratorCollapseClass
    ; mixedScaleClass
    ; prefixClass
    )
open import DASHI.Physics.Closure.ShiftContractMixedScaleTrajectoryFamily
  using (fullSupportCascade; supportCascade)
open import DASHI.Physics.Closure.ShiftContractParametricTrajectoryCompositionFamily
  using
    ( anchoredTrajectory
    ; balancedComposed
    ; balancedCycle
    ; denseComposed
    ; explicitWidth2
    ; explicitWidth3
    )
open import Ontology.Hecke.DefectOrbitCollapseBridge as DOCB
  using
    ( forcedStableCountOrbitP2
    ; orbitSummaryP2
    )
open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS
  using (DefectOrbitSummary)
open import Ontology.Hecke.SupportCascadePersistence as SCP
  using
    ( supportCascadeForcedStableOrbitP2≡15
    ; supportCascadeForcedStableSummaryField≡15
    )

------------------------------------------------------------------------
-- Current saturated-side negative boundary at the all-generator scope.
--
-- The present `forcedStableCount`-based Hecke summary explains the low-stay
-- split, but it still collapses every currently saturated generator to the
-- same value `15`, including the mixed-scale `supportCascade` extension.

data CurrentSaturatedGenerator : Set where
  saturatedExplicitWidth3 : CurrentSaturatedGenerator
  saturatedDenseComposed : CurrentSaturatedGenerator
  saturatedBalancedCycle : CurrentSaturatedGenerator
  saturatedBalancedComposed : CurrentSaturatedGenerator
  saturatedExplicitWidth2 : CurrentSaturatedGenerator
  saturatedAnchoredTrajectory : CurrentSaturatedGenerator
  saturatedSupportCascade : CurrentSaturatedGenerator
  saturatedFullSupportCascade : CurrentSaturatedGenerator

saturatedGeneratorClass : CurrentSaturatedGenerator → GeneratorCollapseClass
saturatedGeneratorClass saturatedExplicitWidth3 = prefixClass explicitWidth3
saturatedGeneratorClass saturatedDenseComposed = prefixClass denseComposed
saturatedGeneratorClass saturatedBalancedCycle = prefixClass balancedCycle
saturatedGeneratorClass saturatedBalancedComposed = prefixClass balancedComposed
saturatedGeneratorClass saturatedExplicitWidth2 = prefixClass explicitWidth2
saturatedGeneratorClass saturatedAnchoredTrajectory = prefixClass anchoredTrajectory
saturatedGeneratorClass saturatedSupportCascade = mixedScaleClass supportCascade
saturatedGeneratorClass saturatedFullSupportCascade = mixedScaleClass fullSupportCascade

saturatedOrbitSummaryP2At : CurrentSaturatedGenerator → DefectOrbitSummary
saturatedOrbitSummaryP2At c = orbitSummaryP2 (saturatedGeneratorClass c)

saturatedForcedStableCountAt : CurrentSaturatedGenerator → Nat
saturatedForcedStableCountAt c =
  forcedStableCountOrbitP2 (saturatedGeneratorClass c)

saturatedSummaryFieldAt : CurrentSaturatedGenerator → Nat
saturatedSummaryFieldAt c =
  FOS.DefectOrbitSummary.forcedStableCount (saturatedOrbitSummaryP2At c)

saturatedForcedStableCount≡15 :
  ∀ c →
  saturatedForcedStableCountAt c ≡ 15
saturatedForcedStableCount≡15 saturatedExplicitWidth3 = refl
saturatedForcedStableCount≡15 saturatedDenseComposed = refl
saturatedForcedStableCount≡15 saturatedBalancedCycle = refl
saturatedForcedStableCount≡15 saturatedBalancedComposed = refl
saturatedForcedStableCount≡15 saturatedExplicitWidth2 = refl
saturatedForcedStableCount≡15 saturatedAnchoredTrajectory = refl
saturatedForcedStableCount≡15 saturatedSupportCascade =
  supportCascadeForcedStableOrbitP2≡15
saturatedForcedStableCount≡15 saturatedFullSupportCascade = refl

saturatedSummaryField≡15 :
  ∀ c →
  saturatedSummaryFieldAt c ≡ 15
saturatedSummaryField≡15 saturatedExplicitWidth3 = refl
saturatedSummaryField≡15 saturatedDenseComposed = refl
saturatedSummaryField≡15 saturatedBalancedCycle = refl
saturatedSummaryField≡15 saturatedBalancedComposed = refl
saturatedSummaryField≡15 saturatedExplicitWidth2 = refl
saturatedSummaryField≡15 saturatedAnchoredTrajectory = refl
saturatedSummaryField≡15 saturatedSupportCascade =
  supportCascadeForcedStableSummaryField≡15
saturatedSummaryField≡15 saturatedFullSupportCascade = refl
