module Ontology.Hecke.CurrentGeneratorPersistenceRefinement where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.ShiftContractCollapseTime as SCT
  using
    ( GeneratorCollapseClass
    ; collapseTime
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
    ; explicitWidth1
    ; explicitWidth2
    ; explicitWidth3
    )
open import Ontology.Hecke.DefectOrbitCollapseBridge as DOCB
  using (forcedStableCountOrbitP2)
open import Ontology.Hecke.DefectPersistenceRefinement as DPR
  using
    ( RefinedPressureLevel
    ; StayRefinement
    ; exactOrbitPressureAt
    ; highStay
    ; lowStay
    ; nonStay
    ; refinedPressureLevel
    )
open import Ontology.Hecke.SupportCascadePersistence as SCP
  using (supportCascadeForcedStableOrbitP2≡15)

------------------------------------------------------------------------
-- Current all-generator refinement law.
--
-- This extends the previous certified representative refinement from the
-- original finite certified subset to every currently landed generator class
-- in the collapse taxonomy.  The only new non-certified case is the mixed-
-- scale `supportCascade` branch, which now lands explicitly on the same
-- saturated stay side as the existing high-stay representatives.

currentStayRefinement : GeneratorCollapseClass → StayRefinement
currentStayRefinement (prefixClass explicitWidth1) = lowStay
currentStayRefinement (prefixClass explicitWidth2) = nonStay
currentStayRefinement (prefixClass explicitWidth3) = highStay
currentStayRefinement (prefixClass balancedCycle) = nonStay
currentStayRefinement (prefixClass denseComposed) = highStay
currentStayRefinement (prefixClass balancedComposed) = nonStay
currentStayRefinement (prefixClass anchoredTrajectory) = nonStay
currentStayRefinement (mixedScaleClass supportCascade) = highStay
currentStayRefinement (mixedScaleClass fullSupportCascade) = nonStay

currentExactOrbitPressureAt : GeneratorCollapseClass → Nat
currentExactOrbitPressureAt c = exactOrbitPressureAt (currentStayRefinement c)

currentRefinedPressureLevel : GeneratorCollapseClass → RefinedPressureLevel
currentRefinedPressureLevel c =
  refinedPressureLevel (currentStayRefinement c)

currentOrbitPressureLaw :
  ∀ c →
  forcedStableCountOrbitP2 c ≡ currentExactOrbitPressureAt c
currentOrbitPressureLaw (prefixClass explicitWidth1) = refl
currentOrbitPressureLaw (prefixClass explicitWidth2) = refl
currentOrbitPressureLaw (prefixClass explicitWidth3) = refl
currentOrbitPressureLaw (prefixClass balancedCycle) = refl
currentOrbitPressureLaw (prefixClass denseComposed) = refl
currentOrbitPressureLaw (prefixClass balancedComposed) = refl
currentOrbitPressureLaw (prefixClass anchoredTrajectory) = refl
currentOrbitPressureLaw (mixedScaleClass supportCascade)
  rewrite supportCascadeForcedStableOrbitP2≡15 = refl
currentOrbitPressureLaw (mixedScaleClass fullSupportCascade) = refl

supportCascade-highStay :
  currentStayRefinement (mixedScaleClass supportCascade) ≡ highStay
supportCascade-highStay = refl

supportCascade-saturatedPressure :
  currentRefinedPressureLevel (mixedScaleClass supportCascade) ≡ DPR.saturatedPressure
supportCascade-saturatedPressure = refl
