module Ontology.Hecke.SupportCascadePersistence where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.ShiftContractCollapseTime as SCT
  using
    ( collapseTime
    ; collapseTime-supportCascade
    ; mixedScaleClass
    ; staysOneMoreStep
    )
open import DASHI.Physics.Closure.ShiftContractMixedScaleTrajectoryFamily
  using (supportCascade)
open import MonsterOntos using (p2)
open import Ontology.Hecke.DefectOrbitCollapseBridge as DOCB
  using
    ( forcedStableCountOrbitP2
    ; orbitSummaryP2
    ; representativeState
    )
open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS
  using (DefectOrbitSummary)

------------------------------------------------------------------------
-- First extension beyond the current certified representative set:
-- the mixed-scale `supportCascade` class.
--
-- This keeps the current persistence story honest by testing the next live
-- `staysOneMoreStep` class directly on the Hecke side rather than assuming
-- the certified finite quotient already covers every current generator class.

supportCascadeCollapseTime :
  collapseTime (mixedScaleClass supportCascade) ≡ staysOneMoreStep
supportCascadeCollapseTime = collapseTime-supportCascade

supportCascadeRepresentative = representativeState (mixedScaleClass supportCascade)

supportCascadeOrbitSummaryP2 : DefectOrbitSummary
supportCascadeOrbitSummaryP2 =
  orbitSummaryP2 (mixedScaleClass supportCascade)

supportCascadeForcedStableOrbitP2 : Nat
supportCascadeForcedStableOrbitP2 =
  forcedStableCountOrbitP2 (mixedScaleClass supportCascade)

supportCascadeForcedStableOrbitP2≡15 :
  supportCascadeForcedStableOrbitP2 ≡ 15
supportCascadeForcedStableOrbitP2≡15 = refl

supportCascadeForcedStableSummaryField≡15 :
  FOS.DefectOrbitSummary.forcedStableCount supportCascadeOrbitSummaryP2 ≡ 15
supportCascadeForcedStableSummaryField≡15 = supportCascadeForcedStableOrbitP2≡15
