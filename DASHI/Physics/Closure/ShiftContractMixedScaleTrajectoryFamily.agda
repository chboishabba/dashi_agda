module DASHI.Physics.Closure.ShiftContractMixedScaleTrajectoryFamily where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.ShiftContractAnchoredTrajectoryFamily as SATJ
  using (shiftStep)
open import DASHI.Physics.Closure.ShiftContractFullSupportTrajectory as FS
  using
    ( fullSupport
    ; fullStep01
    ; fullStep12
    ; fullStep23
    ; fullStep34
    ; fullToDenseExit
    ; denseToAnchoredExit
    ; anchoredToOneHotExit
    )
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)
open import DASHI.Physics.Closure.ShiftContractSupportCascadeTrajectory as SSCT
  using
    ( cascade0
    ; cascade1
    ; cascade2
    ; cascade3
    ; cascadeStep01
    ; cascadeStep12
    ; cascadeStep23
    ; cascadeStep34
    ; cascadeDenseFibre
    ; cascadeDenseToAnchored
    ; cascadeAnchoredToOneHot
    )

------------------------------------------------------------------------
-- Normalized mixed-scale trajectory surface above the same-fibre 3-state
-- generator classes.
--
-- The repo now has two theorem-bearing mixed-scale trajectories:
-- - a dense support-cascade that stays in one fibre for one step, then exits;
-- - a full-support cascade that exits immediately and keeps descending.
--
-- This module packages those shapes into one reusable interface so later
-- search/control code can quantify over mixed-scale generators without
-- reopening the individual trajectory modules.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

data MixedScaleGeneratorClass : Set where
  supportCascade : MixedScaleGeneratorClass
  fullSupportCascade : MixedScaleGeneratorClass

data FibreTransition
  (x y : ShiftContractState) : Set where
  staysInFibre :
    π-mdl-max x ≡ π-mdl-max y →
    FibreTransition x y
  exitsFibre :
    π-mdl-max x ≢ π-mdl-max y →
    FibreTransition x y

record MixedScaleTrajectoryFamily : Set₁ where
  field
    familyClass : MixedScaleGeneratorClass
    levelStart : ShiftContractState
    levelNext : ShiftContractState
    levelNext2 : ShiftContractState
    levelNext3 : ShiftContractState
    step01 : shiftStep levelStart ≡ levelNext
    step12 : shiftStep levelNext ≡ levelNext2
    step23 : shiftStep levelNext2 ≡ levelNext3
    step34 : shiftStep levelNext3 ≡ levelNext3
    transition01 : FibreTransition levelStart levelNext
    transition12 : FibreTransition levelNext levelNext2
    transition23 : FibreTransition levelNext2 levelNext3

canonicalSupportCascadeMixedScaleFamily :
  MixedScaleTrajectoryFamily
canonicalSupportCascadeMixedScaleFamily =
  record
    { familyClass = supportCascade
    ; levelStart = cascade0
    ; levelNext = cascade1
    ; levelNext2 = cascade2
    ; levelNext3 = cascade3
    ; step01 = cascadeStep01
    ; step12 = cascadeStep12
    ; step23 = cascadeStep23
    ; step34 = cascadeStep34
    ; transition01 = staysInFibre cascadeDenseFibre
    ; transition12 = exitsFibre cascadeDenseToAnchored
    ; transition23 = exitsFibre cascadeAnchoredToOneHot
    }

canonicalFullSupportMixedScaleFamily :
  MixedScaleTrajectoryFamily
canonicalFullSupportMixedScaleFamily =
  record
    { familyClass = fullSupportCascade
    ; levelStart = fullSupport
    ; levelNext = cascade1
    ; levelNext2 = cascade2
    ; levelNext3 = cascade3
    ; step01 = fullStep01
    ; step12 = fullStep12
    ; step23 = fullStep23
    ; step34 = fullStep34
    ; transition01 = exitsFibre fullToDenseExit
    ; transition12 = exitsFibre denseToAnchoredExit
    ; transition23 = exitsFibre anchoredToOneHotExit
    }

familyAt : MixedScaleGeneratorClass → MixedScaleTrajectoryFamily
familyAt supportCascade = canonicalSupportCascadeMixedScaleFamily
familyAt fullSupportCascade = canonicalFullSupportMixedScaleFamily

record ShiftContractMixedScaleTrajectorySchema : Set₂ where
  field
    family : MixedScaleGeneratorClass → MixedScaleTrajectoryFamily

canonicalShiftContractMixedScaleTrajectorySchema :
  ShiftContractMixedScaleTrajectorySchema
canonicalShiftContractMixedScaleTrajectorySchema =
  record
    { family = familyAt
    }

open MixedScaleTrajectoryFamily public
open ShiftContractMixedScaleTrajectorySchema public
