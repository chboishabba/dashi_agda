{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayFixedGroupMaxCutRound477Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND477: FIX THE COMPACT-SIMPLE GROUP BEFORE ANALYSIS
--
-- Clay quantifies externally over compact-simple G.  Inside the analytic proof
-- all objects are specialized to one exact G.  Group-dependent constants are
-- therefore legitimate; only cutoff/scale uniformity demanded by the fixed-G
-- consumer remains an analytic obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record FixedGroupYM
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    : Set₁ where
  field
    compactSimple :
      Top.IsCompactSimple S group

    finiteMeasure :
      Top.Cutoff C → Top.FiniteMeasure C

    continuumMeasure :
      Top.ContinuumMeasure C

    schwinger :
      Top.SchwingerFamily C

    hilbertSpace :
      Top.HilbertSpace C

    hamiltonian :
      Top.Hamiltonian C

    vacuum :
      Top.VacuumState C

    massGap :
      ℚ

open FixedGroupYM public

specializeAt :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S)
    (allCompactSimple : ∀ G → Top.IsCompactSimple S G)
    (group : Top.CompactSimpleGroup C) →
  FixedGroupYM Y group
specializeAt Y allCompactSimple group = record
  { compactSimple = allCompactSimple group
  ; finiteMeasure = Top.finiteMeasure Y group
  ; continuumMeasure = Top.continuumMeasure Y group
  ; schwinger = Top.schwinger Y group
  ; hilbertSpace = Top.hilbertSpace Y group
  ; hamiltonian = Top.hamiltonian Y group
  ; vacuum = Top.vacuum Y group
  ; massGap = Top.massGap Y group
  }

finiteMeasureIsSelectedGroupProjection :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S)
    (allCompactSimple : ∀ G → Top.IsCompactSimple S G)
    group cutoff →
  finiteMeasure (specializeAt Y allCompactSimple group) cutoff
  ≡ Top.finiteMeasure Y group cutoff
finiteMeasureIsSelectedGroupProjection Y allCompactSimple group cutoff = refl

continuumIsSelectedGroupProjection :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S)
    (allCompactSimple : ∀ G → Top.IsCompactSimple S G)
    group →
  continuumMeasure (specializeAt Y allCompactSimple group)
  ≡ Top.continuumMeasure Y group
continuumIsSelectedGroupProjection Y allCompactSimple group = refl

hamiltonianIsSelectedGroupProjection :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S)
    (allCompactSimple : ∀ G → Top.IsCompactSimple S G)
    group →
  hamiltonian (specializeAt Y allCompactSimple group)
  ≡ Top.hamiltonian Y group
hamiltonianIsSelectedGroupProjection Y allCompactSimple group = refl

gapIsSelectedGroupProjection :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S)
    (allCompactSimple : ∀ G → Top.IsCompactSimple S G)
    group →
  massGap (specializeAt Y allCompactSimple group)
  ≡ Top.massGap Y group
gapIsSelectedGroupProjection Y allCompactSimple group = refl

record GroupDependentConstant
    {C : Top.LiteralYangMillsCarriers}
    (Constant : Set)
    : Set₁ where
  field
    constantFor :
      Top.CompactSimpleGroup C → Constant

open GroupDependentConstant public

clayQuantifierIsExternalPerGroup : Bool
clayQuantifierIsExternalPerGroup = true

oneConstantUniformAcrossAllGroupsRequired : Bool
oneConstantUniformAcrossAllGroupsRequired = false

groupDependentConstantsAllowed : Bool
groupDependentConstantsAllowed = true

fixedGroupCutoffUniformityMayStillBeRequired : Bool
fixedGroupCutoffUniformityMayStillBeRequired = true

postHocSameGroupWeldRequired : Bool
postHocSameGroupWeldRequired = false

round477FixedGroupCompilerLevel : ProofLevel
round477FixedGroupCompilerLevel = machineChecked
