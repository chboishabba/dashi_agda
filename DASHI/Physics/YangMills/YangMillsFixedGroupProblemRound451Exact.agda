{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsFixedGroupProblemRound451Exact where

------------------------------------------------------------------------
-- ROUND451 / SPECIALIZE THE CLAY CONSTRUCTION AT FIXED G FIRST
--
-- The outer theorem remains:
--
--   forall compact-simple G, close YMProblemAt G.
--
-- Inside one analytic proof, however, the finite family, continuum carrier,
-- Hamiltonian and gap should already refer to THAT exact G.  This prevents
-- post-hoc same-group welds and leaves constants free to depend on G unless a
-- downstream consumer genuinely asks for uniformity across groups.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned

record YMProblemAt
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (pinned : Pinned.PinnedYangMillsConstruction S)
    (group : Top.CompactSimpleGroup C)
    : Set₁ where
  field
    groupIsCompactSimple :
      Top.IsCompactSimple S group

    finiteMeasureAt :
      Top.Cutoff C → Top.FiniteMeasure C

    continuumMeasureAt :
      Top.ContinuumMeasure C

    schwingerAt :
      Top.SchwingerFamily C

    hilbertSpaceAt :
      Top.HilbertSpace C

    hamiltonianAt :
      Top.Hamiltonian C

    vacuumAt :
      Top.VacuumState C

    massGapAt :
      ℚ

    continuumLimitAt :
      Top.IsContinuumLimitOf S group
        finiteMeasureAt continuumMeasureAt

    schwingerBelongsAt :
      Top.SchwingerBelongsToMeasure S
        continuumMeasureAt schwingerAt

    strictlyPositiveFiniteMassGapAt :
      Top.IsStrictlyPositiveFiniteMassGap S
        hamiltonianAt massGapAt

open YMProblemAt public

specializePinnedAt :
  ∀ {C S}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S)
    (group : Top.CompactSimpleGroup C) →
  YMProblemAt pinned group
specializePinnedAt pinned group = record
  { groupIsCompactSimple =
      Pinned.compactSimple pinned group
  ; finiteMeasureAt =
      λ cutoff →
        Pinned.finiteMeasure (Pinned.finite pinned) group cutoff
  ; continuumMeasureAt =
      Pinned.continuumMeasure (Pinned.continuum pinned) group
  ; schwingerAt =
      Pinned.schwinger (Pinned.continuum pinned) group
  ; hilbertSpaceAt =
      Pinned.hilbertSpace (Pinned.continuum pinned) group
  ; hamiltonianAt =
      Pinned.hamiltonian (Pinned.continuum pinned) group
  ; vacuumAt =
      Pinned.vacuum (Pinned.gap pinned) group
  ; massGapAt =
      Pinned.massGap (Pinned.gap pinned) group
  ; continuumLimitAt =
      Pinned.continuumLimit (Pinned.continuum pinned) group
  ; schwingerBelongsAt =
      Pinned.schwingerBelongsToContinuumMeasure
        (Pinned.continuum pinned) group
  ; strictlyPositiveFiniteMassGapAt =
      Pinned.strictlyPositiveFiniteMassGap
        (Pinned.gap pinned) group
  }

fixedFiniteMeasureIsPinnedProjection :
  ∀ {C S}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S)
    (group : Top.CompactSimpleGroup C)
    cutoff →
  finiteMeasureAt (specializePinnedAt pinned group) cutoff
  ≡ Pinned.finiteMeasure (Pinned.finite pinned) group cutoff
fixedFiniteMeasureIsPinnedProjection pinned group cutoff = refl

fixedContinuumMeasureIsPinnedProjection :
  ∀ {C S}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S)
    (group : Top.CompactSimpleGroup C) →
  continuumMeasureAt (specializePinnedAt pinned group)
  ≡ Pinned.continuumMeasure (Pinned.continuum pinned) group
fixedContinuumMeasureIsPinnedProjection pinned group = refl

fixedHamiltonianIsPinnedProjection :
  ∀ {C S}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S)
    (group : Top.CompactSimpleGroup C) →
  hamiltonianAt (specializePinnedAt pinned group)
  ≡ Pinned.hamiltonian (Pinned.continuum pinned) group
fixedHamiltonianIsPinnedProjection pinned group = refl

fixedGapIsPinnedProjection :
  ∀ {C S}
    (pinned : Pinned.PinnedYangMillsConstruction {C = C} S)
    (group : Top.CompactSimpleGroup C) →
  massGapAt (specializePinnedAt pinned group)
  ≡ Pinned.massGap (Pinned.gap pinned) group
fixedGapIsPinnedProjection pinned group = refl

round451FixedGroupSpecializationCompilerLevel : ProofLevel
round451FixedGroupSpecializationCompilerLevel = machineChecked

round451PostHocSameGroupEqualityRequired : Bool
round451PostHocSameGroupEqualityRequired = false

round451UniformAcrossGroupsConstantRequiredBySpecialization : Bool
round451UniformAcrossGroupsConstantRequiredBySpecialization = false
