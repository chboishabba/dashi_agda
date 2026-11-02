{-# OPTIONS --safe #-}
module DASHI.Unified.LeechQualityGuardTOEBridgeExact where

-- Normalized theorem-owner bridge for the E8-first Leech-LILA MoE cut.
-- Original Leech-LILA: Anatolii Kornienko,
-- DOI 10.5281/zenodo.18784424.
-- New DASHI proof owners:
-- Reasoning/LeechQualityGateTeacherErasureExact
-- Reasoning/LeechSharedCanonicalOrbitHistoryExact.
-- Executable candidate owner: chboishabba/LeechTransformer PR #4.
--
-- Both finite theorems have DIFFERENT prerequisites.
-- Full gate admission yields teacher-free trace equivalence.
-- Invertible, genuinely shared history charts yield canonical reopening.
-- Neither theorem implies trained E8 quality, a literal Leech lattice
-- automorphism, semantic equivalence, or a measured distributed speedup.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Equality using (_≡_)
import DASHI.Reasoning.LeechQualityGateTeacherErasureExact as Quality
import DASHI.Reasoning.LeechSharedCanonicalOrbitHistoryExact as Orbit

toeTeacherFreeReplayUnderFullAdmission :
  ∀ {L : Nat} {State : Set} →
  (program : Quality.LayerProgram L State) →
  Quality.AllGatesFull program →
  (schedule : List (Fin L)) (initial : State) →
  Quality.hybridTrace program schedule initial
    ≡ Quality.teacherFreeTrace program schedule initial
toeTeacherFreeReplayUnderFullAdmission =
  Quality.fullAdmissionPreservesEntireTrace

toeCanonicalHistoryReopensFromAnyExpert :
  ∀ {E : Nat} {State : Set} →
  (family : Orbit.CanonicalHistoryFamily E State) →
  (expert : Fin E) →
  Orbit.recoverCanonical family expert ≡ Orbit.canonical family
toeCanonicalHistoryReopensFromAnyExpert =
  Orbit.everyExpertReopensSharedCanonical

-- Global student-only training does NOT require the deployed gate
-- configuration to change. The proof's premise matches only the
-- student functions; teacher functions and gate values may differ.
toeStudentRolloutGateIndependent :
  ∀ {L : Nat} {State : Set} →
  (first second : Quality.LayerProgram L State) →
  ((layer : Fin L) (state : State) →
      Quality.studentStep first layer state
        ≡ Quality.studentStep second layer state) →
  (schedule : List (Fin L)) (initial : State) →
  Quality.studentRollout first schedule initial
    ≡ Quality.studentRollout second schedule initial
toeStudentRolloutGateIndependent =
  Quality.studentRolloutIndependentOfGates
