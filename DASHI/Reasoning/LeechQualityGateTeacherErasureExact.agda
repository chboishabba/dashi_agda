{-# OPTIONS --safe #-}
module DASHI.Reasoning.LeechQualityGateTeacherErasureExact where

-- Formal contract for the new guarded teacher->student export cut.
-- Original trained model: Anatolii Kornienko, Leech-LILA,
-- DOI 10.5281/zenodo.18784424.
-- Executable experimental owner:
-- chboishabba/LeechTransformer PR #4,
-- scripts/train_guarded_moe_continuation.py and
-- scripts/promote_guarded_moe.py (2026-11-02).
--
-- This is an independently constructed DASHI finite-control theorem.
-- No correspondence to floating PyTorch, trained neural quality, E8
-- expert equivariance, network latency, or Leech lattice is asserted.
-- Intermediate alpha in (0,1) is intentionally NOT a teacher erasure:
-- the deployed dense FFN remains necessary until every layer has alpha=1.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

data Gate : Set where
  denseOnly : Gate
  studentOnly : Gate

selectImplementation : ∀ {A : Set} → Gate → A → A → A
selectImplementation denseOnly teacher student = teacher
selectImplementation studentOnly teacher student = student

zeroGatePreservesTeacher :
  ∀ {A : Set} (teacher student : A) →
  selectImplementation denseOnly teacher student ≡ teacher
zeroGatePreservesTeacher teacher student = refl

fullGateErasesTeacher :
  ∀ {A : Set} (teacher student : A) →
  selectImplementation studentOnly teacher student ≡ student
fullGateErasesTeacher teacher student = refl

record LayerProgram (L : Nat) (State : Set) : Set where
  constructor layerProgram
  field
    gate : Fin L → Gate
    teacherStep : Fin L → State → State
    studentStep : Fin L → State → State
open LayerProgram public

hybridStep :
  ∀ {L : Nat} {State : Set} →
  LayerProgram L State → Fin L → State → State
hybridStep program layer state =
  selectImplementation (gate program layer)
    (teacherStep program layer state)
    (studentStep program layer state)

teacherFreeStep :
  ∀ {L : Nat} {State : Set} →
  LayerProgram L State → Fin L → State → State
teacherFreeStep program layer = studentStep program layer

record AllGatesFull
       {L : Nat} {State : Set} (program : LayerProgram L State)
       : Set where
  constructor allGatesFull
  field
    admitted : (layer : Fin L) → gate program layer ≡ studentOnly
open AllGatesFull public

fullLayerEliminatesTeacher :
  ∀ {L : Nat} {State : Set} →
  (program : LayerProgram L State) →
  AllGatesFull program →
  (layer : Fin L) (state : State) →
  hybridStep program layer state ≡ teacherFreeStep program layer state
fullLayerEliminatesTeacher program witness layer state
  rewrite admitted witness layer = refl

hybridTrace :
  ∀ {L : Nat} {State : Set} →
  LayerProgram L State → List (Fin L) → State → State
hybridTrace program [] state = state
hybridTrace program (layer ∷ rest) state =
  hybridTrace program rest (hybridStep program layer state)

teacherFreeTrace :
  ∀ {L : Nat} {State : Set} →
  LayerProgram L State → List (Fin L) → State → State
teacherFreeTrace program [] state = state
teacherFreeTrace program (layer ∷ rest) state =
  teacherFreeTrace program rest (teacherFreeStep program layer state)

fullAdmissionPreservesEntireTrace :
  ∀ {L : Nat} {State : Set} →
  (program : LayerProgram L State) →
  AllGatesFull program →
  (schedule : List (Fin L)) (initial : State) →
  hybridTrace program schedule initial
    ≡ teacherFreeTrace program schedule initial
fullAdmissionPreservesEntireTrace program witness [] state = refl
fullAdmissionPreservesEntireTrace program witness (layer ∷ rest) state
  rewrite admitted witness layer =
  fullAdmissionPreservesEntireTrace program witness rest
    (studentStep program layer state)

-- The theorem's admission premise is a proof obligation. It must not
-- be fabricated from the CE score or from a gate-zero dense fallback.
-- The executable implementation additionally checks an independently
-- heldout quality budget and numeric logit parity before export.
