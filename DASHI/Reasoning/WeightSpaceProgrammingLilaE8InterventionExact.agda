{-# OPTIONS --safe #-}

module DASHI.Reasoning.WeightSpaceProgrammingLilaE8InterventionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Reasoning.WeightSpaceProgrammingInterventionExact as WSP

------------------------------------------------------------------------
-- WSP x LILA/E8: DISJOINT INTERVENTION SURFACES
--
-- Provenance:
-- MIT CSAIL: Rikiya Takehi, Jayden Teoh, Alex Zhang, Omar Khattab
--   (2026 weight-space programming experiment).
-- Sovereign-LILA/E8GPT: original SPUTNIKAI model; accessible
--   meta-introspector/sovereign-lila-e8 mirror.
-- DASHI source owners: Agda PR #1094 (semantic action), #1095
--   (E8 quantizer/bias/QK gauge), #1265 (Dust forward probes).
-- Dust: Samip Dahal, Bishwas Mandal, Serdar Gülbahar,
--   Akshay Vegesna; distinct from direct hand-written WSP edits.
-- Leech-LILA: Anatolii Kornienko.
--
-- Only WSP's standalone safe finite masked-edit owner is imported.
-- The still-open PR #1094/#1095/#1265 implementations live on
-- separate branches. Never pretend an unmerged module is imported
-- by this master-based source. Their definitions are treated as
-- source-scoped prospective adapters, not proved same-object values.
------------------------------------------------------------------------

data ModelSurface : Set where
  parameterProjection : ModelSurface
  attentionBias : ModelSurface
  e8Quantizer : ModelSurface
  e8RootCodebook : ModelSurface
  resonatorMemory : ModelSurface

-- Single-active-surface selectors are *toy coordinate roles* rather
-- than a claim about where all real tensor dependencies flow.

projectionMask : ModelSurface → ⊤ → Bool
projectionMask parameterProjection tt = true
projectionMask _ tt = false

attentionMask : ModelSurface → ⊤ → Bool
attentionMask attentionBias tt = true
attentionMask _ tt = false

-- A WSP-type edit of a projection changes only that parameter
-- coordinate in this *declared, local* model. Real inference through
-- the quantizer or attention still has to be tested independently.

projectionPatch :
  ∀ {Scalar : Set} →
  Scalar →
  (ModelSurface → ⊤ → WSP.TwoAxis Scalar) →
  ModelSurface → ⊤ → WSP.TwoAxis Scalar
projectionPatch zero =
  WSP.sparsePatch projectionMask (WSP.removeRepetitionAxis zero)

attentionPatch :
  ∀ {Scalar : Set} →
  Scalar →
  (ModelSurface → ⊤ → WSP.TwoAxis Scalar) →
  ModelSurface → ⊤ → WSP.TwoAxis Scalar
attentionPatch zero =
  WSP.sparsePatch attentionMask (WSP.removeRepetitionAxis zero)

projectionEditChangesSelectedAxis :
  ∀ {Scalar : Set} (zero : Scalar)
    (state : ModelSurface → ⊤ → WSP.TwoAxis Scalar) →
  WSP.repetitionCoordinate
    (projectionPatch zero state parameterProjection tt) ≡ zero
projectionEditChangesSelectedAxis zero state =
  WSP.selectedRepetitionRemoved
    projectionMask zero state parameterProjection tt refl

projectionEditPreservesQuantizerState :
  ∀ {Scalar : Set} (zero : Scalar)
    (state : ModelSurface → ⊤ → WSP.TwoAxis Scalar) →
  projectionPatch zero state e8Quantizer tt ≡
  state e8Quantizer tt
projectionEditPreservesQuantizerState zero state =
  WSP.unselectedColumnIsUnchanged
    projectionMask (WSP.removeRepetitionAxis zero)
    state e8Quantizer tt refl

projectionEditPreservesCodebookState :
  ∀ {Scalar : Set} (zero : Scalar)
    (state : ModelSurface → ⊤ → WSP.TwoAxis Scalar) →
  projectionPatch zero state e8RootCodebook tt ≡
  state e8RootCodebook tt
projectionEditPreservesCodebookState zero state =
  WSP.unselectedColumnIsUnchanged
    projectionMask (WSP.removeRepetitionAxis zero)
    state e8RootCodebook tt refl

projectionEditPreservesMemoryState :
  ∀ {Scalar : Set} (zero : Scalar)
    (state : ModelSurface → ⊤ → WSP.TwoAxis Scalar) →
  projectionPatch zero state resonatorMemory tt ≡
  state resonatorMemory tt
projectionEditPreservesMemoryState zero state =
  WSP.unselectedColumnIsUnchanged
    projectionMask (WSP.removeRepetitionAxis zero)
    state resonatorMemory tt refl

attentionEditPreservesQuantizerState :
  ∀ {Scalar : Set} (zero : Scalar)
    (state : ModelSurface → ⊤ → WSP.TwoAxis Scalar) →
  attentionPatch zero state e8Quantizer tt ≡
  state e8Quantizer tt
attentionEditPreservesQuantizerState zero state =
  WSP.unselectedColumnIsUnchanged
    attentionMask (WSP.removeRepetitionAxis zero)
    state e8Quantizer tt refl

projectionPatchIdempotent :
  ∀ {Scalar : Set} (zero : Scalar)
    (state : ModelSurface → ⊤ → WSP.TwoAxis Scalar)
    (surface : ModelSurface) →
  projectionPatch zero (projectionPatch zero state)
    surface tt ≡ projectionPatch zero state surface tt
projectionPatchIdempotent zero state surface =
  WSP.sparsePatchIdempotent
    projectionMask
    (WSP.removeRepetitionAxis zero)
    state
    (WSP.removalIdempotent zero)
    surface tt

------------------------------------------------------------------------
-- A parameter-edit statement cannot be promoted into an equivalence
-- theorem for the entire E8 quantizer, attention runtime, or training
-- trajectory. Separate downstream assumptions are unavoidable.
------------------------------------------------------------------------

data LocalPatchForcesHeldOutGain : Set where
data E8RootPriorForcesCausalRepair : Set where
data ForwardOnlyUpdateIsSameAsHandwrittenEdit : Set where
data OrthogonalQKGaugeForcesChangedAttentionScore : Set where

localPatchCannotAutomaticallyClaimHeldOutGain :
  LocalPatchForcesHeldOutGain → ⊥
localPatchCannotAutomaticallyClaimHeldOutGain ()

rootPriorCannotAutomaticallyClaimRepair :
  E8RootPriorForcesCausalRepair → ⊥
rootPriorCannotAutomaticallyClaimRepair ()

dustUpdateCannotAutomaticallyEqualWSP :
  ForwardOnlyUpdateIsSameAsHandwrittenEdit → ⊥
dustUpdateCannotAutomaticallyEqualWSP ()

pureGaugeCannotAutomaticallyClaimChangedScore :
  OrthogonalQKGaugeForcesChangedAttentionScore → ⊥
pureGaugeCannotAutomaticallyClaimChangedScore ()
