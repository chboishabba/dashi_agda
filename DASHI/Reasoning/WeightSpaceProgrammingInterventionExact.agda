{-# OPTIONS --safe #-}

module DASHI.Reasoning.WeightSpaceProgrammingInterventionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Reasoning.StructuralMetaphorTaskCompressionExact as Compression
import DASHI.Reasoning.RelationRepresentationRealizationExact as Realization

------------------------------------------------------------------------
-- WEIGHT-SPACE PROGRAMMING: SOURCE-SCOPED FINITE INTERVENTION CORE
--
-- External empirical source (NOT a theorem of DASHI):
-- Rikiya Takehi, Jayden Teoh, Alex Zhang, Omar Khattab,
-- "Sparks of Weight-Space Programming", MIT CSAIL, 2 November 2026.
-- https://rikiyat.github.io/blog/weight-space-programming/
-- https://github.com/RikiyaT/lm_understand-logs/tree/main/exp8_math
--
-- The reported Qwen3.5-0.8B experiment edited 64 columns in each of
-- layers 15 and 19's MLP down-projections. The model below is a
-- coordinate/selection abstraction, NOT a proof about the actual
-- floating-point model, causal mechanism or benchmark improvement.
------------------------------------------------------------------------

-- A two-axis symbolic vector represents a candidate repetition direction
-- and a retained direction. No claim is made that Qwen has only two axes.

record TwoAxis (Scalar : Set) : Set where
  constructor twoAxis
  field
    repetitionCoordinate : Scalar
    retainedCoordinate : Scalar

open TwoAxis public

removeRepetitionAxis :
  ∀ {Scalar : Set} →
  Scalar → TwoAxis Scalar → TwoAxis Scalar
removeRepetitionAxis zero v = twoAxis zero (retainedCoordinate v)

removalKillsRepetition :
  ∀ {Scalar : Set} (zero : Scalar) (v : TwoAxis Scalar) →
  repetitionCoordinate (removeRepetitionAxis zero v) ≡ zero
removalKillsRepetition zero v = refl

removalPreservesRetained :
  ∀ {Scalar : Set} (zero : Scalar) (v : TwoAxis Scalar) →
  retainedCoordinate (removeRepetitionAxis zero v) ≡
  retainedCoordinate v
removalPreservesRetained zero v = refl

removalIdempotent :
  ∀ {Scalar : Set} (zero : Scalar) (v : TwoAxis Scalar) →
  removeRepetitionAxis zero (removeRepetitionAxis zero v) ≡
  removeRepetitionAxis zero v
removalIdempotent zero v = refl

------------------------------------------------------------------------
-- Generic layer/column masked patch: actual changed entries must be
-- certified separately AFTER casting to the deployment numeric format.
------------------------------------------------------------------------

choose : ∀ {A : Set} → Bool → A → A → A
choose true yes no = yes
choose false yes no = no

sparsePatch :
  ∀ {Layer Column Vector : Set} →
  (Layer → Column → Bool) →
  (Vector → Vector) →
  (Layer → Column → Vector) →
  Layer → Column → Vector
sparsePatch selected edit weights layer column =
  choose (selected layer column)
         (edit (weights layer column))
         (weights layer column)

selectedColumnUsesEdit :
  ∀ {Layer Column Vector : Set}
    (selected : Layer → Column → Bool)
    (edit : Vector → Vector)
    (weights : Layer → Column → Vector)
    (layer : Layer) (column : Column) →
  selected layer column ≡ true →
  sparsePatch selected edit weights layer column ≡
  edit (weights layer column)
selectedColumnUsesEdit selected edit weights layer column proof
  rewrite proof = refl

unselectedColumnIsUnchanged :
  ∀ {Layer Column Vector : Set}
    (selected : Layer → Column → Bool)
    (edit : Vector → Vector)
    (weights : Layer → Column → Vector)
    (layer : Layer) (column : Column) →
  selected layer column ≡ false →
  sparsePatch selected edit weights layer column ≡
  weights layer column
unselectedColumnIsUnchanged selected edit weights layer column proof
  rewrite proof = refl

sparsePatchIdempotent :
  ∀ {Layer Column Vector : Set}
    (selected : Layer → Column → Bool)
    (edit : Vector → Vector)
    (weights : Layer → Column → Vector) →
  ((v : Vector) → edit (edit v) ≡ edit v) →
  (layer : Layer) (column : Column) →
  sparsePatch selected edit
    (sparsePatch selected edit weights) layer column ≡
  sparsePatch selected edit weights layer column
sparsePatchIdempotent selected edit weights idem layer column
  with selected layer column
... | true = idem (weights layer column)
... | false = refl

selectedRepetitionRemoved :
  ∀ {Layer Column Scalar : Set}
    (selected : Layer → Column → Bool)
    (zero : Scalar)
    (weights : Layer → Column → TwoAxis Scalar)
    (layer : Layer) (column : Column) →
  selected layer column ≡ true →
  repetitionCoordinate
    (sparsePatch selected (removeRepetitionAxis zero)
      weights layer column) ≡ zero
selectedRepetitionRemoved selected zero weights layer column proof
  rewrite proof = refl

retainedCoordinateStable :
  ∀ {Layer Column Scalar : Set}
    (selected : Layer → Column → Bool)
    (zero : Scalar)
    (weights : Layer → Column → TwoAxis Scalar)
    (layer : Layer) (column : Column) →
  retainedCoordinate
    (sparsePatch selected (removeRepetitionAxis zero)
      weights layer column) ≡
  retainedCoordinate (weights layer column)
retainedCoordinateStable selected zero weights layer column
  with selected layer column
... | true = refl
... | false = refl

-- Two named selected layers and one unselected layer are an illustrative
-- role quotient of the real 24-layer architecture, not a tensor decoder.

data LayerRole : Set where
  layer15 : LayerRole
  layer19 : LayerRole
  otherLayer : LayerRole

data ColumnRole : Set where
  selectedColumn : ColumnRole
  otherColumn : ColumnRole

reportedRoleMask : LayerRole → ColumnRole → Bool
reportedRoleMask layer15 selectedColumn = true
reportedRoleMask layer19 selectedColumn = true
reportedRoleMask _ _ = false

layer15Selected : reportedRoleMask layer15 selectedColumn ≡ true
layer15Selected = refl

layer19Selected : reportedRoleMask layer19 selectedColumn ≡ true
layer19Selected = refl

otherLayerUnchanged : reportedRoleMask otherLayer selectedColumn ≡ false
otherLayerUnchanged = refl

nonSelectedColumnUnchanged :
  (layer : LayerRole) →
  reportedRoleMask layer otherColumn ≡ false
nonSelectedColumnUnchanged layer15 = refl
nonSelectedColumnUnchanged layer19 = refl
nonSelectedColumnUnchanged otherLayer = refl

------------------------------------------------------------------------
-- Non-promotion: preserving a declared channel cannot itself certify
-- benchmark accuracy, causal attribution, or same-checkpoint realization.
-- Reuse the existing compression and realization theorem owners.
------------------------------------------------------------------------

data ToyWorld : Set where
  loopingWorld : ToyWorld
  productiveWorld : ToyWorld

data StableChannel : Set where
  sameStableChannel : StableChannel

data TaskBehavior : Set where
  loops : TaskBehavior
  completes : TaskBehavior

stableChannel : ToyWorld → StableChannel
stableChannel loopingWorld = sameStableChannel
stableChannel productiveWorld = sameStableChannel

taskBehavior : ToyWorld → TaskBehavior
taskBehavior loopingWorld = loops
taskBehavior productiveWorld = completes

stableChannelCollision :
  Compression.CompressionFailureWitness stableChannel taskBehavior
stableChannelCollision =
  Compression.compressionFailureWitness
    loopingWorld productiveWorld refl (λ ())

stableChannelDoesNotDetermineTaskBehavior :
  Realization.RepresentationRealizationWitness
    stableChannel taskBehavior → ⊥
stableChannelDoesNotDetermineTaskBehavior =
  Realization.representationCollisionBlocksRealization
    stableChannelCollision
