{-# OPTIONS --safe #-}
module DASHI.Core.TwinPickoverHistoryHypervoxelTransportExact where

-- Shared *exact* transport: history is the state, never an independent sample.
-- Consumer-specific quantitative analytic theorems are separate.
open import DASHI.Core.Prelude
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper

record HistorySection (State Outcome : Set) : Set₁ where
  field
    initial : State
    consumer : State → Outcome
open HistorySection public

record RetainedVoxel {State : Set}
    (rank coarseDepth fineDepth : Nat) : Set where
  constructor retainedVoxel
  field
    coarse : Hyper.TernaryAddress rank coarseDepth
    suffix : Hyper.AddressSuffix rank fineDepth
open RetainedVoxel public

fine : ∀ {State} {rank coarseDepth fineDepth} →
  RetainedVoxel {State} rank coarseDepth fineDepth →
  Hyper.TernaryAddress rank (Hyper._⊕_ coarseDepth fineDepth)
fine voxel = Hyper.joinAddress (coarse voxel) (suffix voxel)

record TransportHistory (State Outcome : Set)
    (rank coarseDepth fineDepth : Nat) : Set₁ where
  constructor transportHistory
  field
    history : State
    voxel : RetainedVoxel {State} rank coarseDepth fineDepth
    observe : State → Outcome
open TransportHistory public

readRetained : ∀ {State Outcome rank coarseDepth fineDepth} →
  TransportHistory State Outcome rank coarseDepth fineDepth → Outcome
readRetained h = observe h (history h)

readOriginal : ∀ {State Outcome rank coarseDepth fineDepth} →
  TransportHistory State Outcome rank coarseDepth fineDepth → Outcome
readOriginal h = observe h (history h)

forwardConsumer : ∀ {State Outcome rank coarseDepth fineDepth} →
  (h : TransportHistory State Outcome rank coarseDepth fineDepth) →
  readRetained h ≡ readOriginal h
forwardConsumer h = refl

backwardConsumer : ∀ {State Outcome rank coarseDepth fineDepth} →
  (h : TransportHistory State Outcome rank coarseDepth fineDepth) →
  readOriginal h ≡ readRetained h
backwardConsumer h = refl

coarsenSingleStep :
  ∀ {rank depth}
  (parent : Hyper.TernaryAddress rank depth)
  (child : Hyper.AxisBlock rank) →
  Hyper.coarsen (Hyper.address-refine parent child) ≡ parent
coarsenSingleStep = Hyper.coarsenAfterRefine

-- NOTE: readRetained/readOriginal are definitionally identical by design:
-- these lemmas make no claim that a coarse projection alone is sufficient.
-- For genuine descent, use the existing ConsumerIndexedResidualRefinementExact.
