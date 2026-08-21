module DASHI.Biology.TwoBoundaryHyperformalismExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper

------------------------------------------------------------------------
-- TWO-BOUNDARY SECTION THROUGH A FINITE HYPERFABRIC
--
-- Source lineage / mathematical precedent:
--
-- Yakir Aharonov, Peter G. Bergmann, Joel L. Lebowitz,
-- "Time Symmetry in the Quantum Process of Measurement",
-- Physical Review 134 (1964), B1410-B1416.
-- DOI: 10.1103/PhysRev.134.B1410
--
-- Yakir Aharonov, Sandu Popescu, Jeff Tollaksen, Lev Vaidman,
-- "Multiple-time states and multiple-time measurements in quantum mechanics",
-- Physical Review A 79 (2009), 052110.
-- DOI: 10.1103/PhysRevA.79.052110
--
-- DASHI imports only the two-/multi-boundary conditioning architecture.
-- No quantum cognition or retrocausal biology is asserted here.
------------------------------------------------------------------------

data Cell : Set where
  startCell threatIntermediate safeIntermediate goalCell : Cell

data Edge : Cell → Cell → Set where
  startThreat : Edge startCell threatIntermediate
  startSafe : Edge startCell safeIntermediate
  threatGoal : Edge threatIntermediate goalCell
  safeGoal : Edge safeIntermediate goalCell

data Reach : Cell → Cell → Set where
  reachRefl : ∀ {x} → Reach x x
  reachEdge : ∀ {x y} → Edge x y → Reach x y
  reachCompose : ∀ {x y z} → Reach x y → Reach y z → Reach x z

threatPath : Reach startCell goalCell
threatPath =
  reachCompose (reachEdge startThreat) (reachEdge threatGoal)

safePath : Reach startCell goalCell
safePath =
  reachCompose (reachEdge startSafe) (reachEdge safeGoal)

record TwoBoundarySection : Set where
  constructor twoBoundarySection
  field
    intermediate : Cell
    fromPast : Reach startCell intermediate
    toFuture : Reach intermediate goalCell

open TwoBoundarySection public

threatSection : TwoBoundarySection
threatSection =
  twoBoundarySection
    threatIntermediate
    (reachEdge startThreat)
    (reachEdge threatGoal)

safeSection : TwoBoundarySection
safeSection =
  twoBoundarySection
    safeIntermediate
    (reachEdge startSafe)
    (reachEdge safeGoal)

samePastAndFutureAdmitDistinctIntermediateCells :
  intermediate threatSection ≡ intermediate safeSection → ⊥
samePastAndFutureAdmitDistinctIntermediateCells ()

data FutureBoundaryKind : Set where
  actualPostselected predictedFuture desiredFuture : FutureBoundaryKind

data FutureConstraint : Set where
  avoidThreatGoal flexibleSafetyGoal : FutureConstraint

chosenIntermediate : FutureConstraint → Cell
chosenIntermediate avoidThreatGoal = threatIntermediate
chosenIntermediate flexibleSafetyGoal = safeIntermediate

samePastDifferentFutureConstraintChangesSection :
  chosenIntermediate avoidThreatGoal ≡ chosenIntermediate flexibleSafetyGoal → ⊥
samePastDifferentFutureConstraintChangesSection ()

------------------------------------------------------------------------
-- Same future boundary, different embodied history can also change the live
-- intermediate section.  The future constraint remains the same in this
-- witness; the distinction is carried by learned/history state.
------------------------------------------------------------------------

data EmbodiedHistory : Set where
  flexibleHistory threatBiasedHistory : EmbodiedHistory

historyConditionedIntermediate : EmbodiedHistory → FutureConstraint → Cell
historyConditionedIntermediate flexibleHistory flexibleSafetyGoal = safeIntermediate
historyConditionedIntermediate threatBiasedHistory flexibleSafetyGoal = threatIntermediate
historyConditionedIntermediate flexibleHistory avoidThreatGoal = threatIntermediate
historyConditionedIntermediate threatBiasedHistory avoidThreatGoal = threatIntermediate

sameFutureDifferentEmbodiedHistoryChangesSection :
  historyConditionedIntermediate flexibleHistory flexibleSafetyGoal
  ≡ historyConditionedIntermediate threatBiasedHistory flexibleSafetyGoal → ⊥
sameFutureDifferentEmbodiedHistoryChangesSection ()

------------------------------------------------------------------------
-- Every intermediate cell has a local rank-three cubie address in the existing
-- recursive hypervoxel language.
------------------------------------------------------------------------

cellCubie : Cell → Hyper.AxisBlock 3
cellCubie startCell =
  Hyper.block-cons Hyper.axis-mid
    (Hyper.block-cons Hyper.axis-mid
      (Hyper.block-cons Hyper.axis-mid Hyper.block-root))
cellCubie threatIntermediate =
  Hyper.block-cons Hyper.axis-high
    (Hyper.block-cons Hyper.axis-low
      (Hyper.block-cons Hyper.axis-low Hyper.block-root))
cellCubie safeIntermediate =
  Hyper.block-cons Hyper.axis-low
    (Hyper.block-cons Hyper.axis-high
      (Hyper.block-cons Hyper.axis-high Hyper.block-root))
cellCubie goalCell =
  Hyper.block-cons Hyper.axis-high
    (Hyper.block-cons Hyper.axis-high
      (Hyper.block-cons Hyper.axis-mid Hyper.block-root))

record TwoBoundaryHyperformalismBoundary : Set where
  constructor twoBoundaryHyperformalismBoundary
  field
    predictedFutureIsActualPostselection : Bool
    desiredFutureCausesPresentRetrocausally : Bool
    tsvfImpliesQuantumBrain : Bool
    intermediateSectionCanDependOnBothBoundaries : Bool
    embodiedHistoryCanChangeSectionAtSameFutureBoundary : Bool
    historyEqualsEndpoint : Bool

canonicalTwoBoundaryHyperformalismBoundary :
  TwoBoundaryHyperformalismBoundary
canonicalTwoBoundaryHyperformalismBoundary =
  twoBoundaryHyperformalismBoundary false false false true true false
