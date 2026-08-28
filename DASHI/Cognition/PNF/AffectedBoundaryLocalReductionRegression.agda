module DASHI.Cognition.PNF.AffectedBoundaryLocalReductionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Cognition.PNF.AffectedBoundaryLocalReductionExact
open import DASHI.Cognition.PNF.DreamFlowRuntimeComplexityExact
  using (hierarchyTransportWork)

------------------------------------------------------------------------
-- Concrete normalization witnesses for the C3b work equations.
------------------------------------------------------------------------

emptyAffected : AffectedBoundaryKeys
emptyAffected = affectedBoundaryKeys 0 0 0 0 0 0 0 refl

data ParentState : Set where
  parentState : Nat → ParentState

data ChildDelta : Set where
  irrelevantDelta : ChildDelta

trivialLocalReducer : ParentLocalReducer ParentState ChildDelta
trivialLocalReducer = record
  { affected = λ _ → emptyAffected
  ; reduceAffected = λ state _ → state
  ; emittedDeltaCount = λ _ _ → 0
  ; noAffectedKeysPreserveState = λ _ _ _ → refl
  }

zeroAffectedPreservesConcreteParent :
  reduceAffected trivialLocalReducer (parentState 9) irrelevantDelta ≡ parentState 9
zeroAffectedPreservesConcreteParent = refl

threeDeltasTwoLevels : DeltaNativeHierarchyReceipt
threeDeltasTwoLevels =
  deltaNativeHierarchyReceipt
    3
    3
    30
    3
    2
    6
    refl

threeDeltasTwoLevelsTransportWork :
  hierarchyTransportMeasuredWork threeDeltasTwoLevels ≡ 6
threeDeltasTwoLevelsTransportWork = refl

threeDeltasTwoLevelsMatchesDreamShape :
  hierarchyTransportMeasuredWork threeDeltasTwoLevels ≡
    hierarchyTransportWork (asDreamWorkShape threeDeltasTwoLevels)
threeDeltasTwoLevelsMatchesDreamShape =
  hierarchyWorkUsesEmittedDeltas threeDeltasTwoLevels
