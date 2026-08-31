module DASHI.Cognition.PNF.AffectedBoundaryLocalReductionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic
open import DASHI.Cognition.PNF.DreamFlowRuntimeComplexityExact
open import DASHI.Cognition.PNF.ParentInterfaceReduction
open import DASHI.Cognition.PNF.SparseFibredFrontier

------------------------------------------------------------------------
-- Delta-native parent reduction.
--
-- Closed child fibres expose only their boundary.  A change in that boundary
-- first determines a finite set of affected parent keys.  Only those key fibres
-- are permitted to enter the non-monotone local reducer.  Unaffected parent
-- state is retained verbatim.
------------------------------------------------------------------------

data BoundaryKeyFamily : Set where
  objectKey factorKey demandKey actorKey outwardKey : BoundaryKeyFamily

record BoundaryKey : Set where
  constructor boundaryKey
  field
    keyFamily : BoundaryKeyFamily
    keyA keyB keyC : Nat

open BoundaryKey public

record AffectedBoundaryKeys : Set where
  constructor affectedBoundaryKeys
  field
    inputBoundaryDeltaAtoms : Nat
    affectedObjectKeys : Nat
    affectedFactorKeys : Nat
    affectedDemandKeys : Nat
    affectedActorKeys : Nat
    affectedOutwardKeys : Nat
    touchedKeyCount : Nat
    touchedKeysExact :
      touchedKeyCount ≡
        affectedObjectKeys
        + affectedFactorKeys
        + affectedDemandKeys
        + affectedActorKeys
        + affectedOutwardKeys

open AffectedBoundaryKeys public

record ParentLocalReducer
    (ParentState ChildDelta : Set) : Set₁ where
  field
    affected : ChildDelta → AffectedBoundaryKeys
    reduceAffected : ParentState → ChildDelta → ParentState
    emittedDeltaCount : ParentState → ChildDelta → Nat

    -- A delta with no affected key is observationally irrelevant to this
    -- parent reducer and must preserve the parent state exactly.
    noAffectedKeysPreserveState :
      (state : ParentState) →
      (delta : ChildDelta) →
      touchedKeyCount (affected delta) ≡ 0 →
      reduceAffected state delta ≡ state

    -- Work performed is not itself semantic change.  If the reduced parent
    -- state is extensionally unchanged, hierarchy transport must stop here.
    noParentChangeEmitsNoDelta :
      (state : ParentState) →
      (delta : ChildDelta) →
      reduceAffected state delta ≡ state →
      emittedDeltaCount state delta ≡ 0

open ParentLocalReducer public

------------------------------------------------------------------------
-- Change-sensitive propagation.
--
-- The runtime is allowed to transport a parent delta only when local reduction
-- emitted one.  The hierarchy term therefore depends on emitted deltas and
-- hierarchy depth, never on accumulated lower state size.
------------------------------------------------------------------------

record DeltaNativeHierarchyReceipt : Set where
  constructor deltaNativeHierarchyReceipt
  field
    inputDeltaAtoms : Nat
    touchedParentKeys : Nat
    accumulatedParentBoundaryKeys : Nat
    emittedParentDeltas : Nat
    hierarchyDepth : Nat
    hierarchyTransportMeasuredWork : Nat

    transportWorkExact :
      hierarchyTransportMeasuredWork ≡ emittedParentDeltas * hierarchyDepth

open DeltaNativeHierarchyReceipt public

asDreamWorkShape : DeltaNativeHierarchyReceipt → DreamWorkShape
asDreamWorkShape receipt =
  dreamWorkShape
    (inputDeltaAtoms receipt)
    (touchedParentKeys receipt)
    0
    (emittedParentDeltas receipt)
    0
    0
    0
    (hierarchyDepth receipt)

hierarchyWorkUsesEmittedDeltas :
  (receipt : DeltaNativeHierarchyReceipt) →
  hierarchyTransportMeasuredWork receipt ≡
    hierarchyTransportWork (asDreamWorkShape receipt)
hierarchyWorkUsesEmittedDeltas receipt = transportWorkExact receipt

------------------------------------------------------------------------
-- Lookup remains a projection of admitted parent export, not another boundary
-- evidence family transported independently through the hierarchy.
------------------------------------------------------------------------

record DeltaNativeLookupBoundary : Set where
  constructor deltaNativeLookupBoundary
  field
    parentReductionBoundary : ParentReductionBoundary
    sparseBoundary : SparseFibredFrontierBoundary
    changedAdmittedExportCount : Nat
    changedLookupProjectionCount : Nat
    lookupChangesDoNotExceedAdmittedChanges :
      changedLookupProjectionCount ≤ᶜ changedAdmittedExportCount

open DeltaNativeLookupBoundary public

------------------------------------------------------------------------
-- Invalid execution interpretations are intentionally uninhabited.
------------------------------------------------------------------------

data UnaffectedKeyRequiresReduction : Set where

data ChildInteriorRequiredForParentDelta : Set where

data LookupIsIndependentBoundaryEvidence : Set where

data AccumulatedParentStateRescanRequired : Set where

data WorkPerformedCountsAsSemanticChange : Set where

unaffectedKeyNeedNotReduce : UnaffectedKeyRequiresReduction → ⊥
unaffectedKeyNeedNotReduce ()

closedChildInteriorNeedNotReopen : ChildInteriorRequiredForParentDelta → ⊥
closedChildInteriorNeedNotReopen ()

lookupIsNotIndependentEvidence : LookupIsIndependentBoundaryEvidence → ⊥
lookupIsNotIndependentEvidence ()

accumulatedParentStateNeedNotRescan : AccumulatedParentStateRescanRequired → ⊥
accumulatedParentStateNeedNotRescan ()

workDoesNotManufactureSemanticDelta : WorkPerformedCountsAsSemanticChange → ⊥
workDoesNotManufactureSemanticDelta ()
