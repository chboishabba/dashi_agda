{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.HierarchicalDeltaFusionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- HIERARCHICAL EXECUTION IS DELTA COMPOSITION, NOT REBUILD CASCADING
--
-- For a hierarchy such as sentence < paragraph < message < conversation,
-- semantic ascent is expressed as
--
--     Sᵢ --emit--> Δᵢ --apply--> Sᵢ₊₁.
--
-- A bulk compiler may fuse several legal delta applications into one set-wise
-- operation, while the incremental compiler may apply them one at a time.  The
-- admissibility condition is equality of resulting semantic state.
------------------------------------------------------------------------

record HierarchicalDeltaStep
  (ChildState Delta ParentState : Set) : Set₁ where
  field
    emitDelta : ChildState → Delta
    parentBefore : ChildState → ParentState
    applyDelta : ParentState → Delta → ParentState
    parentAfter : ChildState → ParentState

    deltaStepExact :
      (child : ChildState) →
      applyDelta (parentBefore child) (emitDelta child)
        ≡ parentAfter child

open HierarchicalDeltaStep public

record DeltaFusion
  (Input Delta State : Set) : Set₁ where
  field
    firstDelta : Input → Delta
    secondDelta : Input → Delta
    initialState : Input → State
    apply : State → Delta → State

    sequential : Input → State
    fused : Input → State

    sequentialDefinition :
      (input : Input) →
      sequential input
        ≡ apply (apply (initialState input) (firstDelta input))
                (secondDelta input)

    -- Fused bulk execution is permitted only after proving it realizes the same
    -- semantic state as the sequential delta semantics.
    fusionExact :
      (input : Input) → fused input ≡ sequential input

open DeltaFusion public

fusedAndSequentialSemanticsAgree :
  ∀ {Input Delta State : Set}
    (fusion : DeltaFusion Input Delta State)
    (input : Input) →
  fused fusion input ≡ sequential fusion input
fusedAndSequentialSemanticsAgree fusion = fusionExact fusion

------------------------------------------------------------------------
-- CLOSED-FIBRE NO-RESCAN LAW
--
-- Closing a fibre produces a retained summary/delta.  A parent transition that
-- has that summary available must not semantically depend on reopening the full
-- closed child carrier.  Reopening remains an explicit exceptional operation.
------------------------------------------------------------------------

record ClosedFibreSummarySufficiency
  (ClosedFibre Summary ParentInput ParentResult : Set) : Set₁ where
  field
    summarize : ClosedFibre → Summary
    parentFromClosed : ParentInput → ClosedFibre → ParentResult
    parentFromSummary : ParentInput → Summary → ParentResult

    summarySufficient :
      (input : ParentInput) →
      (closed : ClosedFibre) →
      parentFromClosed input closed
        ≡ parentFromSummary input (summarize closed)

open ClosedFibreSummarySufficiency public

closedFibreNeedNotBeRescanned :
  ∀ {ClosedFibre Summary ParentInput ParentResult : Set}
    (system : ClosedFibreSummarySufficiency
      ClosedFibre Summary ParentInput ParentResult)
    (input : ParentInput)
    (closed : ClosedFibre) →
  parentFromClosed system input closed
    ≡ parentFromSummary system input (summarize system closed)
closedFibreNeedNotBeRescanned system = summarySufficient system

------------------------------------------------------------------------
-- Anti-confusion boundary: hierarchy depth does not itself authorize repeated
-- reconstruction of descendants.  Any such reconstruction must be justified by
-- a failure of the retained summary/delta to be sufficient for the consumer.
------------------------------------------------------------------------

data HierarchyDepthAuthorizesRescanPermission : Set where

hierarchyDepthDoesNotAuthorizeRescan :
  HierarchyDepthAuthorizesRescanPermission → ⊥
hierarchyDepthDoesNotAuthorizeRescan ()
