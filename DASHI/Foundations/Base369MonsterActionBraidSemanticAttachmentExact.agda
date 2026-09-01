module DASHI.Foundations.Base369MonsterActionBraidSemanticAttachmentExact where

open import DASHI.Core.Prelude

import DASHI.Core.ActionCrossingTraceCalculusExact as Trace
import DASHI.Foundations.Base369MonsterSemanticCoordinateSystemExact as Semantic
import DASHI.Foundations.Base369JCoarseFineStableIdentityDisciplineExact as JIdentity

------------------------------------------------------------------------
-- ACTION-BRAID SEMANTIC ATTACHMENT
--
-- The history coordinate h is an actual ordered ActionTrace.  The residual r
-- is derived from the provenance observer of that trace rather than introduced
-- as an unrelated product coordinate.
------------------------------------------------------------------------

record ActionBraidSemanticAttachment
    (Strand Action Endpoint Provenance FutureCone : Set) : Set₁ where
  constructor action-braid-semantic-attachment
  field
    traceSurface : Trace.TraceObservationSurface Strand Action
    endpointCarrierMatches : Trace.Endpoint traceSurface ≡ Endpoint

    coarsePhaseOf : Semantic.SemanticBaseState → JIdentity.JCoarse9
    historyTraceOf :
      Semantic.SemanticBaseState → Trace.ActionTrace Strand Action
    futureConeOf : Semantic.SemanticBaseState → FutureCone

open ActionBraidSemanticAttachment public

historyResidualSystem :
  {Strand Action Endpoint Provenance FutureCone : Set} →
  (attachment :
    ActionBraidSemanticAttachment Strand Action Endpoint Provenance FutureCone) →
  Semantic.SemanticCoordinateSystem
    (Trace.ActionTrace Strand Action)
    (Trace.Provenance (traceSurface attachment))
    FutureCone
historyResidualSystem attachment =
  Semantic.semantic-coordinate-system
    (coarsePhaseOf attachment)
    (historyTraceOf attachment)
    (λ state →
      Trace.provenance
        (traceSurface attachment)
        (historyTraceOf attachment state))
    (futureConeOf attachment)

------------------------------------------------------------------------
-- The residual is definitionally the provenance reading of the retained trace.
------------------------------------------------------------------------

residualIsTraceProvenance :
  {Strand Action Endpoint Provenance FutureCone : Set} →
  (attachment :
    ActionBraidSemanticAttachment Strand Action Endpoint Provenance FutureCone) →
  (state : Semantic.SemanticBaseState) →
  Semantic.residualOf (historyResidualSystem attachment) state
  ≡ Trace.provenance
      (traceSurface attachment)
      (historyTraceOf attachment state)
residualIsTraceProvenance attachment state = refl

historyIsOrderedCrossingTrace :
  {Strand Action Endpoint Provenance FutureCone : Set} →
  (attachment :
    ActionBraidSemanticAttachment Strand Action Endpoint Provenance FutureCone) →
  Semantic.SemanticBaseState → Trace.ActionTrace Strand Action
historyIsOrderedCrossingTrace = historyTraceOf

------------------------------------------------------------------------
-- Endpoint-only observation need not recover the retained provenance.  A
-- concrete collision receipt from the trace calculus can be transported into
-- the semantic layer without changing the underlying 196830 carrier.
------------------------------------------------------------------------

record SemanticHistoryCollision
    {Strand Action Endpoint Provenance FutureCone : Set}
    (attachment :
      ActionBraidSemanticAttachment Strand Action Endpoint Provenance FutureCone) : Set where
  constructor semantic-history-collision
  field
    collision :
      Trace.SameEndpointDifferentTraceProvenance (traceSurface attachment)

open SemanticHistoryCollision public

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data HistoryTraceIsIndependentCardinalFactor : Set where
data ProvenanceResidualIsIndependentCardinalFactor : Set where
data SameEndpointMeansSameSemanticHistory : Set where
data ActionTraceAutomaticallyIsMonsterGroupAction : Set where

historyTraceDoesNotInflateBaseCarrier : HistoryTraceIsIndependentCardinalFactor → ⊥
historyTraceDoesNotInflateBaseCarrier ()

provenanceResidualDoesNotInflateBaseCarrier :
  ProvenanceResidualIsIndependentCardinalFactor → ⊥
provenanceResidualDoesNotInflateBaseCarrier ()

sameEndpointNeedNotMeanSameSemanticHistory : SameEndpointMeansSameSemanticHistory → ⊥
sameEndpointNeedNotMeanSameSemanticHistory ()

actionTraceDoesNotAutomaticallyBecomeMonsterAction :
  ActionTraceAutomaticallyIsMonsterGroupAction → ⊥
actionTraceDoesNotAutomaticallyBecomeMonsterAction ()

record MonsterActionBraidSemanticBoundary : Set where
  constructor monster-action-braid-semantic-boundary
  field
    historyCoordinateIsOrderedCrossingTrace : Bool
    residualDerivedFromTraceProvenance : Bool
    historyAttachmentInflates196830Carrier : Bool
    endpointDeterminesFullProvenance : Bool
    actionTraceAutomaticallyConstructsMonsterAction : Bool

canonicalMonsterActionBraidSemanticBoundary : MonsterActionBraidSemanticBoundary
canonicalMonsterActionBraidSemanticBoundary =
  monster-action-braid-semantic-boundary true true false false false
