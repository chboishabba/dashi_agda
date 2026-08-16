module DASHI.Governance.SocialAttractorAdaptersExact where

open import DASHI.Core.Prelude

import DASHI.Governance.GenericSocialAttractor as Generic
import DASHI.Governance.TraumaExploitationAttractor as Trauma
import DASHI.Governance.ExternalityCarrierAttractor as Externality

------------------------------------------------------------------------
-- Upward refactor by adapters, not duplication.
--
-- Existing domain modules retain their richer semantics.  This file projects
-- only their state/step surface into GenericSocialAttractor so generic fixed-
-- point/invariance theorems can be reused without rewriting those modules.
------------------------------------------------------------------------

traumaAsGenericSystem :
  Trauma.TraumaExploitationSystem →
  Generic.DiscreteSystem
traumaAsGenericSystem S =
  record
    { State = Trauma.HistoricalState S
    ; step = Trauma.step S
    }

traumaFixedPointToGeneric :
  (S : Trauma.TraumaExploitationSystem) →
  Trauma.FixedPoint S →
  Generic.FixedPoint (traumaAsGenericSystem S)
traumaFixedPointToGeneric S fixed =
  record
    { point = Trauma.FixedPoint.point fixed
    ; fixed = Trauma.FixedPoint.fixed fixed
    }

------------------------------------------------------------------------
-- ExternalityCarrierAttractor exposes a cycle carrier but not a single
-- canonical step on every case.  The adapter therefore requires the producer
-- to identify which transition is the repeated state transition.
------------------------------------------------------------------------

record ExternalityStepAdapter : Set₁ where
  field
    State : Set
    step : State → State

externalityAdapterAsGeneric :
  ExternalityStepAdapter →
  Generic.DiscreteSystem
externalityAdapterAsGeneric adapter =
  record
    { State = ExternalityStepAdapter.State adapter
    ; step = ExternalityStepAdapter.step adapter
    }

------------------------------------------------------------------------
-- The import of ExternalityCarrierAttractor is deliberate provenance: named
-- policy cases in that module remain evidence-gated.  A generic dynamical
-- adapter never manufactures an empirical transition function for them.
------------------------------------------------------------------------

record SocialAttractorAdapterBoundary : Set where
  constructor socialAttractorAdapterBoundary
  field
    genericProjectionErasesDomainSemantics : Bool
    genericFixedPointCreatesNormativeApproval : Bool
    externalityCaseGetsAutomaticDynamics : Bool
    domainSpecificReceiptStillRequired : Bool

canonicalSocialAttractorAdapterBoundary : SocialAttractorAdapterBoundary
canonicalSocialAttractorAdapterBoundary =
  socialAttractorAdapterBoundary true false false true
