module DASHI.Economics.AIPartialCoordinateBounds2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIMultiplexSourceWeightedGraph2026Exact as Graph
import DASHI.Economics.AnthropicProspectusCapitalRecovery2026Exact as Anthropic

------------------------------------------------------------------------
-- PARTIAL-INFORMATION COORDINATE BOUNDS
--
-- Incomplete source vectors still carry information.  The safe operation is
-- to retain an interval/lower bound, not to coerce unknown mass to zero and not
-- to promote an interval to a complete point estimate.
------------------------------------------------------------------------

record BasisPointInterval : Set where
  constructor basisPointInterval
  field
    lower : Nat
    upper : Nat
    upperBoundReceipt : String
    complete : Bool

open BasisPointInterval public

------------------------------------------------------------------------
-- Anthropic customer concentration bound from the cited 2025 revenue vector:
-- two disclosed unnamed customers each account for 12% of revenue.
--
-- Certain HHI mass = 0.12² + 0.12² = 0.0288 = 288 / 10000.
-- If all undisclosed 76% were one counterparty, HHI = 0.6064 = 6064 / 10000.
-- We intentionally keep the whole interval.
------------------------------------------------------------------------

anthropicCustomerConcentrationBounds : BasisPointInterval
anthropicCustomerConcentrationBounds = basisPointInterval
  288
  6064
  "Reuters analysis of Anthropic IPO filing: two customers each 12% of 2025 revenue; undisclosed 76% tail unresolved"
  false

anthropicConcentrationSource : Set
anthropicConcentrationSource = Anthropic.ProspectusReading

------------------------------------------------------------------------
-- The global selected-component terminal-payer vector is not yet aligned on a
-- common flow horizon.  Thus the only sound global conductance bound remains
-- [0,1], represented here as [0,10000] basis points.
------------------------------------------------------------------------

currentTerminalConductanceBounds : BasisPointInterval
currentTerminalConductanceBounds = basisPointInterval
  0
  10000
  "terminal-payer identity and complete revenue vector remain open on a common flow horizon"
  false

record PartialCoordinateCut : Set where
  constructor partialCoordinateCut
  field
    graphCut : Graph.CurrentWeightedGraphCut
    concentrationBounds : BasisPointInterval
    terminalBounds : BasisPointInterval
    pointEstimatePromotionAllowed : Bool
    pointEstimatePromotionAllowedIsFalse :
      pointEstimatePromotionAllowed ≡ false

open PartialCoordinateCut public

currentPartialCoordinateCut : PartialCoordinateCut
currentPartialCoordinateCut = partialCoordinateCut
  Graph.currentOctober2026WeightedGraphCut
  anthropicCustomerConcentrationBounds
  currentTerminalConductanceBounds
  false refl

data IntervalImpliesPointEstimatePermission : Set where
data LowerBoundImpliesCompleteVectorPermission : Set where

intervalDoesNotAutoBecomePointEstimate :
  IntervalImpliesPointEstimatePermission → ⊥
intervalDoesNotAutoBecomePointEstimate ()

lowerBoundDoesNotAutoCloseRevenueVector :
  LowerBoundImpliesCompleteVectorPermission → ⊥
lowerBoundDoesNotAutoCloseRevenueVector ()

currentBoundsStillNonPromotable :
  pointEstimatePromotionAllowed currentPartialCoordinateCut ≡ false
currentBoundsStillNonPromotable = refl
