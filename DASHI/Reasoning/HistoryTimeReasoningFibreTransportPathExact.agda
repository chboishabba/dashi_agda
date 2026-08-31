module DASHI.Reasoning.HistoryTimeReasoningFibreTransportPathExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.HistoryTimeRelationalReasoningFibreExact as Fibre
import DASHI.Reasoning.HistoryTimeReasoningFibreTransportExact as Transport

------------------------------------------------------------------------
-- COMPOSABLE HISTORY/TIME REASONING-FIBRE TRANSPORT PATHS
--
-- A temporal path retains every intermediate reasoning-fibre point together
-- with its local attachment receipt.  Composition therefore does not overwrite
-- history with the endpoint: the proof object still contains each governed
-- transition and each relevant attachment surface along the route.
------------------------------------------------------------------------

record AttachedGovernedStep
    {carrier : Fibre.HistoryTimeArtifactCarrier}
    (fabric : Fibre.RelationalAttachmentFabric carrier)
    (kind : Transport.TransitionKind)
    (before after : Fibre.ReasoningFibrePoint carrier) : Set₁ where
  constructor attachedGovernedStep
  field
    governedTransport : Transport.GovernedFibreTransport kind before after
    beforeAttachments : Fibre.LocalReasoningAttachmentReceipt fabric before
    afterAttachments : Fibre.LocalReasoningAttachmentReceipt fabric after
    stepReference : String

open AttachedGovernedStep public

data GovernedTransportPath
    {carrier : Fibre.HistoryTimeArtifactCarrier}
    (fabric : Fibre.RelationalAttachmentFabric carrier) :
    Fibre.ReasoningFibrePoint carrier →
    Fibre.ReasoningFibrePoint carrier → Set₁ where
  pathRefl :
    ∀ {point} →
    Fibre.LocalReasoningAttachmentReceipt fabric point →
    GovernedTransportPath fabric point point
  pathStep :
    ∀ {before middle after kind} →
    AttachedGovernedStep fabric kind before middle →
    GovernedTransportPath fabric middle after →
    GovernedTransportPath fabric before after

------------------------------------------------------------------------
-- Composition is structural append.  The middle point is not discarded: it
-- remains present as the endpoint of the left path and start of the right path.
------------------------------------------------------------------------

appendTransportPath :
  ∀ {carrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    {a b c : Fibre.ReasoningFibrePoint carrier} →
  GovernedTransportPath fabric a b →
  GovernedTransportPath fabric b c →
  GovernedTransportPath fabric a c
appendTransportPath (pathRefl _) right = right
appendTransportPath (pathStep step rest) right =
  pathStep step (appendTransportPath rest right)

------------------------------------------------------------------------
-- Every point on the path is proof-relevantly retained.
------------------------------------------------------------------------

data PointOccursOnPath
    {carrier : Fibre.HistoryTimeArtifactCarrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    (point : Fibre.ReasoningFibrePoint carrier) :
    ∀ {start finish} →
    GovernedTransportPath fabric start finish → Set₁ where
  occursAtStart :
    ∀ {finish}
      {path : GovernedTransportPath fabric point finish} →
    PointOccursOnPath point path
  occursLater :
    ∀ {start middle finish kind}
      {step : AttachedGovernedStep fabric kind start middle}
      {rest : GovernedTransportPath fabric middle finish} →
    PointOccursOnPath point rest →
    PointOccursOnPath point (pathStep step rest)

middlePointRetained :
  ∀ {carrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    {before middle after kind}
    (step : AttachedGovernedStep fabric kind before middle)
    (rest : GovernedTransportPath fabric middle after) →
  PointOccursOnPath middle (pathStep step rest)
middlePointRetained step rest = occursLater occursAtStart

occurrenceSurvivesPathPrefix :
  ∀ {carrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    {point a b c : Fibre.ReasoningFibrePoint carrier}
    {left : GovernedTransportPath fabric a b}
    {right : GovernedTransportPath fabric b c} →
  PointOccursOnPath point left →
  PointOccursOnPath point (appendTransportPath left right)
occurrenceSurvivesPathPrefix {left = pathRefl receipt} occursAtStart = occursAtStart
occurrenceSurvivesPathPrefix {left = pathStep step rest} occursAtStart = occursAtStart
occurrenceSurvivesPathPrefix {left = pathStep step rest} (occursLater occurrence) =
  occursLater (occurrenceSurvivesPathPrefix occurrence)

------------------------------------------------------------------------
-- Coordinate preservation composes only when every step freezes that
-- coordinate.  This is the path-level form of least-privilege transport.
------------------------------------------------------------------------

data CoordinateFrozenAlong
    {carrier : Fibre.HistoryTimeArtifactCarrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    (coordinate : Transport.Coordinate) :
    ∀ {start finish} →
    GovernedTransportPath fabric start finish → Set₁ where
  frozenRefl :
    ∀ {point receipt} →
    CoordinateFrozenAlong coordinate (pathRefl {point = point} receipt)
  frozenStep :
    ∀ {before middle after kind}
      {step : AttachedGovernedStep fabric kind before middle}
      {rest : GovernedTransportPath fabric middle after} →
    (Transport.MayChange kind coordinate → ⊥) →
    CoordinateFrozenAlong coordinate rest →
    CoordinateFrozenAlong coordinate (pathStep step rest)

frozenCoordinatePreservedAcrossPath :
  ∀ {carrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    {coordinate : Transport.Coordinate}
    {start finish : Fibre.ReasoningFibrePoint carrier}
    {path : GovernedTransportPath fabric start finish} →
  CoordinateFrozenAlong coordinate path →
  Transport.coordinateValue coordinate finish
    ≡ Transport.coordinateValue coordinate start
frozenCoordinatePreservedAcrossPath frozenRefl = refl
frozenCoordinatePreservedAcrossPath
  (frozenStep blocked frozenRest) =
  trans
    (frozenCoordinatePreservedAcrossPath frozenRest)
    (Transport.preservesOutsideDeclaredChange
      (governedTransport _)
      _
      blocked)

------------------------------------------------------------------------
-- Attachment receipts are recoverable at both endpoints and every step.
------------------------------------------------------------------------

initialAttachmentReceipt :
  ∀ {carrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    {start finish : Fibre.ReasoningFibrePoint carrier} →
  GovernedTransportPath fabric start finish →
  Fibre.LocalReasoningAttachmentReceipt fabric start
initialAttachmentReceipt (pathRefl receipt) = receipt
initialAttachmentReceipt (pathStep step rest) = beforeAttachments step

terminalAttachmentReceipt :
  ∀ {carrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    {start finish : Fibre.ReasoningFibrePoint carrier} →
  GovernedTransportPath fabric start finish →
  Fibre.LocalReasoningAttachmentReceipt fabric finish
terminalAttachmentReceipt (pathRefl receipt) = receipt
terminalAttachmentReceipt (pathStep step rest) = terminalAttachmentReceipt rest

------------------------------------------------------------------------
-- Hard boundary.
------------------------------------------------------------------------

record TransportPathBoundary : Set where
  constructor transportPathBoundary
  field
    compositionErasesIntermediatePoints : Bool
    compositionErasesIntermediatePointsIsFalse :
      compositionErasesIntermediatePoints ≡ false
    everyStepRetainsAttachmentReceipts : Bool
    everyStepRetainsAttachmentReceiptsIsTrue :
      everyStepRetainsAttachmentReceipts ≡ true
    endpointEqualityAloneDefinesPathHistory : Bool
    endpointEqualityAloneDefinesPathHistoryIsFalse :
      endpointEqualityAloneDefinesPathHistory ≡ false
    oneChangingStepStillCountsAsFrozenCoordinatePath : Bool
    oneChangingStepStillCountsAsFrozenCoordinatePathIsFalse :
      oneChangingStepStillCountsAsFrozenCoordinatePath ≡ false
    pathCompositionPreservesProofRelevantRoute : Bool
    pathCompositionPreservesProofRelevantRouteIsTrue :
      pathCompositionPreservesProofRelevantRoute ≡ true

canonicalTransportPathBoundary : TransportPathBoundary
canonicalTransportPathBoundary =
  transportPathBoundary
    false refl
    true refl
    false refl
    false refl
    true refl
