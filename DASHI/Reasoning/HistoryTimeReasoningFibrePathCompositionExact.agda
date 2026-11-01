module DASHI.Reasoning.HistoryTimeReasoningFibrePathCompositionExact where

open import DASHI.Core.Prelude

import DASHI.Reasoning.HistoryTimeRelationalReasoningFibreExact as Fibre
import DASHI.Reasoning.HistoryTimeReasoningFibreTransportExact as Transport
import DASHI.Reasoning.HistoryTimeReasoningFibreTransportPathExact as Path

------------------------------------------------------------------------
-- PATH COMPOSITION RECEIPTS
--
-- Path append composes not only routes but also least-privilege preservation
-- certificates.  A coordinate is frozen across a composite path exactly when
-- each constituent path supplies a frozen-coordinate receipt.
------------------------------------------------------------------------

coordinateFrozenAlongAppend :
  ∀ {carrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    {coordinate : Transport.Coordinate}
    {a b c : Fibre.ReasoningFibrePoint carrier}
    {left : Path.GovernedTransportPath fabric a b}
    {right : Path.GovernedTransportPath fabric b c} →
  Path.CoordinateFrozenAlong coordinate left →
  Path.CoordinateFrozenAlong coordinate right →
  Path.CoordinateFrozenAlong coordinate (Path.appendTransportPath left right)
coordinateFrozenAlongAppend Path.frozenRefl rightFrozen = rightFrozen
coordinateFrozenAlongAppend (Path.frozenStep blocked restFrozen) rightFrozen =
  Path.frozenStep blocked (coordinateFrozenAlongAppend restFrozen rightFrozen)

compositeFrozenCoordinatePreserved :
  ∀ {carrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    {coordinate : Transport.Coordinate}
    {a b c : Fibre.ReasoningFibrePoint carrier}
    {left : Path.GovernedTransportPath fabric a b}
    {right : Path.GovernedTransportPath fabric b c} →
  Path.CoordinateFrozenAlong coordinate left →
  Path.CoordinateFrozenAlong coordinate right →
  Transport.coordinateValue coordinate c ≡
  Transport.coordinateValue coordinate a
compositeFrozenCoordinatePreserved leftFrozen rightFrozen =
  Path.frozenCoordinatePreservedAcrossPath
    (coordinateFrozenAlongAppend leftFrozen rightFrozen)

------------------------------------------------------------------------
-- Concrete high-value route: source correction followed by semantic
-- refinement cannot silently change the consumer coordinate at either step.
------------------------------------------------------------------------

sourceThenSemanticConsumerFrozen :
  ∀ {carrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    {p0 p1 p2 : Fibre.ReasoningFibrePoint carrier}
    (sourceStep :
      Path.AttachedGovernedStep fabric Transport.sourceCorrection p0 p1)
    (semanticStep :
      Path.AttachedGovernedStep fabric Transport.semanticRefinement p1 p2)
    (terminalReceipt : Fibre.LocalReasoningAttachmentReceipt fabric p2) →
  Path.CoordinateFrozenAlong Transport.consumerCoordinate
    (Path.pathStep sourceStep
      (Path.pathStep semanticStep
        (Path.pathRefl terminalReceipt)))
sourceThenSemanticConsumerFrozen sourceStep semanticStep terminalReceipt =
  Path.frozenStep (λ ())
    (Path.frozenStep (λ ()) Path.frozenRefl)

sourceThenSemanticCannotRewriteConsumer :
  ∀ {carrier}
    {fabric : Fibre.RelationalAttachmentFabric carrier}
    {p0 p1 p2 : Fibre.ReasoningFibrePoint carrier}
    (sourceStep :
      Path.AttachedGovernedStep fabric Transport.sourceCorrection p0 p1)
    (semanticStep :
      Path.AttachedGovernedStep fabric Transport.semanticRefinement p1 p2)
    (terminalReceipt : Fibre.LocalReasoningAttachmentReceipt fabric p2) →
  Fibre.consumerState p2 ≡ Fibre.consumerState p0
sourceThenSemanticCannotRewriteConsumer sourceStep semanticStep terminalReceipt =
  Path.frozenCoordinatePreservedAcrossPath
    (sourceThenSemanticConsumerFrozen sourceStep semanticStep terminalReceipt)

------------------------------------------------------------------------
-- Conversely, appending an authorised consumer-revision step does not permit
-- us to manufacture a frozen-consumer certificate for the whole path: there
-- is no inhabitant of MayChange consumerRevision consumerCoordinate -> bottom.
------------------------------------------------------------------------

consumerRevisionAllowsConsumerChange :
  Transport.MayChange
    Transport.consumerRevision
    Transport.consumerCoordinate
consumerRevisionAllowsConsumerChange = Transport.consumerMayChange

record PathCompositionBoundary : Set where
  constructor pathCompositionBoundary
  field
    preservationReceiptsCompose : Bool
    preservationReceiptsComposeIsTrue : preservationReceiptsCompose ≡ true
    sourceThenSemanticMayRewriteConsumer : Bool
    sourceThenSemanticMayRewriteConsumerIsFalse :
      sourceThenSemanticMayRewriteConsumer ≡ false
    consumerRevisionIsFalselyClassifiedAsConsumerFrozen : Bool
    consumerRevisionIsFalselyClassifiedAsConsumerFrozenIsFalse :
      consumerRevisionIsFalselyClassifiedAsConsumerFrozen ≡ false
    compositePathRetainsStepwiseAuthority : Bool
    compositePathRetainsStepwiseAuthorityIsTrue :
      compositePathRetainsStepwiseAuthority ≡ true

canonicalPathCompositionBoundary : PathCompositionBoundary
canonicalPathCompositionBoundary =
  pathCompositionBoundary
    true refl
    false refl
    false refl
    true refl
