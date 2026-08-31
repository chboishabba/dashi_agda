module DASHI.Core.BidiResidualLineageCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.ContextGovernedLineageTransportExact as Lineage

------------------------------------------------------------------------
-- Residual narrowing and provenance-lineage transport are orthogonal axes.
-- A value/state fibre can shrink while a coordinate is preserved, erased or
-- reintroduced; narrowing therefore does not by itself certify provenance.
------------------------------------------------------------------------

record BidiRefinementWithLineage
    {Hidden Context Coordinate : Set}
    (family : Lineage.ContextCoordinateLineage Context Coordinate)
    (source target : Context)
    (prior posterior : Bidi.ResidualFibre Hidden) : Set₁ where
  constructor bidiRefinementWithLineage
  field
    fibreRefinement : Bidi.FibreRefines posterior prior
    lineageTransport : Lineage.LineageTransportReceipt family source target
    residualDerivationReference : String
    lineageAuthorityReference : String
    consumerReference : String

open BidiRefinementWithLineage public

attachIndependentLineageTransport :
  ∀ {Hidden Context Coordinate}
    {family : Lineage.ContextCoordinateLineage Context Coordinate}
    {source target : Context}
    {prior posterior : Bidi.ResidualFibre Hidden} →
  Bidi.FibreRefines posterior prior →
  Lineage.LineageTransportReceipt family source target →
  String → String → String →
  BidiRefinementWithLineage family source target prior posterior
attachIndependentLineageTransport refinement transport residualRef lineageRef consumerRef =
  bidiRefinementWithLineage
    refinement transport residualRef lineageRef consumerRef

refinementPartRemainsAvailable :
  ∀ {Hidden Context Coordinate}
    {family : Lineage.ContextCoordinateLineage Context Coordinate}
    {source target : Context}
    {prior posterior : Bidi.ResidualFibre Hidden} →
  BidiRefinementWithLineage family source target prior posterior →
  Bidi.FibreRefines posterior prior
refinementPartRemainsAvailable receipt = fibreRefinement receipt

lineagePartRemainsIndependent :
  ∀ {Hidden Context Coordinate}
    {family : Lineage.ContextCoordinateLineage Context Coordinate}
    {source target : Context}
    {prior posterior : Bidi.ResidualFibre Hidden} →
  BidiRefinementWithLineage family source target prior posterior →
  Lineage.LineageTransportReceipt family source target
lineagePartRemainsIndependent receipt = lineageTransport receipt

record BidiResidualLineageBoundary : Set where
  constructor bidiResidualLineageBoundary
  field
    narrowerValueFibreAutomaticallyPreservesLineage : Bool
    narrowerValueFibreAutomaticallyPreservesLineageIsFalse :
      narrowerValueFibreAutomaticallyPreservesLineage ≡ false
    safeConsumerApproximationAutomaticallyRestoresLineage : Bool
    safeConsumerApproximationAutomaticallyRestoresLineageIsFalse :
      safeConsumerApproximationAutomaticallyRestoresLineage ≡ false
    fibreRefinementAndLineageTransportCanBeCertifiedSeparately : Bool
    fibreRefinementAndLineageTransportCanBeCertifiedSeparatelyIsTrue :
      fibreRefinementAndLineageTransportCanBeCertifiedSeparately ≡ true
    provenanceLossMakesAllResidualRefinementInvalid : Bool
    provenanceLossMakesAllResidualRefinementInvalidIsFalse :
      provenanceLossMakesAllResidualRefinementInvalid ≡ false

canonicalBidiResidualLineageBoundary : BidiResidualLineageBoundary
canonicalBidiResidualLineageBoundary =
  bidiResidualLineageBoundary false refl false refl true refl false refl
