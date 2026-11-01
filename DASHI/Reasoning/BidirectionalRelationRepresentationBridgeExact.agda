module DASHI.Reasoning.BidirectionalRelationRepresentationBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.StructuralMetaphorTaskCompressionExact as Compression
import DASHI.Reasoning.RelationRepresentationAdequacyExact as Adequacy
import DASHI.Reasoning.RelationRepresentationRealizationExact as Realization

------------------------------------------------------------------------
-- BIDIRECTIONAL BRIDGE CUT
--
-- "Bidirectional" here is a proof-construction discipline, not an assertion
-- that the representation and target are inverse/isomorphic carriers.
--
-- Forward side:
--   fine state -> representation -> declared task output.
--
-- Backward side:
--   declared target phenomenon -> required realization decoder through the
--   same representation.
--
-- The bridge closes only when both receipts inhabit the same encoding.  A
-- richer-consumer collision reopens the cut and blocks closure through that
-- representation.
------------------------------------------------------------------------

record BidirectionalRelationBridge
    (Fine Representation Task Output Target : Set)
    (encode : Fine → Representation)
    (evaluate : Task → Fine → Output)
    (targetPhenomenon : Fine → Target) : Set₁ where
  constructor bidirectionalRelationBridge
  field
    forwardAdequacy :
      Adequacy.StaticRelationAdequacy
        Fine Representation Task Output encode evaluate
    backwardRealization :
      Realization.RepresentationRealizationWitness encode targetPhenomenon
    bridgeReading : String

open BidirectionalRelationBridge public

forwardConsumerFactors :
  ∀ {Fine Representation Task Output Target : Set}
    {encode : Fine → Representation}
    {evaluate : Task → Fine → Output}
    {targetPhenomenon : Fine → Target} →
  BidirectionalRelationBridge
    Fine Representation Task Output Target
    encode evaluate targetPhenomenon →
  Compression.TaskRelativeStructuralCompression
    Fine Representation Task Output encode evaluate
forwardConsumerFactors bridge =
  Adequacy.compression (forwardAdequacy bridge)

backwardTargetFactors :
  ∀ {Fine Representation Task Output Target : Set}
    {encode : Fine → Representation}
    {evaluate : Task → Fine → Output}
    {targetPhenomenon : Fine → Target} →
  BidirectionalRelationBridge
    Fine Representation Task Output Target
    encode evaluate targetPhenomenon →
  Realization.RepresentationRealizationWitness encode targetPhenomenon
backwardTargetFactors = backwardRealization

------------------------------------------------------------------------
-- If the backward consumer supplies a collision, no bridge through that same
-- representation can close, regardless of success on the forward task.
------------------------------------------------------------------------

collisionReopensBidirectionalCut :
  ∀ {Fine Representation Task Output Target : Set}
    {encode : Fine → Representation}
    {evaluate : Task → Fine → Output}
    {targetPhenomenon : Fine → Target} →
  Compression.CompressionFailureWitness encode targetPhenomenon →
  BidirectionalRelationBridge
    Fine Representation Task Output Target
    encode evaluate targetPhenomenon →
  ⊥
collisionReopensBidirectionalCut collision bridge =
  Realization.representationCollisionBlocksRealization
    collision
    (backwardRealization bridge)

------------------------------------------------------------------------
-- A failed cut should be refined/reopened, not repaired by relabelling a
-- representation that has already erased the required distinction.
------------------------------------------------------------------------

data FailedCutCanBeRepairedByPostprocessingPermission : Set where

data BidirectionalBridgeImpliesRepresentationTargetIsomorphismPermission : Set where

failedCutCannotAutoRepairByPostprocessing :
  FailedCutCanBeRepairedByPostprocessingPermission → ⊥
failedCutCannotAutoRepairByPostprocessing ()

bridgeDoesNotAutoPromoteToIsomorphism :
  BidirectionalBridgeImpliesRepresentationTargetIsomorphismPermission → ⊥
bridgeDoesNotAutoPromoteToIsomorphism ()

record BidirectionalRelationBridgeBoundary : Set where
  constructor bidirectionalRelationBridgeBoundary
  field
    forwardTaskFitAloneClosesBridge : Bool
    forwardTaskFitAloneClosesBridgeIsFalse :
      forwardTaskFitAloneClosesBridge ≡ false

    backwardTargetRequirementAloneSelectsRepresentation : Bool
    backwardTargetRequirementAloneSelectsRepresentationIsFalse :
      backwardTargetRequirementAloneSelectsRepresentation ≡ false

    bothReceiptsMustUseSameEncoding : Bool
    bothReceiptsMustUseSameEncodingIsTrue :
      bothReceiptsMustUseSameEncoding ≡ true

    closedBridgeImpliesCarrierIsomorphism : Bool
    closedBridgeImpliesCarrierIsomorphismIsFalse :
      closedBridgeImpliesCarrierIsomorphism ≡ false

canonicalBidirectionalRelationBridgeBoundary : BidirectionalRelationBridgeBoundary
canonicalBidirectionalRelationBridgeBoundary =
  bidirectionalRelationBridgeBoundary
    false refl
    false refl
    true refl
    false refl
