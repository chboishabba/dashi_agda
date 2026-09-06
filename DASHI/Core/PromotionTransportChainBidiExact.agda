module DASHI.Core.PromotionTransportChainBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.SourceExactFrontierBidiCrossPollination2026 as SourceFrontier

------------------------------------------------------------------------
-- PROMOTION TRANSPORT CHAIN
--
-- Reverse x-pollination from Lean Integration.Kernel.PromotionTransport.
-- The Agda reconstruction keeps four obligations distinct:
--
--   artefact exists
--   -> corresponds to the intended statement
--   -> transport is sound for the target
--   -> target is actually inhabited.
--
-- SourceExactFrontier already separates external kernel/certificate carriers
-- from Agda proof terms; this file sharpens that into a staged transport frame.
------------------------------------------------------------------------

record PromotionTransportFrame
    (Artifact Statement Target : Set) : Set₁ where
  constructor promotion-transport-frame
  field
    ArtifactExists : Artifact → Set
    Corresponds : Artifact → Statement → Set
    TransportSound : Artifact → Statement → Target → Set
    TargetInhabits : Target → Set
    frameReference : String

open PromotionTransportFrame public

record PreInhabitanceReceipt
    {Artifact Statement Target : Set}
    (frame : PromotionTransportFrame Artifact Statement Target)
    (artifact : Artifact)
    (statement : Statement)
    (target : Target) : Set where
  constructor pre-inhabitance-receipt
  field
    artifactExists : ArtifactExists frame artifact
    corresponds : Corresponds frame artifact statement
    transportSound : TransportSound frame artifact statement target

open PreInhabitanceReceipt public

record FullPromotionReceipt
    {Artifact Statement Target : Set}
    (frame : PromotionTransportFrame Artifact Statement Target)
    (artifact : Artifact)
    (statement : Statement)
    (target : Target) : Set where
  constructor full-promotion-receipt
  field
    pre : PreInhabitanceReceipt frame artifact statement target
    targetInhabits : TargetInhabits frame target

open FullPromotionReceipt public

fullPromotionCarriesPreInhabitance :
  ∀ {Artifact Statement Target : Set}
    {frame : PromotionTransportFrame Artifact Statement Target}
    {artifact : Artifact} {statement : Statement} {target : Target} →
  FullPromotionReceipt frame artifact statement target →
  PreInhabitanceReceipt frame artifact statement target
fullPromotionCarriesPreInhabitance = pre

------------------------------------------------------------------------
-- Exact three-of-four countermodel.
------------------------------------------------------------------------

data ToyArtifact : Set where externalReceipt : ToyArtifact
data ToyStatement : Set where intendedStatement : ToyStatement
data ToyTarget : Set where agdaTarget : ToyTarget

toyFrame : PromotionTransportFrame ToyArtifact ToyStatement ToyTarget
toyFrame = promotion-transport-frame
  (λ _ → ⊤)
  (λ _ _ → ⊤)
  (λ _ _ _ → ⊤)
  (λ _ → ⊥)
  "artifact/correspondence/transport all present while target inhabitance remains empty"

toyPreInhabitance :
  PreInhabitanceReceipt toyFrame externalReceipt intendedStatement agdaTarget
toyPreInhabitance = pre-inhabitance-receipt tt tt tt

toyThreeEarlierObligationsDoNotCreateTargetInhabitance :
  FullPromotionReceipt toyFrame externalReceipt intendedStatement agdaTarget → ⊥
toyThreeEarlierObligationsDoNotCreateTargetInhabitance full = targetInhabits full

------------------------------------------------------------------------
-- The frontier's external verification carriers therefore remain inputs to a
-- transport problem, not substitutes for its final inhabitance coordinate.
------------------------------------------------------------------------

sourceFrontierExternalReceiptIsNotAgdaProof :
  SourceFrontier.externalKernelReceipt ≡ SourceFrontier.agdaProofTerm → ⊥
sourceFrontierExternalReceiptIsNotAgdaProof = SourceFrontier.externalKernelNotAgdaProof

record PromotionTransportBoundary : Set where
  constructor promotion-transport-boundary
  field
    artefactExistenceIsStatementCorrespondence : Bool
    statementCorrespondenceIsTransportSoundness : Bool
    transportSoundnessIsTargetInhabitance : Bool
    allFourCoordinatesRequiredForFullReceipt : Bool

canonicalPromotionTransportBoundary : PromotionTransportBoundary
canonicalPromotionTransportBoundary =
  promotion-transport-boundary false false false true
