module Ontology.BrainDNA.PacketCodecBridge where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Vec using (Vec; map)

open import Ontology.DNA.Supervoxel4Adic using
  (Base; A; C; G; T; FlatDNA256)
open import Ontology.DNA.EigenclassSurface using (ScanOrder; lineMajor)
open import Ontology.DNA.StreamingEncoderSurface using
  (EncoderState; stateOf; stepAdmissible; streamingEncoderSurface;
   StreamingEncoderSurface)
open import Ontology.DNA.ChannelCodingSurface using
  (IntegratedChannelSurface; integratedChannelSurface;
   genericAdmissibilityFlag)
open import Ontology.DNA.SupervoxelAdmissibility using
  (Supervoxel256; supervoxel256; admissibleSupervoxel;
   SupervoxelAdmissibilitySurface; supervoxelAdmissibilitySurface)

------------------------------------------------------------------------
-- Minimal brain-DNA crossover owner surface.
-- This is intentionally narrow: a line-major brain-side packet boundary with
-- a direct token-to-base map and theorem-thin attachments to the existing
-- DNA streaming/channel/admissibility surfaces.

data BrainToken : Set where
  quiet edge core burst : BrainToken

encodeToken : BrainToken → Base
encodeToken quiet = A
encodeToken edge = C
encodeToken core = G
encodeToken burst = T

record BrainPacket (n : Nat) : Set where
  constructor brainPacket
  field
    tokens : Vec BrainToken n

packetScanOrder : ∀ {n} → BrainPacket n → ScanOrder
packetScanOrder _ = lineMajor

encodePacket : ∀ {n} → BrainPacket n → Vec Base n
encodePacket pkt = map encodeToken (BrainPacket.tokens pkt)

packetState : ∀ {n} → BrainPacket n → EncoderState n
packetState pkt = stateOf (encodePacket pkt)

packetAdmissibility : ∀ {n} → BrainPacket n → Bool
packetAdmissibility pkt = genericAdmissibilityFlag (encodePacket pkt)

packetAdmissibleNext : ∀ {n} → BrainPacket n → BrainToken → Bool
packetAdmissibleNext pkt tok = stepAdmissible (packetState pkt) (encodeToken tok)

packetEmit : ∀ {n} → BrainPacket n → Σ Nat (λ m → Vec Base m)
packetEmit pkt = IntegratedChannelSurface.emit integratedChannelSurface (encodePacket pkt)

packetScanOrder-lineMajor :
  ∀ {n} (pkt : BrainPacket n) →
  packetScanOrder pkt ≡ lineMajor
packetScanOrder-lineMajor pkt = refl

packetEmit-identity :
  ∀ {n} (pkt : BrainPacket n) →
  packetEmit pkt ≡ (n , encodePacket pkt)
packetEmit-identity pkt = refl

packetAdmissibility-consistent :
  ∀ {n} (pkt : BrainPacket n) →
  packetAdmissibility pkt ≡ genericAdmissibilityFlag (encodePacket pkt)
packetAdmissibility-consistent pkt = refl

record BrainPacketPair256 : Set where
  constructor brainPacketPair256
  field
    leftPacket : BrainPacket 256
    rightPacket : BrainPacket 256

encodePacketPair256 : BrainPacketPair256 → Supervoxel256
encodePacketPair256 pair =
  supervoxel256
    (encodePacket (BrainPacketPair256.leftPacket pair))
    (encodePacket (BrainPacketPair256.rightPacket pair))

pairAdmissibility : BrainPacketPair256 → Bool
pairAdmissibility pair = admissibleSupervoxel (encodePacketPair256 pair)

pairAdmissibility-consistent :
  (pair : BrainPacketPair256) →
  pairAdmissibility pair
    ≡
  SupervoxelAdmissibilitySurface.localAdmissible
    supervoxelAdmissibilitySurface
    (encodePacketPair256 pair)
pairAdmissibility-consistent pair = refl

record BrainDNACrossoverSurface : Set₁ where
  field
    Packet : Nat → Set
    packetOrder : ∀ {n} → Packet n → ScanOrder
    encode : ∀ {n} → Packet n → Vec Base n
    streamingBoundary : StreamingEncoderSurface
    channelBoundary : IntegratedChannelSurface
    admissibilityBoundary : ∀ {n} → Packet n → Bool
    emitBoundary : ∀ {n} → Packet n → Σ Nat (λ m → Vec Base m)
    PairedPacket : Set
    pairedEncode : PairedPacket → Supervoxel256
    pairedAdmissibilityBoundary : PairedPacket → Bool

brainDNACrossoverSurface : BrainDNACrossoverSurface
brainDNACrossoverSurface = record
  { Packet = BrainPacket
  ; packetOrder = packetScanOrder
  ; encode = encodePacket
  ; streamingBoundary = streamingEncoderSurface
  ; channelBoundary = integratedChannelSurface
  ; admissibilityBoundary = packetAdmissibility
  ; emitBoundary = packetEmit
  ; PairedPacket = BrainPacketPair256
  ; pairedEncode = encodePacketPair256
  ; pairedAdmissibilityBoundary = pairAdmissibility
  }
