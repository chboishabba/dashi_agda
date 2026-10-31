{-# OPTIONS --safe #-}
module DASHI.Reasoning.FederatedExpertTransportBidiExact where

-- Finite producer/consumer transport semantics. We do not formalize
-- DEFLATE, cryptography, hashes or network latency in this module.
-- Existing sibling owners: TriadicVideoCodecObservationQuotient;
-- DistributedEpistemicPlaneSeparationExact; IEEEOrbitSignWitnessBidiExact.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

data Codec : Set where
  raw zlib signOrbit : Codec

record ExpertWire : Set where
  constructor wire
  field
    modelRevision : String
    historyRevision : String
    selectedExperts : List Nat
    orientationWitness : List Bool
    codec : Codec
    payload : List Bool
open ExpertWire public

-- Receive only when both model and history agree. The successful
-- branch carries the same payload and routing witness without loss.
data Receive (A : Set) : Set where
  reject : Receive A
  accept : A → Receive A

choose : Bool → Bool → ExpertWire → Receive ExpertWire
choose false _ packet = reject
choose true false packet = reject
choose true true packet = accept packet

correctReferenceBidi : (packet : ExpertWire) →
  choose true true packet ≡ accept packet
correctReferenceBidi packet = refl

staleModelRejects : (packet : ExpertWire) →
  choose false true packet ≡ reject
staleModelRejects packet = refl

staleHistoryRejects : (packet : ExpertWire) →
  choose true false packet ≡ reject
staleHistoryRejects packet = refl

-- This symbolic contract deliberately does not claim a real string
-- equality algorithm, authenticated encryption, hash validation,
-- remote history synchronization or bitwise Python correspondence.


------------------------------------------------------------------------
-- Pareto decision contract: an encoding may be smaller in bytes yet
-- slower after encoder and decoder costs. A network oracle is explicit.
-- Natural time units are abstract calibrated costs, not WAN benchmarks.
------------------------------------------------------------------------

record CandidateCost : Set where
  constructor candidateCost
  field
    encoderTime : Nat
    wireTime : Nat
    decoderTime : Nat
open CandidateCost public

totalTime : CandidateCost → Nat
totalTime c = encoderTime c + wireTime c + decoderTime c

-- Returning the chosen candidate and its exact receipt is required:
-- the receiver must not infer a codec from time or size alone.
record Candidate : Set where
  constructor candidate
  field
    packet : ExpertWire
    cost : CandidateCost
open Candidate public

-- A real comparator/argmin is not assumed: a supplied selector must
-- carry an admissibility certificate for its choice. This lets latency
-- be an objective without claiming compression is intrinsically faster.
record Admission (proposal : Candidate) : Set where
  field
    acceptedCodec : Codec
    exactCodecWitness : acceptedCodec ≡ codec (packet proposal)
    acceptedModel : String
    exactModelWitness : acceptedModel ≡ modelRevision (packet proposal)
    acceptedHistory : String
    exactHistoryWitness : acceptedHistory ≡ historyRevision (packet proposal)
open Admission public

costDecomposition : (candidate : Candidate) →
  totalTime (cost candidate) ≡
  encoderTime (cost candidate) + wireTime (cost candidate) +
  decoderTime (cost candidate)
costDecomposition c = refl
