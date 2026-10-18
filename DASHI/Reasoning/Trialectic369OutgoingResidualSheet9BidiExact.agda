module DASHI.Reasoning.Trialectic369OutgoingResidualSheet9BidiExact where

------------------------------------------------------------------------
-- OUTGOING NINE RESIDUAL <-> CANONICAL TRIADIC CODEC SHEET9
--
-- DASHI CONTRIBUTION
--
-- The participant-centered quotient retains the outgoing observer pair as
-- TriadicKernelLiftQuotientExact.NineSheet.  The canonical triadic codec
-- already owns Sheet9 = Kernel 2 over DASHI.Algebra.Trit.
--
-- This module closes the carrier seam exactly and upgrades
--
--   PhaseOrbit15 x NineSheet
--
-- to
--
--   PhaseOrbit15 x Codec.Sheet9.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Algebra.Trit as Trit
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.Trialectic369ParticipantCenteredSSPFactorExact as Centered
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Reduction

open Codec using ([]ᵥ; _∷ᵥ_)

------------------------------------------------------------------------
-- 1. Exact coordinate conversion.
------------------------------------------------------------------------

kernelTritToCodecTrit :
  Triadic.KernelTrit ->
  Trit.Trit
kernelTritToCodecTrit trit =
  SSP.toTrit (Reduction.kernelToSSPTrit trit)

codecTritToKernelTrit :
  Trit.Trit ->
  Triadic.KernelTrit
codecTritToKernelTrit trit =
  Reduction.sspToKernelTrit (SSP.fromTrit trit)

kernelCodecTritRoundTrip :
  (trit : Triadic.KernelTrit) ->
  codecTritToKernelTrit (kernelTritToCodecTrit trit)
  ≡ trit
kernelCodecTritRoundTrip trit
  rewrite SSP.fromTrit-toTrit (Reduction.kernelToSSPTrit trit)
        | Reduction.kernelSSPRoundTrip trit = refl

codecKernelTritRoundTrip :
  (trit : Trit.Trit) ->
  kernelTritToCodecTrit (codecTritToKernelTrit trit)
  ≡ trit
codecKernelTritRoundTrip trit
  rewrite Reduction.sspKernelRoundTrip (SSP.fromTrit trit)
        | SSP.toTrit-fromTrit trit = refl

------------------------------------------------------------------------
-- 2. Exact NineSheet <-> Codec.Sheet9.
------------------------------------------------------------------------

nineSheetToCodecSheet9 :
  Triadic.NineSheet ->
  Codec.Sheet9
nineSheetToCodecSheet9 (left , right) =
  kernelTritToCodecTrit left
  ∷ᵥ kernelTritToCodecTrit right
  ∷ᵥ []ᵥ

codecSheet9ToNineSheet :
  Codec.Sheet9 ->
  Triadic.NineSheet
codecSheet9ToNineSheet
  (left ∷ᵥ right ∷ᵥ []ᵥ) =
  codecTritToKernelTrit left
  , codecTritToKernelTrit right

nineCodecSheet9RoundTrip :
  (sheet : Triadic.NineSheet) ->
  codecSheet9ToNineSheet (nineSheetToCodecSheet9 sheet)
  ≡ sheet
nineCodecSheet9RoundTrip (left , right)
  rewrite kernelCodecTritRoundTrip left
        | kernelCodecTritRoundTrip right = refl

codecNineSheet9RoundTrip :
  (sheet : Codec.Sheet9) ->
  nineSheetToCodecSheet9 (codecSheet9ToNineSheet sheet)
  ≡ sheet
codecNineSheet9RoundTrip
  (left ∷ᵥ right ∷ᵥ []ᵥ)
  rewrite codecKernelTritRoundTrip left
        | codecKernelTritRoundTrip right = refl

------------------------------------------------------------------------
-- 3. Rechart the participant-centered quotient target canonically.
------------------------------------------------------------------------

PhaseOrbitWithCodecSheet9 : Set
PhaseOrbitWithCodecSheet9 =
  Reduction.PhaseOrbit15 × Codec.Sheet9

phaseOrbitNineToCodec :
  Reduction.PhaseOrbit15 × Triadic.NineSheet ->
  PhaseOrbitWithCodecSheet9
phaseOrbitNineToCodec (phaseOrbit , residual) =
  phaseOrbit , nineSheetToCodecSheet9 residual

phaseOrbitCodecToNine :
  PhaseOrbitWithCodecSheet9 ->
  Reduction.PhaseOrbit15 × Triadic.NineSheet
phaseOrbitCodecToNine (phaseOrbit , residual) =
  phaseOrbit , codecSheet9ToNineSheet residual

phaseOrbitCodecRoundTrip :
  (state : Reduction.PhaseOrbit15 × Triadic.NineSheet) ->
  phaseOrbitCodecToNine (phaseOrbitNineToCodec state)
  ≡ state
phaseOrbitCodecRoundTrip (phaseOrbit , residual)
  rewrite nineCodecSheet9RoundTrip residual = refl

codecPhaseOrbitRoundTrip :
  (state : PhaseOrbitWithCodecSheet9) ->
  phaseOrbitNineToCodec (phaseOrbitCodecToNine state)
  ≡ state
codecPhaseOrbitRoundTrip (phaseOrbit , residual)
  rewrite codecNineSheet9RoundTrip residual = refl

participantCenteredCodecQuotient :
  Centered.CCenteredComplement ->
  PhaseOrbitWithCodecSheet9
participantCenteredCodecQuotient state =
  phaseOrbitNineToCodec
    (Centered.participantCenteredQuotient state)

canonicalLiftParticipantCenteredCodec :
  PhaseOrbitWithCodecSheet9 ->
  Centered.CCenteredComplement
canonicalLiftParticipantCenteredCodec state =
  Centered.canonicalLiftParticipantCentered
    (phaseOrbitCodecToNine state)

participantCenteredCodecSectionRoundTrip :
  (state : PhaseOrbitWithCodecSheet9) ->
  participantCenteredCodecQuotient
    (canonicalLiftParticipantCenteredCodec state)
  ≡ state
participantCenteredCodecSectionRoundTrip state
  rewrite Centered.participantCenteredQuotientLiftRoundTrip
            (phaseOrbitCodecToNine state)
        | codecPhaseOrbitRoundTrip state = refl

------------------------------------------------------------------------
-- 4. The residual is literally the outgoing pair.
------------------------------------------------------------------------

outgoingResidualCodecSheet9 :
  Centered.CCenteredComplement ->
  Codec.Sheet9
outgoingResidualCodecSheet9 state =
  nineSheetToCodecSheet9
    (Centered.outgoingFromC state)

------------------------------------------------------------------------
-- 5. Firewall.
------------------------------------------------------------------------

data CodecSheet9MayBeDiscardedAfterRecognition : Set where
data Sheet9RecognitionCreatesArithmeticNoiseInterpretation : Set where

codecSheet9NotDiscarded :
  CodecSheet9MayBeDiscardedAfterRecognition -> ⊥
codecSheet9NotDiscarded ()

sheet9NotPromotedToArithmeticNoise :
  Sheet9RecognitionCreatesArithmeticNoiseInterpretation -> ⊥
sheet9NotPromotedToArithmeticNoise ()

record Trialectic369OutgoingResidualSheet9BidiBoundary : Set where
  constructor trialectic-369-outgoing-residual-sheet9-bidi-boundary
  field
    kernelTritCodecTritBidiPaid : Bool
    nineSheetCodecSheet9BidiPaid : Bool
    phaseOrbitResidualUsesCanonicalSheet9 : Bool
    participantCenteredCodecSectionPaid : Bool
    outgoingPairIsCanonicalSheet9 : Bool
    residualDiscarded : Bool

canonicalTrialectic369OutgoingResidualSheet9BidiBoundary :
  Trialectic369OutgoingResidualSheet9BidiBoundary
canonicalTrialectic369OutgoingResidualSheet9BidiBoundary =
  trialectic-369-outgoing-residual-sheet9-bidi-boundary
    true true true true true false
