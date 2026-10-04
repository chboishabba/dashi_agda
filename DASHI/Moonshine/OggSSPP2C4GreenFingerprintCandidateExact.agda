module DASHI.Moonshine.OggSSPP2C4GreenFingerprintCandidateExact where

------------------------------------------------------------------------
-- p=2 C4 SOURCE-NATIVE GREEN FINGERPRINT FOR THE FIVE DEPTH CANDIDATES
--
-- EXTERNAL SOURCE INPUT
--
-- Carnahan--Urano Theorem 6.2 gives ring homomorphism values on the nine
-- indecomposable Z[C4]-modules.  Two of those source-native observables already
-- distinguish the five candidates selected upstream:
--
--                  rank      Tr(g)
--     A              1         +1
--     B              1         -1
--     C              2          0
--     C^A            3         +1
--     C^B            3         -1
--
-- The full source table also contains Tr(g^2) and total g^2-Tate dimension,
-- but they are not needed for injectivity on this five-element family.
--
-- DASHI RESULT
--
-- The pair (rank, Tr(g)) is an injective SOURCE-NATIVE fingerprint on
--
--     A, B, C, C^A, C^B.
--
-- Thus, once an actual 2B source piece is independently shown to lift to one
-- of these C4 candidate classes, its candidate label is recoverable without
-- reading the Monster residual, Base369, or the geometric inertia label.
--
-- FIREWALL
--
-- This does NOT prove:
--   * any of the five candidates actually occurs in the required 2B source;
--   * the fingerprint is the Co1 Brauer fingerprint of the direct 2B object;
--   * the five fingerprints are the five inertia sectors;
--   * rank equals localized DVR composition length.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSPP2C4LowRankDepthSpectrumCandidateExact as Spectrum
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source trace-at-g values needed on the five candidates.
------------------------------------------------------------------------

data C4TraceGValue : Set where
  tracePlusOne :
    C4TraceGValue
  traceMinusOne :
    C4TraceGValue
  traceZero :
    C4TraceGValue

candidateTraceG :
  Spectrum.P2C4DepthCandidate ->
  C4TraceGValue
candidateTraceG Spectrum.candidateA = tracePlusOne
candidateTraceG Spectrum.candidateB = traceMinusOne
candidateTraceG Spectrum.candidateC = traceZero
candidateTraceG Spectrum.candidateCA = tracePlusOne
candidateTraceG Spectrum.candidateCB = traceMinusOne

------------------------------------------------------------------------
-- 2. Rank/trace fingerprint.
------------------------------------------------------------------------

record C4RankTraceFingerprint : Set where
  constructor rank-trace-fingerprint
  field
    rank :
      Nat
    traceG :
      C4TraceGValue

open C4RankTraceFingerprint public

candidateFingerprint :
  Spectrum.P2C4DepthCandidate ->
  C4RankTraceFingerprint
candidateFingerprint candidate =
  rank-trace-fingerprint
    (Spectrum.candidateRank candidate)
    (candidateTraceG candidate)

candidateAFingerprint :
  candidateFingerprint Spectrum.candidateA
  ≡ rank-trace-fingerprint 1 tracePlusOne
candidateAFingerprint = refl

candidateBFingerprint :
  candidateFingerprint Spectrum.candidateB
  ≡ rank-trace-fingerprint 1 traceMinusOne
candidateBFingerprint = refl

candidateCFingerprint :
  candidateFingerprint Spectrum.candidateC
  ≡ rank-trace-fingerprint 2 traceZero
candidateCFingerprint = refl

candidateCAFingerprint :
  candidateFingerprint Spectrum.candidateCA
  ≡ rank-trace-fingerprint 3 tracePlusOne
candidateCAFingerprint = refl

candidateCBFingerprint :
  candidateFingerprint Spectrum.candidateCB
  ≡ rank-trace-fingerprint 3 traceMinusOne
candidateCBFingerprint = refl

------------------------------------------------------------------------
-- 3. Exact injectivity.
------------------------------------------------------------------------

candidateFingerprintInjective :
  {left right : Spectrum.P2C4DepthCandidate} ->
  candidateFingerprint left ≡ candidateFingerprint right ->
  left ≡ right
candidateFingerprintInjective
  {Spectrum.candidateA}
  {Spectrum.candidateA}
  same = refl
candidateFingerprintInjective
  {Spectrum.candidateA}
  {Spectrum.candidateB}
  ()
candidateFingerprintInjective
  {Spectrum.candidateA}
  {Spectrum.candidateC}
  ()
candidateFingerprintInjective
  {Spectrum.candidateA}
  {Spectrum.candidateCA}
  ()
candidateFingerprintInjective
  {Spectrum.candidateA}
  {Spectrum.candidateCB}
  ()

candidateFingerprintInjective
  {Spectrum.candidateB}
  {Spectrum.candidateA}
  ()
candidateFingerprintInjective
  {Spectrum.candidateB}
  {Spectrum.candidateB}
  same = refl
candidateFingerprintInjective
  {Spectrum.candidateB}
  {Spectrum.candidateC}
  ()
candidateFingerprintInjective
  {Spectrum.candidateB}
  {Spectrum.candidateCA}
  ()
candidateFingerprintInjective
  {Spectrum.candidateB}
  {Spectrum.candidateCB}
  ()

candidateFingerprintInjective
  {Spectrum.candidateC}
  {Spectrum.candidateA}
  ()
candidateFingerprintInjective
  {Spectrum.candidateC}
  {Spectrum.candidateB}
  ()
candidateFingerprintInjective
  {Spectrum.candidateC}
  {Spectrum.candidateC}
  same = refl
candidateFingerprintInjective
  {Spectrum.candidateC}
  {Spectrum.candidateCA}
  ()
candidateFingerprintInjective
  {Spectrum.candidateC}
  {Spectrum.candidateCB}
  ()

candidateFingerprintInjective
  {Spectrum.candidateCA}
  {Spectrum.candidateA}
  ()
candidateFingerprintInjective
  {Spectrum.candidateCA}
  {Spectrum.candidateB}
  ()
candidateFingerprintInjective
  {Spectrum.candidateCA}
  {Spectrum.candidateC}
  ()
candidateFingerprintInjective
  {Spectrum.candidateCA}
  {Spectrum.candidateCA}
  same = refl
candidateFingerprintInjective
  {Spectrum.candidateCA}
  {Spectrum.candidateCB}
  ()

candidateFingerprintInjective
  {Spectrum.candidateCB}
  {Spectrum.candidateA}
  ()
candidateFingerprintInjective
  {Spectrum.candidateCB}
  {Spectrum.candidateB}
  ()
candidateFingerprintInjective
  {Spectrum.candidateCB}
  {Spectrum.candidateC}
  ()
candidateFingerprintInjective
  {Spectrum.candidateCB}
  {Spectrum.candidateCA}
  ()
candidateFingerprintInjective
  {Spectrum.candidateCB}
  {Spectrum.candidateCB}
  same = refl

------------------------------------------------------------------------
-- 4. Fingerprint-based occurrence recognition socket.
--
-- A future direct 2B theorem may produce source pieces together with a proof
-- that their source-native rank/trace fingerprint lies in the five-candidate
-- image.  It must still pay occurrence; this module only proves uniqueness.
------------------------------------------------------------------------

record P2CandidateFingerprintOccurrenceAuthority : Set₁ where
  field
    SourcePiece :
      Set

    sourcePiece :
      Spectrum.P2C4DepthCandidate ->
      SourcePiece

    sourceRankTraceFingerprint :
      SourcePiece ->
      C4RankTraceFingerprint

    sourcePieceComesFromActualIntegralTwoBTateObject :
      SourcePiece ->
      Bool

    sourcePieceComesFromActualIntegralTwoBTateObjectIsTrue :
      (piece : SourcePiece) ->
      sourcePieceComesFromActualIntegralTwoBTateObject piece ≡ true

    candidateFingerprintCorrect :
      (candidate : Spectrum.P2C4DepthCandidate) ->
      sourceRankTraceFingerprint (sourcePiece candidate)
      ≡
      candidateFingerprint candidate

    everyCandidateActuallyOccurs :
      Spectrum.P2C4DepthCandidate ->
      Bool

    everyCandidateActuallyOccursIsTrue :
      (candidate : Spectrum.P2C4DepthCandidate) ->
      everyCandidateActuallyOccurs candidate ≡ true

    occurrenceDerivedWithoutMonsterResidual :
      Bool
    occurrenceDerivedWithoutMonsterResidualIsTrue :
      occurrenceDerivedWithoutMonsterResidual ≡ true

    occurrenceDerivedWithoutBase369 :
      Bool
    occurrenceDerivedWithoutBase369IsTrue :
      occurrenceDerivedWithoutBase369 ≡ true

open P2CandidateFingerprintOccurrenceAuthority public

------------------------------------------------------------------------
-- 5. Attribution.
------------------------------------------------------------------------

carnahanUranoIntegralGroupRings : Source.AttributedSource
carnahanUranoIntegralGroupRings =
  Source.mkDOISource
    "Scott Carnahan and Satoru Urano"
    "Monstrous Moonshine for Integral Group Rings"
    "International Mathematics Research Notices 2024(4), 2748-2789"
    "2024"
    "10.1093/imrn/rnad028"
    "https://doi.org/10.1093/imrn/rnad028"
    Source.academicArticleSource
    "Theorem 6.2 gives the rank and trace-at-g homomorphism rows on the C4 indecomposable modules. DASHI uses only those sourced values to prove injectivity of the five-candidate rank/trace fingerprint; the source is not credited with a 2B five-sector localization."
    Source.publicAttribution

p2C4FingerprintSourceAtlas : Source.AttributedSourceAtlas
p2C4FingerprintSourceAtlas =
  Source.mkSourceAtlas
    "p2 C4 candidate rank/trace fingerprint"
    "DASHI.Moonshine.OggSSPP2C4GreenFingerprintCandidateExact"
    (carnahanUranoIntegralGroupRings ∷ [])
    "Carnahan--Urano own the C4 Green-ring homomorphism values; DASHI owns the five-candidate injectivity theorem and any future 2B occurrence cross-weld."

------------------------------------------------------------------------
-- 6. No-promotion firewalls.
------------------------------------------------------------------------

data InjectiveFingerprintCreatesOccurrence : Set where
data C4FingerprintIsCo1BrauerFingerprint : Set where
data C4FingerprintCreatesInertiaSectorMap : Set where
data C4FingerprintCreatesLocalizedLength : Set where
data CarnahanUranoProveFiveCandidate2BOccurrence : Set where

injectiveFingerprintDoesNotCreateOccurrence :
  InjectiveFingerprintCreatesOccurrence -> ⊥
injectiveFingerprintDoesNotCreateOccurrence ()

c4FingerprintNotPromotedToCo1BrauerFingerprint :
  C4FingerprintIsCo1BrauerFingerprint -> ⊥
c4FingerprintNotPromotedToCo1BrauerFingerprint ()

c4FingerprintDoesNotCreateInertiaSectorMap :
  C4FingerprintCreatesInertiaSectorMap -> ⊥
c4FingerprintDoesNotCreateInertiaSectorMap ()

c4FingerprintDoesNotCreateLocalizedLength :
  C4FingerprintCreatesLocalizedLength -> ⊥
c4FingerprintDoesNotCreateLocalizedLength ()

carnahanUranoNotCreditedWithFiveCandidateOccurrence :
  CarnahanUranoProveFiveCandidate2BOccurrence -> ⊥
carnahanUranoNotCreditedWithFiveCandidateOccurrence ()

data P2CandidateFingerprintOccurrenceAuthorityInhabited : Set where

candidateFingerprintOccurrenceStillOpen :
  P2CandidateFingerprintOccurrenceAuthorityInhabited -> ⊥
candidateFingerprintOccurrenceStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record P2C4GreenFingerprintCandidateBoundary : Set where
  constructor p2-c4-green-fingerprint-candidate-boundary
  field
    carnahanUranoRankRowSourced : Bool
    carnahanUranoTraceGRowSourced : Bool
    fiveCandidateFingerprintsConstructed : Bool
    fiveCandidateFingerprintInjectivityProved : Bool
    fingerprintDefinedWithoutMonsterResidual : Bool
    fingerprintDefinedWithoutBase369 : Bool
    directTwoBOccurrencePaid : Bool
    co1BrauerFingerprintIdentityClaimed : Bool
    inertiaSectorRecognitionClaimed : Bool
    localizedDVRLengthClaimed : Bool
    occurrenceAttributedToCarnahanUrano : Bool
    attributionFirewallPreserved : Bool

canonicalP2C4GreenFingerprintCandidateBoundary :
  P2C4GreenFingerprintCandidateBoundary
canonicalP2C4GreenFingerprintCandidateBoundary =
  p2-c4-green-fingerprint-candidate-boundary
    true true true true true true
    false false false false false true
