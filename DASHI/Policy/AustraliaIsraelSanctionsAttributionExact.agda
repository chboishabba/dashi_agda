module DASHI.Policy.AustraliaIsraelSanctionsAttributionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Interop.WikidataDerivationFibreBridge as Fibre

------------------------------------------------------------------------
-- Source-conditioned political attribution fixture.
--
-- This module deliberately separates:
--   * what the UK announced;
--   * what Penny Wong / the Australian Government said;
--   * the ABC 7.30 broadcast wording;
--   * the identity of the speaker at that broadcast cut; and
--   * any downstream assessment of whether the characterisation is apt.
--
-- Correction history:
--   The initial user recollection named Adam Bandt. A subsequent search raised
--   David Shoebridge as a plausible speaker, but the recovered ABC 7.30
--   transcript does not label the speaker at the relevant cut. The exact words
--   are now source-backed; the speaker identity remains unresolved.
--
-- A speaker's evaluative label is evidence that the speaker used that label.
-- It is not, by itself, evidence that the target proposition is true.

speakerAxis policyAxis comparisonAxis assessmentAxis correctionAxis transcriptAxis : Fibre.OntologyAxis
speakerAxis = Fibre.externalAxis "speaker-attribution"
policyAxis = Fibre.externalAxis "policy-position"
comparisonAxis = Fibre.externalAxis "cross-government-policy-comparison"
assessmentAxis = Fibre.externalAxis "evaluative-characterisation"
correctionAxis = Fibre.externalAxis "attribution-correction"
transcriptAxis = Fibre.externalAxis "broadcast-transcript"

------------------------------------------------------------------------
-- Public/source carriers checked 9 September 2026.

ukSource : String
ukSource = "UK policy, 8-9 Sep 2026: settlement-goods trade ban; new arms/export restrictions; individual sanctions; public reporting"

wongSource : String
wongSource = "Penny Wong, 9 Sep 2026: Australia pursuing further targeted measures; concerns about blanket-ban implementation and unintended consequences for Australian businesses, Palestinians and Israelis"

abc730TranscriptSource : String
abc730TranscriptSource = "ABC 7.30 broadcast transcript supplied by user, 9 Sep 2026: after Wong/Labor rationale, transcript contains 'This is unbelievable gaslighting from labour'."

speakerStatus : String
speakerStatus = "speaker not labelled in recovered transcript at the relevant cut; Bandt and Shoebridge attributions must not be promoted from wording alone"

------------------------------------------------------------------------
-- Base claims.

ukBroaderMeasuresClaim : Fibre.ClaimBase
ukBroaderMeasuresClaim = Fibre.claimBase
  "au-il-sanctions:uk-broader-measures:2026-09-09"
  "The UK adopted a settlement-goods trade ban together with additional arms/export restrictions and individual sanctions concerning Israeli settlement activity."
  (Fibre.externalClaimKind "public-policy-source-claim")
  Fibre.mainValueRole
  "source-snapshot:2026-09-09"

wongNoBlanketBanClaim : Fibre.ClaimBase
wongNoBlanketBanClaim = Fibre.claimBase
  "au-il-sanctions:wong-no-blanket-ban:2026-09-09"
  "Penny Wong said Australia was pursuing further targeted measures but was not adopting the UK-style blanket settlement-goods ban, citing implementation and unintended-consequence concerns."
  (Fibre.externalClaimKind "speaker-policy-position")
  Fibre.mainValueRole
  "source-snapshot:2026-09-09"

policyDifferenceClaim : Fibre.ClaimBase
policyDifferenceClaim = Fibre.claimBase
  "au-il-sanctions:uk-australia-policy-difference:2026-09-09"
  "On the verified 9 September 2026 source surface, the UK policy package is broader than the Australian position stated by Wong because the UK includes a settlement-goods trade ban that Australia is not presently adopting."
  (Fibre.externalClaimKind "bounded-cross-source-comparison")
  Fibre.mainValueRole
  "source-snapshot:2026-09-09"

abcGaslightingWordsClaim : Fibre.ClaimBase
abcGaslightingWordsClaim = Fibre.claimBase
  "au-il-sanctions:abc-730-gaslighting-words:2026-09-09"
  "The 9 September 2026 ABC 7.30 segment contains the words 'This is unbelievable gaslighting from labour'."
  (Fibre.externalClaimKind "broadcast-transcript-claim")
  Fibre.mainValueRole
  "user-supplied-transcript:2026-09-09"

bandtSpeakerClaim : Fibre.ClaimBase
bandtSpeakerClaim = Fibre.claimBase
  "au-il-sanctions:bandt-speaker:2026-09-09"
  "Adam Bandt was the speaker of the ABC 7.30 'unbelievable gaslighting from labour' line."
  (Fibre.externalClaimKind "speaker-attribution")
  Fibre.mainValueRole
  "speaker-unresolved"

shoebridgeSpeakerClaim : Fibre.ClaimBase
shoebridgeSpeakerClaim = Fibre.claimBase
  "au-il-sanctions:shoebridge-speaker:2026-09-09"
  "David Shoebridge was the speaker of the ABC 7.30 'unbelievable gaslighting from labour' line."
  (Fibre.externalClaimKind "speaker-attribution")
  Fibre.mainValueRole
  "speaker-unresolved"

gaslightingAptClaim : Fibre.ClaimBase
gaslightingAptClaim = Fibre.claimBase
  "au-il-sanctions:gaslighting-characterisation-apt:2026-09-09"
  "The Wong/Labor position is correctly characterised as gaslighting."
  (Fibre.externalClaimKind "evaluative-political-claim")
  Fibre.mainValueRole
  "assessment-not-promoted"

------------------------------------------------------------------------
-- Derivations.

ukBroaderMeasuresEvidence : Fibre.Derivation ukBroaderMeasuresClaim
ukBroaderMeasuresEvidence = Fibre.derivation
  "source:uk-policy:2026-09-08/09"
  Fibre.supporting
  (policyAxis ∷ [])
  ukSource
  "public sources checked 2026-09-09"
  []

wongNoBlanketBanEvidence : Fibre.Derivation wongNoBlanketBanClaim
wongNoBlanketBanEvidence = Fibre.derivation
  "source:wong-policy:2026-09-09"
  Fibre.supporting
  (speakerAxis ∷ policyAxis ∷ [])
  wongSource
  "public parliamentary/media reporting checked 2026-09-09"
  []

policyDifferenceEvidence : Fibre.Derivation policyDifferenceClaim
policyDifferenceEvidence = Fibre.derivation
  "comparison:uk-v-australia:2026-09-09"
  Fibre.supporting
  (comparisonAxis ∷ policyAxis ∷ [])
  "UK source includes settlement-goods trade ban; Wong source expressly declines a blanket ban while proposing targeted measures."
  "derived only from the two bounded public-source carriers above"
  []

abcGaslightingWordsEvidence : Fibre.Derivation abcGaslightingWordsClaim
abcGaslightingWordsEvidence = Fibre.derivation
  "source:abc-730-transcript:2026-09-09"
  Fibre.supporting
  (transcriptAxis ∷ assessmentAxis ∷ [])
  abc730TranscriptSource
  "user-supplied ABC 7.30 transcript, relevant span around lines 22-24"
  []

bandtSpeakerEvidence : Fibre.Derivation bandtSpeakerClaim
bandtSpeakerEvidence = Fibre.derivation
  "attribution:bandt:unresolved-after-transcript"
  Fibre.unresolved
  (speakerAxis ∷ correctionAxis ∷ [])
  "Recovered transcript proves the words but does not label the speaker at the relevant cut."
  speakerStatus
  ("recover labelled video frame, caption, lower-third, or transcript with speaker identity" ∷ [])

shoebridgeSpeakerEvidence : Fibre.Derivation shoebridgeSpeakerClaim
shoebridgeSpeakerEvidence = Fibre.derivation
  "attribution:shoebridge:unresolved-after-transcript"
  Fibre.unresolved
  (speakerAxis ∷ correctionAxis ∷ [])
  "Shoebridge is independently source-backed as a critic of Labor's Israel policy, but the recovered ABC transcript alone does not identify him as the speaker of this line."
  speakerStatus
  ("recover labelled video frame, caption, lower-third, or transcript with speaker identity" ∷ [])

gaslightingAptEvidence : Fibre.Derivation gaslightingAptClaim
gaslightingAptEvidence = Fibre.derivation
  "assessment:gaslighting-apt:unpromoted"
  Fibre.unresolved
  (assessmentAxis ∷ [])
  "The broadcast's evaluative label is not by itself a source-established truth condition."
  "consumer-relative assessment intentionally left open"
  ("define and pay an explicit evaluative consumer before promotion" ∷ [])

------------------------------------------------------------------------
-- Regression receipts for the non-collapse boundary.

abcWordsSupported :
  Fibre.validateRequiredSubfibre Fibre.axisRequired true false ≡
  Fibre.fibreShape Fibre.satisfied
abcWordsSupported = refl

bandtSpeakerStillUndetermined :
  Fibre.validateRequiredSubfibre Fibre.axisRequired false false ≡
  Fibre.fibreShape Fibre.undetermined
bandtSpeakerStillUndetermined = refl

shoebridgeSpeakerStillUndetermined :
  Fibre.validateRequiredSubfibre Fibre.axisRequired false false ≡
  Fibre.fibreShape Fibre.undetermined
shoebridgeSpeakerStillUndetermined = refl

evaluativeTruthStillUndetermined :
  Fibre.validateRequiredSubfibre Fibre.axisRequired false false ≡
  Fibre.fibreShape Fibre.undetermined
evaluativeTruthStillUndetermined = refl

------------------------------------------------------------------------
-- Intended interpretation:
--
--   verified UK action
--       + verified Wong position
--       -> bounded policy-difference claim
--
--   recovered ABC 7.30 transcript
--       -> exact words supported
--       -> speaker identity still unresolved
--
--   exact words supported
--       != Bandt was speaker
--       != Shoebridge was speaker
--       != evaluative label is correct
--
-- This preserves the existing source -> claim -> consumer admission discipline.
