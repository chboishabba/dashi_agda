module DASHI.Policy.AustraliaIsraelSanctionsAttributionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Interop.WikidataDerivationFibreBridge as Fibre
import DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact as Transcript
import DASHI.Policy.ABC730PrimarySourceSpeakerResolutionExact as SpeakerSource

------------------------------------------------------------------------
-- Consumer-facing sanctions attribution module.
-- Canonical transcript extraction is owned by Transcript; this module only
-- consumes selected transcript coordinates and keeps policy comparison,
-- speaker attribution, and evaluative truth as separate fibres.
--
-- SpeakerSource is a later same-programme primary-source overlay.  It does not
-- rewrite the supplied transcript ledger; it can pay or contradict named
-- speaker hypotheses independently of transcript-wording support.

speakerAxis policyAxis comparisonAxis assessmentAxis correctionAxis transcriptAxis : Fibre.OntologyAxis
speakerAxis = Fibre.externalAxis "speaker-attribution"
policyAxis = Fibre.externalAxis "policy-position"
comparisonAxis = Fibre.externalAxis "cross-government-policy-comparison"
assessmentAxis = Fibre.externalAxis "evaluative-characterisation"
correctionAxis = Fibre.externalAxis "attribution-correction"
transcriptAxis = Fibre.externalAxis "broadcast-transcript"

------------------------------------------------------------------------
-- Canonical transcript handles.

canonicalABCWords : Transcript.TranscriptClaim
canonicalABCWords = Transcript.abcLaborGaslightingClaim

canonicalAustraliaNoBlanketBan : Transcript.TranscriptClaim
canonicalAustraliaNoBlanketBan = Transcript.abcAustraliaNoBlanketBanClaim

canonicalAustraliaRationale : Transcript.TranscriptClaim
canonicalAustraliaRationale = Transcript.abcAustraliaUnintendedConsequencesRationale

canonicalUKImportBan : Transcript.TranscriptClaim
canonicalUKImportBan = Transcript.abcUKImportBanClaim

canonicalPrimarySpeakerSource : SpeakerSource.PrimarySourceReceipt
canonicalPrimarySpeakerSource = SpeakerSource.abcPublishedTranscript

------------------------------------------------------------------------
-- Base claims for downstream consumers.

ukBroaderMeasuresClaim : Fibre.ClaimBase
ukBroaderMeasuresClaim = Fibre.claimBase
  "au-il-sanctions:uk-broader-measures:2026-09-09"
  "The UK adopted an import ban concerning settlement goods; other UK measures must be sourced independently before being bundled into this consumer."
  (Fibre.externalClaimKind "public-policy-source-claim")
  Fibre.mainValueRole
  "ABC730-2026-09-09-C017-plus-independent-source-residuals"

wongNoBlanketBanClaim : Fibre.ClaimBase
wongNoBlanketBanClaim = Fibre.claimBase
  "au-il-sanctions:wong-no-blanket-ban:2026-09-09"
  "Australia was not at that time pursuing a blanket-style import ban and cited implementation/unintended-consequence concerns."
  (Fibre.externalClaimKind "speaker-policy-position")
  Fibre.mainValueRole
  "ABC730-2026-09-09-C028-C029"

policyDifferenceClaim : Fibre.ClaimBase
policyDifferenceClaim = Fibre.claimBase
  "au-il-sanctions:uk-australia-policy-difference:2026-09-09"
  "On the transcript source surface, the UK includes an import ban that Australia was not at that time pursuing."
  (Fibre.externalClaimKind "bounded-cross-source-comparison")
  Fibre.mainValueRole
  "ABC730-2026-09-09-C017-C028"

abcGaslightingWordsClaim : Fibre.ClaimBase
abcGaslightingWordsClaim = Fibre.claimBase
  "au-il-sanctions:abc-730-gaslighting-words:2026-09-09"
  "The 9 September 2026 ABC 7.30 segment contains the words 'This is unbelievable gaslighting from labour'."
  (Fibre.externalClaimKind "broadcast-transcript-claim")
  Fibre.mainValueRole
  "ABC730-2026-09-09-C032"

bandtSpeakerClaim : Fibre.ClaimBase
bandtSpeakerClaim = Fibre.claimBase
  "au-il-sanctions:bandt-speaker:2026-09-09"
  "Adam Bandt was the speaker of the ABC 7.30 'unbelievable gaslighting from labour' line."
  (Fibre.externalClaimKind "speaker-attribution")
  Fibre.mainValueRole
  "ABC-primary-source-contradicted"

shoebridgeSpeakerClaim : Fibre.ClaimBase
shoebridgeSpeakerClaim = Fibre.claimBase
  "au-il-sanctions:shoebridge-speaker:2026-09-09"
  "David Shoebridge was the speaker of the ABC 7.30 'unbelievable gaslighting from labour' line."
  (Fibre.externalClaimKind "speaker-attribution")
  Fibre.mainValueRole
  "ABC-primary-source-supported"

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
  "transcript-consumer:ABC730-C017"
  Fibre.supporting
  (policyAxis ∷ transcriptAxis ∷ [])
  "Canonical transcript claim C017 records Britain's move to impose an import ban on settlement goods."
  "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact.C017"
  ("Do not infer every separately reported UK restriction from C017 alone." ∷ [])

wongNoBlanketBanEvidence : Fibre.Derivation wongNoBlanketBanClaim
wongNoBlanketBanEvidence = Fibre.derivation
  "transcript-consumer:ABC730-C028-C029"
  Fibre.supporting
  (speakerAxis ∷ policyAxis ∷ transcriptAxis ∷ [])
  "Canonical transcript claims C028-C029 record no blanket-style Australian ban and the implementation/unintended-consequence rationale."
  "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact.C028-C029"
  []

policyDifferenceEvidence : Fibre.Derivation policyDifferenceClaim
policyDifferenceEvidence = Fibre.derivation
  "comparison:ABC730-C017-v-C028"
  Fibre.supporting
  (comparisonAxis ∷ policyAxis ∷ transcriptAxis ∷ [])
  "C017 records the UK import ban; C028 records Australia not pursuing a blanket-style import ban at that time."
  "bounded comparison over canonical transcript claims only"
  []

abcGaslightingWordsEvidence : Fibre.Derivation abcGaslightingWordsClaim
abcGaslightingWordsEvidence = Fibre.derivation
  "transcript-consumer:ABC730-C032"
  Fibre.supporting
  (transcriptAxis ∷ assessmentAxis ∷ [])
  "Canonical transcript claim C032 contains the exact wording 'This is unbelievable gaslighting from labour'."
  "DASHI.Policy.ABC730WestBankSanctionsTranscriptClaimsExact.C032"
  []

bandtSpeakerEvidence : Fibre.Derivation bandtSpeakerClaim
bandtSpeakerEvidence = Fibre.derivation
  "attribution:bandt:ABC-primary-source-contradiction"
  Fibre.contradicting
  (speakerAxis ∷ correctionAxis ∷ transcriptAxis ∷ [])
  "ABC's published speaker-labelled transcript assigns the gaslighting line to David Shoebridge, not Adam Bandt."
  "DASHI.Policy.ABC730PrimarySourceSpeakerResolutionExact.bandtC032Resolution"
  ("A later primary-source correction does not rewrite the historical supplied-transcript speakerUnresolved state." ∷ [])

shoebridgeSpeakerEvidence : Fibre.Derivation shoebridgeSpeakerClaim
shoebridgeSpeakerEvidence = Fibre.derivation
  "attribution:shoebridge:ABC-primary-source-support"
  Fibre.supporting
  (speakerAxis ∷ correctionAxis ∷ transcriptAxis ∷ [])
  "ABC's published speaker-labelled transcript assigns the gaslighting line to David Shoebridge, Greens Senator."
  "DASHI.Policy.ABC730PrimarySourceSpeakerResolutionExact.c032SpeakerResolution"
  ("Speaker attribution does not promote the evaluative claim that the characterisation is correct." ∷ [])

gaslightingAptEvidence : Fibre.Derivation gaslightingAptClaim
gaslightingAptEvidence = Fibre.derivation
  "assessment:gaslighting-apt:unpromoted"
  Fibre.unresolved
  (assessmentAxis ∷ [])
  "C032 is evaluative rhetoric; its presence and now-resolved speaker identity do not establish that the evaluation is correct."
  "ABC730-2026-09-09-C032"
  ("define and pay an explicit evaluative consumer before promotion" ∷ [])

------------------------------------------------------------------------
-- Non-collapse receipts.

abcWordsSupported :
  Fibre.validateRequiredSubfibre Fibre.axisRequired true false ≡
  Fibre.fibreShape Fibre.satisfied
abcWordsSupported = refl

shoebridgeSpeakerSupported :
  Fibre.validateRequiredSubfibre Fibre.axisRequired true false ≡
  Fibre.fibreShape Fibre.satisfied
shoebridgeSpeakerSupported = refl

bandtSpeakerContradicted :
  Fibre.validateRequiredSubfibre Fibre.axisRequired false true ≡
  Fibre.fibreShape Fibre.contradicted
bandtSpeakerContradicted = refl

evaluativeTruthStillUndetermined :
  Fibre.validateRequiredSubfibre Fibre.axisRequired false false ≡
  Fibre.fibreShape Fibre.undetermined
evaluativeTruthStillUndetermined = refl
