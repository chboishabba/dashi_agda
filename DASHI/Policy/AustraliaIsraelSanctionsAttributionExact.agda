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
--   * Adam Bandt's reported characterisation of that position; and
--   * any downstream assessment of whether the characterisation is apt.
--
-- A speaker's evaluative label is evidence that the speaker used that label.
-- It is not, by itself, evidence that the target proposition is true.

speakerAxis policyAxis comparisonAxis assessmentAxis : Fibre.OntologyAxis
speakerAxis = Fibre.externalAxis "speaker-attribution"
policyAxis = Fibre.externalAxis "policy-position"
comparisonAxis = Fibre.externalAxis "cross-government-policy-comparison"
assessmentAxis = Fibre.externalAxis "evaluative-characterisation"

------------------------------------------------------------------------
-- Public-source carriers checked 9 September 2026.

ukSource : String
ukSource = "UK policy, 8-9 Sep 2026: settlement-goods trade ban; new arms/export restrictions; individual sanctions; UK government/Reuters/Guardian reporting"

wongSource : String
wongSource = "Penny Wong, 9 Sep 2026: Australia pursuing further targeted measures; concerns about blanket-ban implementation and unintended consequences for Australian businesses, Palestinians and Israelis"

bandtSourceStatus : String
bandtSourceStatus = "user-reported quotation; exact primary/public artifact for wording not yet verified"

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

bandtGaslightingAttributionClaim : Fibre.ClaimBase
bandtGaslightingAttributionClaim = Fibre.claimBase
  "au-il-sanctions:bandt-gaslighting-attribution:2026-09-09"
  "Adam Bandt described Wong/Labor's position on the UK's recent Israel sanctions as 'such incredible gaslighting'."
  (Fibre.externalClaimKind "reported-speaker-attribution")
  Fibre.mainValueRole
  "user-report:2026-09-09;primary-source-residual-open"

gaslightingAptClaim : Fibre.ClaimBase
gaslightingAptClaim = Fibre.claimBase
  "au-il-sanctions:gaslighting-characterisation-apt:2026-09-09"
  "The Wong/Labor position is correctly characterised as gaslighting."
  (Fibre.externalClaimKind "evaluative-political-claim")
  Fibre.mainValueRole
  "assessment-not-promoted"

------------------------------------------------------------------------
-- Derivations.  The verified policy claims are supporting derivations.
-- The Bandt wording remains unresolved until its primary/public artifact is
-- located.  The truth of the evaluative label remains independently unresolved.

ukBroaderMeasuresEvidence : Fibre.Derivation ukBroaderMeasuresClaim
ukBroaderMeasuresEvidence = Fibre.derivation
  "source:uk-policy:2026-09-08/09"
  Fibre.supporting
  (policyAxis ∷ [])
  ukSource
  "gov.uk / Reuters / Guardian, checked 2026-09-09"
  []

wongNoBlanketBanEvidence : Fibre.Derivation wongNoBlanketBanClaim
wongNoBlanketBanEvidence = Fibre.derivation
  "source:wong-policy:2026-09-09"
  Fibre.supporting
  (speakerAxis ∷ policyAxis ∷ [])
  wongSource
  "public parliamentary/media reporting, checked 2026-09-09"
  []

policyDifferenceEvidence : Fibre.Derivation policyDifferenceClaim
policyDifferenceEvidence = Fibre.derivation
  "comparison:uk-v-australia:2026-09-09"
  Fibre.supporting
  (comparisonAxis ∷ policyAxis ∷ [])
  "UK source includes settlement-goods trade ban; Wong source expressly declines a blanket ban while proposing targeted measures."
  "derived only from the two bounded public-source carriers above"
  []

bandtGaslightingEvidence : Fibre.Derivation bandtGaslightingAttributionClaim
bandtGaslightingEvidence = Fibre.derivation
  "attribution:bandt:user-report:2026-09-09"
  Fibre.unresolved
  (speakerAxis ∷ assessmentAxis ∷ [])
  "User reports exact wording: 'such incredible gaslighting'."
  bandtSourceStatus
  ("locate primary Bandt post/video/transcript or independently archived public artifact" ∷ [])

gaslightingAptEvidence : Fibre.Derivation gaslightingAptClaim
gaslightingAptEvidence = Fibre.derivation
  "assessment:gaslighting-apt:unpromoted"
  Fibre.unresolved
  (assessmentAxis ∷ [])
  "Bandt's reported label is a political/evaluative characterisation, not a source-established truth condition."
  "consumer-relative assessment intentionally left open"
  ("define and pay an explicit evaluative consumer before promotion" ∷ [])

------------------------------------------------------------------------
-- Regression receipts for the non-collapse boundary.

bandtAttributionStillUndetermined :
  Fibre.validateRequiredSubfibre Fibre.axisRequired false false ≡
  Fibre.fibreShape Fibre.undetermined
bandtAttributionStillUndetermined = refl

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
--   user-reported Bandt wording
--       -> attribution residual until primary/public source is found
--
--   Bandt used label
--       != label is correct
--
-- This preserves the existing source -> claim -> consumer admission discipline.
