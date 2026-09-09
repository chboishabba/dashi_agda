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
--   * David Shoebridge's reported characterisation of that position; and
--   * any downstream assessment of whether the characterisation is apt.
--
-- Correction history:
--   The initial user recollection named Adam Bandt.  Subsequent user correction
--   identified Greens Senator David Shoebridge, consistent with independently
--   sourced prior Shoebridge uses of "gaslighting" concerning Labor's Israel
--   policy.  The exact ABC 9-Sep-2026 wording remains source-verification debt.
--
-- A speaker's evaluative label is evidence that the speaker used that label.
-- It is not, by itself, evidence that the target proposition is true.

speakerAxis policyAxis comparisonAxis assessmentAxis correctionAxis : Fibre.OntologyAxis
speakerAxis = Fibre.externalAxis "speaker-attribution"
policyAxis = Fibre.externalAxis "policy-position"
comparisonAxis = Fibre.externalAxis "cross-government-policy-comparison"
assessmentAxis = Fibre.externalAxis "evaluative-characterisation"
correctionAxis = Fibre.externalAxis "attribution-correction"

------------------------------------------------------------------------
-- Public-source carriers checked 9 September 2026.

ukSource : String
ukSource = "UK policy, 8-9 Sep 2026: settlement-goods trade ban; new arms/export restrictions; individual sanctions; UK government/Reuters/Guardian reporting"

wongSource : String
wongSource = "Penny Wong, 9 Sep 2026: Australia pursuing further targeted measures; concerns about blanket-ban implementation and unintended consequences for Australian businesses, Palestinians and Israelis"

shoebridgePriorSource : String
shoebridgePriorSource = "Guardian 18 Sep 2025: David Shoebridge said the Albanese government had been 'gaslighting the Australian public' about its role in the genocide and legal responsibilities; Defence Connect 30 Jul 2024 records a separate Shoebridge 'gaslighting the public' allegation concerning Australia-Israel arms trade"

shoebridgeCurrentSourceStatus : String
shoebridgeCurrentSourceStatus = "user reports seeing the exact 9-Sep-2026 quote on ABC News; current web search has not yet recovered the indexed ABC artifact containing the exact wording 'such incredible gaslighting'"

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

initialBandtAttributionClaim : Fibre.ClaimBase
initialBandtAttributionClaim = Fibre.claimBase
  "au-il-sanctions:bandt-attribution-initial-recollection:2026-09-09"
  "The speaker of the reported 'such incredible gaslighting' line was Adam Bandt."
  (Fibre.externalClaimKind "superseded-speaker-attribution")
  Fibre.mainValueRole
  "superseded-by-user-correction:2026-09-09"

shoebridgeGaslightingAttributionClaim : Fibre.ClaimBase
shoebridgeGaslightingAttributionClaim = Fibre.claimBase
  "au-il-sanctions:shoebridge-gaslighting-attribution:2026-09-09"
  "David Shoebridge described Wong/Labor's position on the UK's recent Israel sanctions as 'such incredible gaslighting'."
  (Fibre.externalClaimKind "reported-speaker-attribution")
  Fibre.mainValueRole
  "user-correction:ABC-News-observation:2026-09-09;exact-source-residual-open"

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

initialBandtAttributionRefuted : Fibre.Derivation initialBandtAttributionClaim
initialBandtAttributionRefuted = Fibre.derivation
  "correction:bandt-to-shoebridge:2026-09-09"
  Fibre.contradicting
  (speakerAxis ∷ correctionAxis ∷ [])
  "User corrected the speaker after checking the ABC News item: the speaker was David Shoebridge, not Adam Bandt."
  "conversation correction plus independent historical Shoebridge 'gaslighting' source context"
  []

shoebridgePriorUsageEvidence : Fibre.Derivation shoebridgeGaslightingAttributionClaim
shoebridgePriorUsageEvidence = Fibre.derivation
  "context:shoebridge-prior-gaslighting-usage"
  Fibre.unresolved
  (speakerAxis ∷ assessmentAxis ∷ [])
  "Independent sources establish that Shoebridge has previously used 'gaslighting' against Labor on Israel-related policy, but they do not establish the exact 9-Sep-2026 ABC wording."
  shoebridgePriorSource
  ("do not substitute prior quotations for the current ABC quotation" ∷ [])

shoebridgeCurrentAttributionEvidence : Fibre.Derivation shoebridgeGaslightingAttributionClaim
shoebridgeCurrentAttributionEvidence = Fibre.derivation
  "attribution:shoebridge:abc-user-observation:2026-09-09"
  Fibre.unresolved
  (speakerAxis ∷ assessmentAxis ∷ [])
  "User reports directly seeing Shoebridge use the exact wording 'such incredible gaslighting' on ABC News today."
  shoebridgeCurrentSourceStatus
  ("recover ABC video/transcript/article or archived public artifact containing the exact wording" ∷ [])

gaslightingAptEvidence : Fibre.Derivation gaslightingAptClaim
gaslightingAptEvidence = Fibre.derivation
  "assessment:gaslighting-apt:unpromoted"
  Fibre.unresolved
  (assessmentAxis ∷ [])
  "Shoebridge's reported label is a political/evaluative characterisation, not a source-established truth condition."
  "consumer-relative assessment intentionally left open"
  ("define and pay an explicit evaluative consumer before promotion" ∷ [])

------------------------------------------------------------------------
-- Regression receipts for the non-collapse boundary.

initialBandtAttributionHasContradiction :
  Fibre.validateRequiredSubfibre Fibre.axisRequired false true ≡
  Fibre.fibreShape Fibre.violated
initialBandtAttributionHasContradiction = refl

shoebridgeExactQuoteStillUndetermined :
  Fibre.validateRequiredSubfibre Fibre.axisRequired false false ≡
  Fibre.fibreShape Fibre.undetermined
shoebridgeExactQuoteStillUndetermined = refl

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
--   initial Bandt recollection
--       -> contradicted/superseded attribution
--
--   corrected Shoebridge attribution
--       + user-observed ABC source
--       + independent prior usage context
--       -> exact-current-quote residual remains open until ABC artifact recovered
--
--   Shoebridge used label
--       != label is correct
--
-- This preserves the existing source -> claim -> consumer admission discipline.
