module DASHI.Cognition.PNF.SensibLawMetaAttentionConstraintEvidenceReceiptExact where

------------------------------------------------------------------------
-- META / ATTENTION-SYSTEM / EVIDENCE-PROVENANCE FIXTURE
--
-- This file is deliberately typed by evidential status. It does not convert a
-- state's allegation, a party denial, an internal record, a verdict, or a
-- settlement into one undifferentiated proposition.
--
-- Recoverable sources / stable identifiers:
--   * Reuters, "Meta disregarded its own research on teen harm, Tennessee tells
--     jury" (27 July 2026), canonical Reuters article URL:
--     https://www.reuters.com/legal/litigation/meta-disregarded-its-own-research-teen-harm-tennessee-tells-jury-2026-07-27/
--     Reports Tennessee's opening allegation and a displayed 2017 internal Meta
--     document stating that notifications/infinite scroll were inherently at
--     odds with wellbeing; Meta contested the state's characterisation.
--   * Reuters, "Meta loses bid to dismiss US states' claims that Facebook,
--     Instagram addict children" (30 June 2026), canonical Reuters URL:
--     https://www.reuters.com/legal/government/meta-loses-bid-dismiss-us-states-claims-that-facebook-instagram-addict-children-2026-06-30/
--     Reports that deception/unfair-practice claims proceeded and that summary
--     judgment was granted to states on specified COPPA notice/parental-consent
--     issues; allegations of addictive design remained litigation claims.
--   * Reuters, "Meta's $18 billion lesson on ignoring shareholders"
--     (2 September 2026), canonical Reuters URL:
--     https://www.reuters.com/sustainability/sustainable-finance-reporting/metas-18-billion-lesson-ignoring-shareholders-2026-09-02/
--     Reports settlement structure: $12.7bn guaranteed plus up to about $5bn
--     contingent and behavioural restrictions. Settlement is not encoded as an
--     adjudication of every underlying allegation.
--
-- No DOI is asserted for these news/legal-reporting sources. The canonical
-- Reuters URLs and dates are retained as recoverable identifiers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SensibLawCorporateConstraintAndEvidenceProvenanceExact as Corp
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as Operational

internal2017WellbeingRecord : Corp.EvidenceReceipt
internal2017WellbeingRecord = Corp.evidence-receipt
  "Meta personnel contemporaneously recorded tension between engagement features such as notifications/infinite scroll and user wellbeing"
  Corp.internalContemporaneousRecord
  "Meta Platforms personnel, as reported from internal document shown in Tennessee litigation"
  "2017 internal youth/wellbeing product document reported by Reuters on 27 July 2026"
  "https://www.reuters.com/legal/litigation/meta-disregarded-its-own-research-teen-harm-tennessee-tells-jury-2026-07-27/"
  true
  false
  false

tennesseeProfitDesignAllegation : Corp.EvidenceReceipt
tennesseeProfitDesignAllegation = Corp.evidence-receipt
  "Tennessee alleged Meta kept engagement-maximising features despite internal warnings because longer teen engagement increased advertising opportunities and profit"
  Corp.partyAllegation
  "State of Tennessee, reported by Reuters"
  "Opening statements in Tennessee youth-harm litigation"
  "https://www.reuters.com/legal/litigation/meta-disregarded-its-own-research-teen-harm-tennessee-tells-jury-2026-07-27/"
  false
  true
  false

metaLitigationDenial : Corp.EvidenceReceipt
metaLitigationDenial = Corp.evidence-receipt
  "Meta disputed the states' characterisation and argued its internal documents reflected efforts to identify and address youth-safety problems"
  Corp.partyDenial
  "Meta Platforms, reported by Reuters"
  "Meta litigation position in Tennessee youth-harm proceeding"
  "https://www.reuters.com/legal/litigation/meta-disregarded-its-own-research-teen-harm-tennessee-tells-jury-2026-07-27/"
  false
  true
  false

coppaSummaryJudgmentReceipt : Corp.EvidenceReceipt
coppaSummaryJudgmentReceipt = Corp.evidence-receipt
  "A federal judge granted summary judgment to states on specified COPPA notice and parental-consent issues while other youth-addiction/deception claims remained for trial"
  Corp.adjudicatedFact
  "United States District Court, reported by Reuters"
  "Order reported 30 June 2026 in states' Meta youth-safety litigation"
  "https://www.reuters.com/legal/government/meta-loses-bid-dismiss-us-states-claims-that-facebook-instagram-addict-children-2026-06-30/"
  false
  false
  true

metaSettlementReceipt : Corp.EvidenceReceipt
metaSettlementReceipt = Corp.evidence-receipt
  "Meta agreed to a multistate youth-safety settlement with guaranteed, contingent and behavioural components"
  Corp.observedConduct
  "Meta Platforms and participating US states, reported by Reuters"
  "Meta multistate youth-safety settlement reported 2 September 2026"
  "https://www.reuters.com/sustainability/sustainable-finance-reporting/metas-18-billion-lesson-ignoring-shareholders-2026-09-02/"
  false
  true
  false

------------------------------------------------------------------------
-- Evidence topology.
------------------------------------------------------------------------

data LitigationDenialCancelsInternalRecord : Set where
data SettlementAdmitsEveryUnderlyingAllegation : Set where
data InternalKnowledgePlusObservedDesignAutomaticallyProvesBoardroomIntent : Set where

denialDoesNotCancelInternalRecord : LitigationDenialCancelsInternalRecord → ⊥
denialDoesNotCancelInternalRecord ()

settlementDoesNotAdjudicateEverything : SettlementAdmitsEveryUnderlyingAllegation → ⊥
settlementDoesNotAdjudicateEverything ()

systemEvidenceDoesNotRequireMindReading :
  InternalKnowledgePlusObservedDesignAutomaticallyProvesBoardroomIntent → ⊥
systemEvidenceDoesNotRequireMindReading ()

partyDenialStillIsNotIndependentContraryEvidence :
  Corp.PartyDenialIsIndependentContraryEvidence → ⊥
partyDenialStillIsNotIndependentContraryEvidence =
  Corp.partyDenialDoesNotBecomeIndependentEvidence

------------------------------------------------------------------------
-- POSIWID / system-operation bridge.
--
-- A system-level operational description can be grounded in repeated design,
-- incentive and outcome evidence without making subjective-intent a necessary
-- premise. This preserves "a system is what it does" as an operational audit
-- principle rather than a claim to know private mental states.
------------------------------------------------------------------------

metaOperationalAuditDoesNotNeedIntentPromotion :
  Operational.POSIWIDProvesHostileIntent → ⊥
metaOperationalAuditDoesNotNeedIntentPromotion =
  Operational.posiwidDoesNotProveHostileIntent

nominalSettlementStillDoesNotDetermineDeterrence :
  Corp.NominalPenaltyEqualsEconomicDeterrence → ⊥
nominalSettlementStillDoesNotDetermineDeterrence =
  Corp.nominalAmountDoesNotDetermineDeterrence
