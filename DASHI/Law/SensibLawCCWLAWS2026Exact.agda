module DASHI.Law.SensibLawCCWLAWS2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Law.SensibLawInternationalInstrumentLifecycleExact as Lifecycle

------------------------------------------------------------------------
-- 2026 CCW / GGE ON LAWS — SOURCE-BOUND SNAPSHOT
--
-- Primary-source discipline:
--   * UN/UNODA documents pay mandate/session/document-status coordinates.
--   * A government mission report is retained as a post-session consensus
--     report, not promoted into a treaty or independent legal authority.
--   * No DOI/QID/Dewey/OEIS identifier is invented.  Absence here is local to
--     this atlas and may be refined by later source acquisition.
------------------------------------------------------------------------

ccwGGE2026AgendaSource : Source.AttributedSource
ccwGGE2026AgendaSource =
  Source.mkNoDOISource
    "Chairperson, CCW Group of Governmental Experts on LAWS"
    "CCW/GGE.1/2026/1 — Provisional agenda"
    "United Nations / UN Office for Disarmament Affairs"
    "2025"
    "https://docs-library.unoda.org/Convention_on_Certain_Conventional_Weapons_-Group_of_Governmental_Experts_on_Lethal_Autonomous_Weapons_Systems_%282026%29/CCW-GGE.1-2026-1_English.pdf"
    Source.institutionalSource
    "Primary institutional source for the 2026 session dates and the mandate to formulate by consensus elements of an instrument without prejudging its nature"
    Source.publicAttribution

ccwGGE2026AgendaSourceSnowballReceipt :
  AttributionSnowball.SourceRoleSnowballReceipt ccwGGE2026AgendaSource
ccwGGE2026AgendaSourceSnowballReceipt =
  AttributionSnowball.canonicalSourceRoleSnowballReceipt ccwGGE2026AgendaSource

ccwGGEFirst2026ChairSummarySource : Source.AttributedSource
ccwGGEFirst2026ChairSummarySource =
  Source.mkNoDOISource
    "Robert in den Bosch, Chairperson"
    "CCW/GGE.1/2026/WP.2 — Chair's summary, first 2026 session of the GGE on LAWS"
    "United Nations / UN Office for Disarmament Affairs"
    "2026"
    "https://docs-library.unoda.org/Convention_on_Certain_Conventional_Weapons_-Group_of_Governmental_Experts_on_Lethal_Autonomous_Weapons_Systems_%282026%29/CCW-GGE.1-2026-WP.2.pdf"
    Source.institutionalSource
    "Primary chair-summary source for the first 2026 session; explicitly under the Chairperson's sole authority and useful for rolling-text/procedural status, not a treaty-status promotion"
    Source.publicAttribution

ccwSeptember2026ConsensusReportSource : Source.AttributedSource
ccwSeptember2026ConsensusReportSource =
  Source.mkNoDOISource
    "Permanent Mission of Italy to the Conference on Disarmament"
    "The 128 States Parties to the CCW agreed on basic elements for defining lethal autonomous weapons and their use"
    "Government of Italy, Permanent Mission in Geneva"
    "2026"
    "https://italiarappdisarmo.esteri.it/en/news/dalla_rappresentanza/2026/09/the-128-states-parties-to-the-convention-on-certain-conventional-weapons-ccw-have-agreed-on-the-basic-elements-for-defining-lethal-autonomous-weapons-and-their-use/"
    Source.governmentSource
    "Official post-session government report of consensus on basic elements; retained as a status report and not treated as an adopted treaty/protocol or as proof of binding legal effect"
    Source.publicAttribution

ccwLAWS2026Sources : List Source.AttributedSource
ccwLAWS2026Sources =
  ccwGGE2026AgendaSource
  ∷ ccwGGEFirst2026ChairSummarySource
  ∷ ccwSeptember2026ConsensusReportSource
  ∷ []

ccwLAWS2026SourceAtlas : Source.AttributedSourceAtlas
ccwLAWS2026SourceAtlas =
  Source.mkSourceAtlas
    "2026 CCW/GGE LAWS lifecycle source atlas"
    "DASHI.Law.SensibLawCCWLAWS2026Exact"
    ccwLAWS2026Sources
    "Mandate, session dates, chair-summary status and September 2026 consensus-elements status only; does not establish a treaty, entry into force, State consent, universal binding effect, event-level applicability or independent legal authority"

ccwLAWS2026SourceAtlasCreatesAuthority : Bool
ccwLAWS2026SourceAtlasCreatesAuthority =
  Source.atlasCreatesAuthority ccwLAWS2026SourceAtlas

ccwLAWS2026SourceAtlasCreatesAuthorityIsFalse :
  ccwLAWS2026SourceAtlasCreatesAuthority ≡ false
ccwLAWS2026SourceAtlasCreatesAuthorityIsFalse =
  Source.atlasCreatesAuthorityIsFalse ccwLAWS2026SourceAtlas

------------------------------------------------------------------------
-- Snapshot as of the close of the second 2026 GGE session.
--
-- This records the legal-status boundary, not a prediction of the Seventh CCW
-- Review Conference.  A later institutional act must append/refine status.
------------------------------------------------------------------------

september2026NegotiationStatus : Lifecycle.NegotiationStatus
september2026NegotiationStatus = Lifecycle.consensusElements

september2026InstrumentNature : Lifecycle.InstrumentNature
september2026InstrumentNature = Lifecycle.instrumentNatureUnresolved

september2026LegalEffectStatus : Lifecycle.LegalEffectStatus
september2026LegalEffectStatus = Lifecycle.noNewBindingEffect

september2026ApplicabilityStatus : Lifecycle.ApplicabilityStatus
september2026ApplicabilityStatus = Lifecycle.applicabilityUnresolved

september2026LifecycleSnapshot : Lifecycle.InstrumentLifecycleSnapshot
september2026LifecycleSnapshot =
  Lifecycle.instrumentLifecycleSnapshot
    september2026NegotiationStatus
    september2026InstrumentNature
    september2026LegalEffectStatus
    september2026ApplicabilityStatus

------------------------------------------------------------------------
-- Attribution/status firewalls.
------------------------------------------------------------------------

mandateLeavesInstrumentNatureUnprejudged : Bool
mandateLeavesInstrumentNatureUnprejudged = true

septemberConsensusElementsAreNotEncodedAsAdoptedInstrument : Bool
septemberConsensusElementsAreNotEncodedAsAdoptedInstrument = true

septemberConsensusDoesNotCreateBindingEffectByCitation : Bool
septemberConsensusDoesNotCreateBindingEffectByCitation = true

existingIHLQuestionSeparateFromNewInstrumentCreation : Bool
existingIHLQuestionSeparateFromNewInstrumentCreation = true

existingIHLReferenceDoesNotMeanGGECreatedExistingIHL : Bool
existingIHLReferenceDoesNotMeanGGECreatedExistingIHL = true

reviewConferenceOutcomeNotPredictedBySeptemberSnapshot : Bool
reviewConferenceOutcomeNotPredictedBySeptemberSnapshot = true

sourceAcquisitionMayPrecedeLifecyclePayment : Bool
sourceAcquisitionMayPrecedeLifecyclePayment = true

downstreamLifecyclePaymentMaySkipUnpaidDependency : Bool
downstreamLifecyclePaymentMaySkipUnpaidDependency = false
