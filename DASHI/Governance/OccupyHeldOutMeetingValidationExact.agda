module DASHI.Governance.OccupyHeldOutMeetingValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- PROSPECTIVE HELD-OUT VALIDATION PROTOCOL.
--
-- This owner exists because several People's Library meetings have already
-- been inspected during evidence acquisition.  They cannot honestly be called
-- held out after their contents and process outcomes are known.
--
-- Provenance / methodology rule:
--   * archive records supply observations;
--   * DASHI supplies the coding and validation protocol;
--   * candidate held-out meetings must be selected/frozen before their
--     participant-issue and burden/outcome coding is inspected;
--   * coding vocabulary and model family must be frozen before evaluation.
------------------------------------------------------------------------

data DevelopmentEvidenceClass : Set where
  inspectedArchivePage : DevelopmentEvidenceClass
  sourceUsedToDesignCoding : DevelopmentEvidenceClass
  sourceUsedToDesignOutcomeVocabulary : DevelopmentEvidenceClass

record AlreadyInspectedMeeting : Set where
  constructor alreadyInspectedMeeting
  field
    meetingLabel : String
    reasonNotHeldOut : DevelopmentEvidenceClass

open AlreadyInspectedMeeting public

knownDevelopmentMeetings : List AlreadyInspectedMeeting
knownDevelopmentMeetings =
  alreadyInspectedMeeting "2011-10-15 People's Library first formal WG meeting" inspectedArchivePage
  ∷ alreadyInspectedMeeting "2011-10-22 People's Library WG meeting" sourceUsedToDesignCoding
  ∷ alreadyInspectedMeeting "2011-11-20 People's Library WG meeting" sourceUsedToDesignCoding
  ∷ alreadyInspectedMeeting "2011-11-28 People's Library WG meeting" sourceUsedToDesignOutcomeVocabulary
  ∷ alreadyInspectedMeeting "2011-12-04 People's Library WG meeting" sourceUsedToDesignOutcomeVocabulary
  ∷ alreadyInspectedMeeting "2011-12-11 People's Library WG meeting" sourceUsedToDesignCoding
  ∷ alreadyInspectedMeeting "2012-01-08 People's Library WG meeting" sourceUsedToDesignCoding
  ∷ alreadyInspectedMeeting "2012-03-11 People's Library WG meeting" sourceUsedToDesignOutcomeVocabulary
  ∷ []

record ProspectiveHeldOutPlan : Set where
  constructor prospectiveHeldOutPlan
  field
    sourceCorpusLabel : String
    selectionRule : String
    incidenceCodingRule : String
    outcomeCodingRule : String
    confoundVocabulary : String
    modelFamily : String
    meetingSetFrozenBeforeExtraction : Bool
    codingProtocolFrozenBeforeExtraction : Bool
    modelFamilyFrozenBeforeOutcomeEvaluation : Bool

open ProspectiveHeldOutPlan public

canonicalProspectiveHeldOutPlan : ProspectiveHeldOutPlan
canonicalProspectiveHeldOutPlan =
  prospectiveHeldOutPlan
    "future not-yet-inspected OWS / People's Library meeting records, preferably from the Kinna-Prichard corpus once materialised"
    "choose meeting identifiers before reading/coding participant-issue rows or process outcomes; record inclusion/exclusion reasons"
    "admit only explicit named-person-to-named-issue/topic associations; never attendance x agenda cross-products; collapse repeated same-person/same-issue utterances within meeting"
    "record only source-explicit duration, mediation, tabled/unresolved items, decisions, interruption/conflict observations; qualitative wording stays qualitative"
    "participant count, issue count, meeting type, external shock/context, source completeness, repeated participants"
    "predeclared candidate relation from incidence/control coordinates to independently coded burden outcomes"
    true
    true
    true

record HeldOutValidationBoundary : Set where
  constructor heldOutValidationBoundary
  field
    alreadyInspectedMeetingCountsAsProspectiveHeldOut : Bool
    retrospectiveTrainTestSplitEqualsProspectiveValidation : Bool
    modelChoiceAfterHeldOutOutcomesStillCountsAsHeldOut : Bool

    heldOutSetMustBeFrozenBeforeOutcomeCoding : Bool
    codingProtocolMustBeFrozenBeforeHeldOutExtraction : Bool
    modelFamilyMustBeFrozenBeforeHeldOutEvaluation : Bool
    sourceCompletenessStillRequiresAudit : Bool

    prospectiveHeldOutValidationPaid : Bool

open HeldOutValidationBoundary public

canonicalHeldOutBoundary : HeldOutValidationBoundary
canonicalHeldOutBoundary =
  heldOutValidationBoundary
    false
    false
    false
    true
    true
    true
    true
    false

canonicalOccupyHeldOutValidationReceipt : GenericReceipt.GenericReceipt
canonicalOccupyHeldOutValidationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "prospective Occupy meeting held-out validation protocol"
    "DASHI.Governance.OccupyHeldOutMeetingValidationExact"
    "canonicalHeldOutBoundary"
    "marks already-inspected People's Library meetings as development evidence and defines a prospective freeze-before-coding protocol for future unseen meeting records, including frozen incidence/outcome coding, confound vocabulary and model family"
    "retrospective relabelling is not promoted to prospective validation; no held-out receipt is paid until a meeting set is frozen before extraction and subsequently evaluated under the frozen protocol"
    "agda -i . DASHI/Governance/OccupyHeldOutMeetingValidationRegression.agda"
