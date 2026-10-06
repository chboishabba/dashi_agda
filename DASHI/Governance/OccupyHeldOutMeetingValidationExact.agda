module DASHI.Governance.OccupyHeldOutMeetingValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- PROSPECTIVE HELD-OUT VALIDATION PROTOCOL.
--
-- Several People's Library meetings have already been inspected during
-- evidence acquisition. They cannot honestly be called held out after their
-- contents or process outcomes are known.
--
-- Provenance / methodology rule:
--   * archive records supply observations;
--   * DASHI supplies the coding and validation protocol;
--   * candidate held-out records must be selected outcome-blind;
--   * corpus manifest, coding vocabulary, confounds and model family must be
--     frozen before held-out extraction/evaluation.
------------------------------------------------------------------------

data DevelopmentEvidenceClass : Set where
  inspectedArchivePage : DevelopmentEvidenceClass
  sourceUsedToDesignCoding : DevelopmentEvidenceClass
  sourceUsedToDesignOutcomeVocabulary : DevelopmentEvidenceClass
  sourceUsedToDesignPanelMissingness : DevelopmentEvidenceClass

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
  ∷ alreadyInspectedMeeting "2011-11-06 People's Library WG meeting" sourceUsedToDesignPanelMissingness
  ∷ alreadyInspectedMeeting "2011-11-20 People's Library WG meeting" sourceUsedToDesignCoding
  ∷ alreadyInspectedMeeting "2011-11-28 People's Library WG meeting" sourceUsedToDesignOutcomeVocabulary
  ∷ alreadyInspectedMeeting "2011-12-04 People's Library WG meeting" sourceUsedToDesignOutcomeVocabulary
  ∷ alreadyInspectedMeeting "2011-12-11 People's Library WG meeting" sourceUsedToDesignCoding
  ∷ alreadyInspectedMeeting "2012-01-08 People's Library WG meeting" sourceUsedToDesignCoding
  ∷ alreadyInspectedMeeting "2012-02-19 People's Library WG meeting" sourceUsedToDesignPanelMissingness
  ∷ alreadyInspectedMeeting "2012-02-26 People's Library WG meeting" sourceUsedToDesignPanelMissingness
  ∷ alreadyInspectedMeeting "2012-03-11 People's Library WG meeting" sourceUsedToDesignOutcomeVocabulary
  ∷ alreadyInspectedMeeting "2012-04-22 People's Library WG meeting" inspectedArchivePage
  ∷ []

------------------------------------------------------------------------
-- Prospective manifest-first split.
--
-- The Kinna-Prichard corpus has not yet materialised in this environment.
-- Therefore no concrete held-out records are claimed. Instead the split rule
-- is frozen now, before outcome extraction:
--
--   1. materialise corpus;
--   2. freeze manifest + checksum;
--   3. retain Wall Street meeting-minute records only under a predeclared
--      inclusion rule;
--   4. sort by stable canonical corpus identifier / filename;
--   5. assign every fifth eligible record (indices 5,10,15,...) to holdout;
--   6. all remaining eligible records are development/training records;
--   7. never reassign after reading outcomes.
--
-- This is a DASHI validation design, not an archival-source claim.
------------------------------------------------------------------------

record ProspectiveHeldOutPlan : Set where
  constructor prospectiveHeldOutPlan
  field
    sourceCorpusLabel : String
    manifestFreezeRule : String
    eligibilityRule : String
    selectionRule : String
    incidenceCodingRule : String
    outcomeCodingRule : String
    confoundVocabulary : String
    modelFamily : String
    meetingSetFrozenBeforeExtraction : Bool
    corpusManifestFrozenBeforeSelection : Bool
    codingProtocolFrozenBeforeExtraction : Bool
    modelFamilyFrozenBeforeOutcomeEvaluation : Bool
    assignmentImmutableAfterOutcomeInspection : Bool

open ProspectiveHeldOutPlan public

canonicalProspectiveHeldOutPlan : ProspectiveHeldOutPlan
canonicalProspectiveHeldOutPlan =
  prospectiveHeldOutPlan
    "Kinna-Prichard OccupyFiles corpus once materialised; Wall Street meeting-minute records only"
    "materialise corpus, enumerate canonical record identifiers/filenames, and record a corpus-manifest checksum before assigning development versus held-out records"
    "include only records identified by the frozen manifest/source metadata as Occupy Wall Street meeting minutes; exclude non-Wall-Street camps and non-meeting artifacts by the frozen rule"
    "sort eligible records by stable canonical corpus identifier or filename; assign every fifth eligible record (5,10,15,...) to held out and all others to development; never alter assignment after reading outcomes"
    "admit only explicit named-person-to-named-issue/topic associations; never attendance x agenda cross-products; collapse repeated same-person/same-issue utterances within meeting"
    "record only source-explicit duration, mediation, tabled/unresolved items, decisions, interruption/conflict observations; qualitative wording stays qualitative"
    "participant count, issue count, meeting type, external shock/context, source completeness, repeated participants"
    "predeclared candidate relation from incidence/control coordinates to independently coded burden outcomes"
    true
    true
    true
    true
    true

record HeldOutValidationBoundary : Set where
  constructor heldOutValidationBoundary
  field
    alreadyInspectedMeetingCountsAsProspectiveHeldOut : Bool
    retrospectiveTrainTestSplitEqualsProspectiveValidation : Bool
    modelChoiceAfterHeldOutOutcomesStillCountsAsHeldOut : Bool
    outcomeAwareRecordSelectionAllowed : Bool

    heldOutSetMustBeFrozenBeforeOutcomeCoding : Bool
    corpusManifestMustBeFrozenBeforeSelection : Bool
    selectionRuleMustBeOutcomeBlindAndDeterministic : Bool
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
    false
    true
    true
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
    "marks every already-inspected People's Library meeting as development evidence and freezes a manifest-first, deterministic, outcome-blind every-fifth-record held-out assignment for eligible Wall Street meeting minutes once the Kinna-Prichard corpus is materialised"
    "the split rule is paid but the validation result is not: no held-out receipt exists until a checksum-pinned corpus manifest is materialised, the frozen assignment is applied before outcome extraction, and held-out records are evaluated under the frozen coding/model protocol"
    "agda -i . DASHI/Governance/OccupyHeldOutMeetingValidationRegression.agda"
