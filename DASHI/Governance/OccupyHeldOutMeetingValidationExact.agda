module DASHI.Governance.OccupyHeldOutMeetingValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.OccupyFilesCorpusReceiptExact as Corpus
import DASHI.Governance.OccupyOWSManifestExact as Manifest

------------------------------------------------------------------------
-- PROSPECTIVE HELD-OUT VALIDATION PROTOCOL.
--
-- People's Library development evidence and the materialised OWS GA corpus
-- are distinct archival lanes. Already-inspected records cannot honestly be
-- called held out after their contents or process outcomes are known.
--
-- Provenance / methodology rule:
--   * archive records supply observations;
--   * Kinna/Prichard supply curation/selection metadata for OccupyFiles;
--   * DASHI supplies parsing, coding and validation protocol;
--   * candidate held-out records are selected outcome-blind;
--   * coding vocabulary, confounds and model family remain frozen before
--     held-out outcome extraction/evaluation.
------------------------------------------------------------------------

data DevelopmentEvidenceClass : Set where
  inspectedArchivePage : DevelopmentEvidenceClass
  sourceUsedToDesignCoding : DevelopmentEvidenceClass
  sourceUsedToDesignOutcomeVocabulary : DevelopmentEvidenceClass
  sourceUsedToDesignPanelMissingness : DevelopmentEvidenceClass
  corpusRecordExposedBeforeManifestFreeze : DevelopmentEvidenceClass

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
-- Materialised manifest-first split.
--
-- OccupyFiles.zip is now materialised and checksum-pinned by Corpus.
-- Manifest pins forty-five OWS records. During structural localisation the
-- first seven records had substantive content exposed, so they are forced to
-- development. Among the remaining still-uninspected records, every fifth
-- eligible record is protected as prospective holdout.
--
-- Protected OWS corpus indices:
--   12, 17, 22, 27, 32, 37, 42
-- corresponding to 2011-09-30, 10-09, 10-15, 10-20, 10-26, 11-01, 11-08.
--
-- This split is DASHI methodology, not an archival-source claim.
------------------------------------------------------------------------

record ProspectiveHeldOutPlan : Set where
  constructor prospectiveHeldOutPlan
  field
    sourceCorpusLabel : String
    packageSha256 : String
    splitManifestSha256 : String
    eligibilityRule : String
    selectionRule : String
    incidenceCodingRule : String
    outcomeCodingRule : String
    confoundVocabulary : String
    modelFamily : String
    corpusMaterialised : Bool
    corpusManifestFrozenBeforeSelection : Bool
    preFreezeInspectedRecordsForcedDevelopment : Bool
    heldOutAssignmentApplied : Bool
    codingProtocolFrozenBeforeHeldOutOutcomeExtraction : Bool
    modelFamilyFrozenBeforeOutcomeEvaluation : Bool
    assignmentImmutableAfterOutcomeInspection : Bool

open ProspectiveHeldOutPlan public

canonicalProspectiveHeldOutPlan : ProspectiveHeldOutPlan
canonicalProspectiveHeldOutPlan =
  prospectiveHeldOutPlan
    "Kinna-Prichard OccupyFiles corpus; Occupy Wall Street GA records"
    (Corpus.packageSha256 Corpus.canonicalOccupyFilesCorpusReceipt)
    Manifest.splitManifestSha256
    "use the forty-five parser-detected OWS records; records whose substantive contents were exposed before manifest freeze are development-only"
    "after excluding pre-freeze-inspected records, preserve canonical corpus order and assign every fifth still-uninspected eligible record to holdout; protected corpus indices are 12,17,22,27,32,37,42"
    "admit only explicit named-person-to-named-issue/topic associations; never attendance x agenda cross-products; collapse repeated same-person/same-issue utterances within meeting"
    "record only source-explicit duration, mediation, tabled/unresolved items, decisions, interruption/conflict observations; qualitative wording stays qualitative"
    "participant count, issue count, meeting type, external shock/context, source completeness, repeated participants"
    "predeclared candidate relation from incidence/control coordinates to independently coded burden outcomes"
    true
    true
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

    corpusMaterialisationPaid : Bool
    corpusManifestFreezePaid : Bool
    holdoutAssignmentPaid : Bool
    heldOutOutcomeExtractionPaid : Bool
    heldOutEvaluationPaid : Bool

    selectionRuleMustBeOutcomeBlindAndDeterministic : Bool
    codingProtocolMustBeFrozenBeforeHeldOutOutcomeExtraction : Bool
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
    "consumes the materialised OccupyFiles package and checksum-pinned forty-five-record OWS manifest; forces the seven records exposed before manifest freeze to development and freezes seven still-uninspected OWS records as outcome-blind prospective holdout"
    "materialisation, manifest freeze and assignment are paid, but held-out outcome extraction/evaluation are intentionally unpaid; protected substantive contents must remain uninspected until coding/model freeze and evaluation"
    "agda -i . DASHI/Governance/OccupyHeldOutMeetingValidationRegression.agda"
