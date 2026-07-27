module DASHI.Biology.EcologyOfDataHyperfabricBridge where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources
import DASHI.Biology.OEFMultiFibreFeedbackHyperfabric as OEF

------------------------------------------------------------------------
-- Ecology-of-data / hyperfabric bridge.
--
-- The Finn/Brown paper supplies an eco-behavioural correction to flat coding:
-- person and place are co-constituted, and analysis should retain system
-- edges, affordances, minutiae, value flows, and pedagogical curation.

data CustodianResponsibility : Set where
  mapSystemEdgesAndIntersections : CustodianResponsibility
  analyseAffordancesOfPlace : CustodianResponsibility
  attendToMinutiaeAndEffort : CustodianResponsibility
  considerFlowsOfValue : CustodianResponsibility
  learnWithAndCurateData : CustodianResponsibility

canonicalCustodianResponsibilities : List CustodianResponsibility
canonicalCustodianResponsibilities =
  mapSystemEdgesAndIntersections
  ∷ analyseAffordancesOfPlace
  ∷ attendToMinutiaeAndEffort
  ∷ considerFlowsOfValue
  ∷ learnWithAndCurateData
  ∷ []

responsibilityName : CustodianResponsibility → String
responsibilityName mapSystemEdgesAndIntersections =
  "map system edges and intersections"
responsibilityName analyseAffordancesOfPlace =
  "analyse affordances of place"
responsibilityName attendToMinutiaeAndEffort =
  "attend to minutiae and effort after meaning and value"
responsibilityName considerFlowsOfValue =
  "consider flows of value"
responsibilityName learnWithAndCurateData =
  "learn with and curate data pedagogically"

record EcologicalFeedbackCell : Set where
  constructor mkEcologicalFeedbackCell
  field
    studentSurface : String
    placeSurface : String
    affordanceSurface : String
    activitySurface : String
    valueFlowSurface : String
    timeSurface : String
    feedbackProjection : OEF.FeedbackHypervoxel
    personPlaceCoConstituted : Bool
    personPlaceCoConstitutedIsTrue : personPlaceCoConstituted ≡ true
    projectionNotWholeEcology : Bool
    projectionNotWholeEcologyIsTrue : projectionNotWholeEcology ≡ true

open EcologicalFeedbackCell public

canonicalEcologicalFeedbackCell : EcologicalFeedbackCell
canonicalEcologicalFeedbackCell =
  mkEcologicalFeedbackCell
    "situated student"
    "course / home / platform / institution place field"
    "available and unavailable learning affordances"
    "student activity and effort"
    "flows of attention, labour, care, recognition and institutional benefit"
    "semester-local observation time"
    OEF.canonicalFeedbackHypervoxel
    true refl
    true refl

record CustodianshipGate : Set where
  constructor mkCustodianshipGate
  field
    contextRetained : Bool
    contextRetainedIsTrue : contextRetained ≡ true
    participantAgencyRetained : Bool
    participantAgencyRetainedIsTrue : participantAgencyRetained ≡ true
    dataOwnershipNotAssumed : Bool
    dataOwnershipNotAssumedIsTrue : dataOwnershipNotAssumed ≡ true
    valueExtractionAudited : Bool
    valueExtractionAuditedIsTrue : valueExtractionAudited ≡ true
    codingDoesNotEraseMinutiae : Bool
    codingDoesNotEraseMinutiaeIsTrue : codingDoesNotEraseMinutiae ≡ true
    curationOpenToContest : Bool
    curationOpenToContestIsTrue : curationOpenToContest ≡ true

open CustodianshipGate public

canonicalCustodianshipGate : CustodianshipGate
canonicalCustodianshipGate =
  mkCustodianshipGate
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

record EcologyOfDataHyperfabricBridge : Set where
  constructor mkEcologyOfDataHyperfabricBridge
  field
    sourcePaper : Sources.PaperReference
    sourcePaperIsCanonical : sourcePaper ≡ Sources.ecologyOfDataPaper
    sourceFeedbackFormalisation : OEF.OEFMultiFibreFeedbackHyperfabric
    sourceFeedbackFormalisationIsCanonical :
      sourceFeedbackFormalisation ≡ OEF.canonicalOEFMultiFibreFeedbackHyperfabric
    responsibilities : List CustodianResponsibility
    responsibilitiesAreCanonical :
      responsibilities ≡ canonicalCustodianResponsibilities
    ecologicalCell : EcologicalFeedbackCell
    ecologicalCellIsCanonical : ecologicalCell ≡ canonicalEcologicalFeedbackCell
    governance : CustodianshipGate
    governanceIsCanonical : governance ≡ canonicalCustodianshipGate
    feedbackIsEcologicalEvent : Bool
    feedbackIsEcologicalEventIsTrue : feedbackIsEcologicalEvent ≡ true
    codingNotWholeAnalysis : Bool
    codingNotWholeAnalysisIsTrue : codingNotWholeAnalysis ≡ true
    noContextFreeMeaning : Bool
    noContextFreeMeaningIsTrue : noContextFreeMeaning ≡ true
    noCustodianInfallibility : Bool
    noCustodianInfallibilityIsTrue : noCustodianInfallibility ≡ true
    reading : String

open EcologyOfDataHyperfabricBridge public

canonicalEcologyOfDataHyperfabricBridge : EcologyOfDataHyperfabricBridge
canonicalEcologyOfDataHyperfabricBridge =
  mkEcologyOfDataHyperfabricBridge
    Sources.ecologyOfDataPaper refl
    OEF.canonicalOEFMultiFibreFeedbackHyperfabric refl
    canonicalCustodianResponsibilities refl
    canonicalEcologicalFeedbackCell refl
    canonicalCustodianshipGate refl
    true refl
    true refl
    true refl
    true refl
    "The end-of-course comment is retained as an ecological event and local projection within a person-place hyperfabric. Custodianship requires system-edge, affordance, minutiae, value-flow and pedagogical-curation audits; it does not turn context-rich interpretation into infallible or complete meaning."
