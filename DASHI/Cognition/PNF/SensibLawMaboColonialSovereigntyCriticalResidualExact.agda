module DASHI.Cognition.PNF.SensibLawMaboColonialSovereigntyCriticalResidualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboBrennanDawsonIssueResidualLiveExact as Mabo
import DASHI.Cognition.PNF.SensibLawMaboSovereigntyRecognitionRelationalBraidExact as Earlier
import DASHI.Governance.SituatedConstituency as Situated

------------------------------------------------------------------------
-- Critical sovereignty residual.
--
-- This owner prevents the court-internal premise that Crown sovereignty is
-- legally settled from becoming a world-level theorem that Indigenous
-- sovereignty was ceded, extinguished, or legitimately transferred.
--
-- It also prevents recognition of Native Title from being promoted into a
-- theorem that sovereignty, dispossession, land return, or material repair have
-- thereby been resolved.
------------------------------------------------------------------------

data SovereigntyFrame : Set where
  australianCourtInternalFrame : SovereigntyFrame
  indigenousSovereigntyFrame : SovereigntyFrame
  decolonialCriticalFrame : SovereigntyFrame
  reparativeJusticeFrame : SovereigntyFrame


data ColonialSovereigntyCoordinate : Set where
  crownLegalSovereigntyPremise : ColonialSovereigntyCoordinate
  indigenousSovereigntyContinuity : ColonialSovereigntyCoordinate
  cessionStatus : ColonialSovereigntyCoordinate
  colonialAcquisitionLegitimacy : ColonialSovereigntyCoordinate
  landDispossession : ColonialSovereigntyCoordinate
  nativeTitleRecognition : ColonialSovereigntyCoordinate
  indigenousSovereigntyRecognition : ColonialSovereigntyCoordinate
  politicalRepresentationRecognition : ColonialSovereigntyCoordinate
  apologyOrAcknowledgement : ColonialSovereigntyCoordinate
  treatyOrAgreement : ColonialSovereigntyCoordinate
  landRestitutionOrReturn : ColonialSovereigntyCoordinate
  materialReparation : ColonialSovereigntyCoordinate
  institutionalRepair : ColonialSovereigntyCoordinate


data PropositionLayer : Set where
  courtHoldingOrPremiseLayer : PropositionLayer
  affectedCommunityClaimLayer : PropositionLayer
  historicalEvidenceLayer : PropositionLayer
  criticalInterpretationLayer : PropositionLayer
  normativeDemandLayer : PropositionLayer
  unresolvedLayer : PropositionLayer


record FramedSovereigntyProposition : Set where
  constructor framedSovereigntyProposition
  field
    issueReference : String
    propositionReference : String
    frame : SovereigntyFrame
    coordinate : ColonialSovereigntyCoordinate
    layer : PropositionLayer
    sourceReference : String
    represented : Bool
    representedIsTrue : represented ≡ true
    worldTruthAutomaticallyAdmitted : Bool
    worldTruthAutomaticallyAdmittedIsFalse : worldTruthAutomaticallyAdmitted ≡ false
    crossFrameAuthorityAutomaticallyTransported : Bool
    crossFrameAuthorityAutomaticallyTransportedIsFalse : crossFrameAuthorityAutomaticallyTransported ≡ false
open FramedSovereigntyProposition public

------------------------------------------------------------------------
-- Court-internal proposition versus independently contestable sovereignty
-- propositions.
------------------------------------------------------------------------

crownSovereigntyCourtPremise : FramedSovereigntyProposition
crownSovereigntyCourtPremise = framedSovereigntyProposition
  "Mabo (No 2) sovereignty architecture"
  "Australian-law reasons proceed on Crown acquisition/settlement of sovereignty as a court-internal legal premise"
  australianCourtInternalFrame
  crownLegalSovereigntyPremise
  courtHoldingOrPremiseLayer
  "Mabo (No 2) primary judgment / Australian-law doctrinal frame"
  true refl false refl false refl

sovereigntyNeverCededCriticalClaim : FramedSovereigntyProposition
sovereigntyNeverCededCriticalClaim = framedSovereigntyProposition
  "Mabo (No 2) sovereignty architecture"
  "Indigenous sovereignty was not ceded: represented here as an affected-community/decolonial claim requiring its own source receipts rather than being erased by the Crown-law frame"
  indigenousSovereigntyFrame
  cessionStatus
  affectedCommunityClaimLayer
  "affected-community / Indigenous sovereignty source receipt required for proposition-level attribution"
  true refl false refl false refl

colonialLegitimacyRemainsOpen : FramedSovereigntyProposition
colonialLegitimacyRemainsOpen = framedSovereigntyProposition
  "Mabo (No 2) sovereignty architecture"
  "Crown legal effectiveness inside Australian law does not itself establish the legitimacy of colonial acquisition"
  decolonialCriticalFrame
  colonialAcquisitionLegitimacy
  criticalInterpretationLayer
  "critical bridge over court-internal sovereignty premise; no automatic historical/world-truth promotion"
  true refl false refl false refl

nativeTitleRecognitionProposition : FramedSovereigntyProposition
nativeTitleRecognitionProposition = framedSovereigntyProposition
  "Mabo (No 2) sovereignty architecture"
  "Native-title recognition is a distinct legal coordinate from Indigenous-sovereignty recognition and from land/material repair"
  australianCourtInternalFrame
  nativeTitleRecognition
  criticalInterpretationLayer
  "Mabo Native Title recognition lane + critical cross-coordinate firewall"
  true refl false refl false refl

------------------------------------------------------------------------
-- Repair/remedy fibres remain distinct.
------------------------------------------------------------------------

data ReparativeResponseKind : Set where
  symbolicRecognition : ReparativeResponseKind
  formalApology : ReparativeResponseKind
  consultativeRepresentation : ReparativeResponseKind
  treatyMaking : ReparativeResponseKind
  sovereigntyRecognitionResponse : ReparativeResponseKind
  landReturnResponse : ReparativeResponseKind
  materialReparationResponse : ReparativeResponseKind
  institutionalReformResponse : ReparativeResponseKind


responseCoordinate : ReparativeResponseKind → ColonialSovereigntyCoordinate
responseCoordinate symbolicRecognition = politicalRepresentationRecognition
responseCoordinate formalApology = apologyOrAcknowledgement
responseCoordinate consultativeRepresentation = politicalRepresentationRecognition
responseCoordinate treatyMaking = treatyOrAgreement
responseCoordinate sovereigntyRecognitionResponse = indigenousSovereigntyRecognition
responseCoordinate landReturnResponse = landRestitutionOrReturn
responseCoordinate materialReparationResponse = materialReparation
responseCoordinate institutionalReformResponse = institutionalRepair

record ReparativeResidualState : Set where
  constructor reparativeResidualState
  field
    nativeTitleRecognitionClosedForSourceMap : Bool
    sovereigntyRecognitionClosed : Bool
    cessionStatusClosed : Bool
    colonialLegitimacyClosed : Bool
    landRestitutionClosed : Bool
    materialReparationClosed : Bool
    institutionalRepairClosed : Bool
    stateReference : String
open ReparativeResidualState public

postMaboCriticalResidual : ReparativeResidualState
postMaboCriticalResidual = reparativeResidualState
  true
  false
  false
  false
  false
  false
  false
  "Mabo may close a bounded Native Title recognition source-map consumer while sovereignty/cession/legitimacy/land-return/material-repair fibres remain independently open"

------------------------------------------------------------------------
-- Intersectional/situated cross-pollination: land and coloniality cannot be
-- erased simply because the doctrinal Native Title coordinate is populated.
------------------------------------------------------------------------

criticalAxes : List Situated.GovernanceAxis
criticalAxes =
  Situated.landAxis
  ∷ Situated.colonialityAxis
  ∷ Situated.displacementAxis
  ∷ Situated.ethnicityAxis
  ∷ Situated.institutionalAccessAxis
  ∷ []

record CriticalAxisBoundary : Set where
  constructor criticalAxisBoundary
  field
    axes : List Situated.GovernanceAxis
    landAxisEraseableAfterNativeTitleRecognition : Bool
    landAxisEraseableAfterNativeTitleRecognitionIsFalse : landAxisEraseableAfterNativeTitleRecognition ≡ false
    colonialityAxisEraseableAfterNativeTitleRecognition : Bool
    colonialityAxisEraseableAfterNativeTitleRecognitionIsFalse : colonialityAxisEraseableAfterNativeTitleRecognition ≡ false
    affectedCommunityArticulationReplaceableByCourtFrame : Bool
    affectedCommunityArticulationReplaceableByCourtFrameIsFalse : affectedCommunityArticulationReplaceableByCourtFrame ≡ false
open CriticalAxisBoundary public

canonicalCriticalAxisBoundary : CriticalAxisBoundary
canonicalCriticalAxisBoundary = criticalAxisBoundary
  criticalAxes
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- Compatibility boundary for the earlier `mereChangeOfSovereignty` label.
------------------------------------------------------------------------

data EarlierLabelStatus : Set where
  deprecatedAsPrimaryCriticalDescription : EarlierLabelStatus
  retainedOnlyForCourtInternalCompatibility : EarlierLabelStatus


mereChangeLabelStatus : EarlierLabelStatus
mereChangeLabelStatus = retainedOnlyForCourtInternalCompatibility

courtInternalCompatibilityOnly :
  Earlier.transitionEffect Earlier.mereChangeOfSovereignty
  ≡ Earlier.continuityNotDisplacedByTransitionAlone
courtInternalCompatibilityOnly = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data CrownLegalPremiseProvesIndigenousCession : Set where
data CrownLegalPremiseProvesColonialLegitimacy : Set where
data NativeTitleRecognitionProvesSovereigntyRecognition : Set where
data NativeTitleRecognitionRepairsDispossession : Set where
data FormalApologyEqualsLandRestitution : Set where
data ConsultativeRecognitionEqualsSovereigntyRecognition : Set where
data PoliticalRecognitionEqualsLandReturn : Set where
data RejectionOfTerraNulliusCompletesDecolonisation : Set where
data CourtFrameErasesAffectedCommunityFrame : Set where

crownPremiseDoesNotProveCession : CrownLegalPremiseProvesIndigenousCession → ⊥
crownPremiseDoesNotProveCession ()
crownPremiseDoesNotProveLegitimacy : CrownLegalPremiseProvesColonialLegitimacy → ⊥
crownPremiseDoesNotProveLegitimacy ()
nativeTitleDoesNotProveSovereigntyRecognition : NativeTitleRecognitionProvesSovereigntyRecognition → ⊥
nativeTitleDoesNotProveSovereigntyRecognition ()
nativeTitleDoesNotRepairDispossessionByItself : NativeTitleRecognitionRepairsDispossession → ⊥
nativeTitleDoesNotRepairDispossessionByItself ()
apologyDoesNotEqualLandRestitution : FormalApologyEqualsLandRestitution → ⊥
apologyDoesNotEqualLandRestitution ()
consultativeRecognitionDoesNotEqualSovereigntyRecognition : ConsultativeRecognitionEqualsSovereigntyRecognition → ⊥
consultativeRecognitionDoesNotEqualSovereigntyRecognition ()
politicalRecognitionDoesNotEqualLandReturn : PoliticalRecognitionEqualsLandReturn → ⊥
politicalRecognitionDoesNotEqualLandReturn ()
terraNulliusRejectionDoesNotCompleteDecolonisation : RejectionOfTerraNulliusCompletesDecolonisation → ⊥
terraNulliusRejectionDoesNotCompleteDecolonisation ()
courtFrameDoesNotEraseAffectedCommunityFrame : CourtFrameErasesAffectedCommunityFrame → ⊥
courtFrameDoesNotEraseAffectedCommunityFrame ()
