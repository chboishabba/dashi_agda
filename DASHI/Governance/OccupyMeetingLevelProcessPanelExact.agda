module DASHI.Governance.OccupyMeetingLevelProcessPanelExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.OccupyOWSDevelopmentDurationPanelExact as OWSDuration
import DASHI.Governance.OccupyOWSDevelopmentTextProcessPanelExact as OWSText
import DASHI.Governance.OccupyOWSDevelopmentInterfaceProcessPanelExact as OWSInterface
import DASHI.Governance.OccupyMeetingPanelExact as LibraryPanel
import DASHI.Governance.OccupyPseudonymousNetworkFeaturesExact as Network

------------------------------------------------------------------------
-- MEETING-LEVEL PROCESS PANEL, SOURCE-REGIME AWARE.
--
-- The quantitative target is meeting-level process, not a named participant
-- matrix. The curated OWS GA corpus and the People's Library web archive are
-- retained as distinct documentary regimes. They may be compared only through
-- explicitly common observables or through a model carrying source regime.
------------------------------------------------------------------------

data SourceRegime : Set where
  curatedOWSGeneralAssemblyCorpus : SourceRegime
  peoplesLibraryWorkingGroupWebArchive : SourceRegime

record MeetingLevelProcessPanel : Set where
  constructor meetingLevelProcessPanel
  field
    owsDevelopmentTextRows : List OWSText.TextProcessRow
    owsDevelopmentInterfaceRows : List OWSInterface.InterfaceProcessRow
    owsDevelopmentDurationRows : List OWSDuration.OWSDurationRow
    librarySourceExplicitRows : List LibraryPanel.MeetingPanelRow
    libraryPseudonymousNetworkRows : List Network.NetworkFeatureRow
    owsDevelopmentRecordCount : Nat
    owsInterfaceProcessRowCount : Nat
    libraryNetworkMeetingCount : Nat

open MeetingLevelProcessPanel public

canonicalMeetingLevelProcessPanel : MeetingLevelProcessPanel
canonicalMeetingLevelProcessPanel =
  meetingLevelProcessPanel
    OWSText.canonicalTextProcessRows
    OWSInterface.canonicalInterfaceProcessRows
    OWSDuration.canonicalOWSDurationRows
    LibraryPanel.canonicalDevelopmentPanel
    Network.canonicalNetworkFeatureRows
    38
    38
    5

record MeetingLevelProcessBoundary : Set where
  constructor meetingLevelProcessBoundary
  field
    meetingLevelProcessIsPrimaryAnalysisTarget : Bool
    completeNamedParticipantIssueMatrixIsAnalysisTarget : Bool
    pseudonymousNetworkFeaturesMayAugmentPanel : Bool
    interfaceProcessLexicalSurfaceIncluded : Bool
    interfaceLexemesDefinitionallyEqualOverheadCosts : Bool
    sourceRegimeIndicatorRequired : Bool
    crossSourceParticipantIdentityAutomaticallyJoined : Bool
    anonymousOWSMarkersReverseEngineered : Bool
    peoplesLibraryPseudonymsPublishedAsNames : Bool
    sameFieldNameMakesDocumentaryRegimesEquivalent : Bool
    missingCoordinateTreatedAsZero : Bool
    crossSourcePoolingWithoutDocumentaryModelAllowed : Bool

open MeetingLevelProcessBoundary public

canonicalMeetingLevelProcessBoundary : MeetingLevelProcessBoundary
canonicalMeetingLevelProcessBoundary =
  meetingLevelProcessBoundary
    true
    false
    true
    true
    false
    true
    false
    false
    false
    false
    false
    false

canonicalMeetingLevelProcessPanelReceipt : GenericReceipt.GenericReceipt
canonicalMeetingLevelProcessPanelReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "source-regime-aware Occupy meeting-level process panel"
    "DASHI.Governance.OccupyMeetingLevelProcessPanelExact"
    "canonicalMeetingLevelProcessBoundary"
    "sets meeting-level process as the primary quantitative target, retaining thirty-eight development OWS lexical rows, thirty-eight development interface-process rows, six OWS duration rows, the source-explicit People's Library panel and five pseudonymous People's Library network-feature rows while preserving documentary regime"
    "a complete named participant-by-issue matrix is not an analysis target; interface lexemes are not overhead costs, source-anonymous markers are not reverse engineered, cross-source person identity is not joined automatically, missingness is not zero and common field names do not license silent pooling"
    "agda -i . DASHI/Governance/OccupyMeetingLevelProcessPanelRegression.agda"
