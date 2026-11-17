module DASHI.Governance.OccupyPanelMissingnessAuditExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- MEETING-PANEL MISSINGNESS / DOCUMENTARY-COMPLETENESS AUDIT.
------------------------------------------------------------------------

record PanelMissingnessAudit : Set where
  constructor panelMissingnessAudit
  field
    owsDevelopmentRecordCount : Nat
    owsLexicalObservedCount : Nat
    owsInterfaceLexicalObservedCount : Nat
    owsDurationObservedCount : Nat
    peoplesLibrarySourceExplicitPanelRows : Nat
    peoplesLibraryNetworkFeatureRows : Nat
    peoplesLibraryCompletenessAuditedRows : Nat

open PanelMissingnessAudit public

canonicalMissingnessAudit : PanelMissingnessAudit
canonicalMissingnessAudit = panelMissingnessAudit 38 38 38 6 7 5 0

record MissingnessBoundary : Set where
  constructor missingnessBoundary
  field
    missingDurationImputedAsZero : Bool
    absentNamedParticipantCountImputedFromAnonymisationMarkers : Bool
    missingnessAssumedIgnorable : Bool
    completeCaseSubsetAssumedRepresentative : Bool
    documentaryCompletenessAssumedFromLongTranscript : Bool
    sourceRegimeExplainsAllMissingness : Bool
    sourceRegimeMustRemainExplicit : Bool
    missingnessPatternIsAnalysisCoordinate : Bool

open MissingnessBoundary public

canonicalMissingnessBoundary : MissingnessBoundary
canonicalMissingnessBoundary =
  missingnessBoundary false false false false false false true true

canonicalMissingnessAuditReceipt : GenericReceipt.GenericReceipt
canonicalMissingnessAuditReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Occupy meeting-panel missingness and documentary-completeness audit"
    "DASHI.Governance.OccupyPanelMissingnessAuditExact"
    "canonicalMissingnessBoundary"
    "pins thirty-eight development OWS general lexical rows, thirty-eight development OWS interface-process lexical rows, six source-explicit OWS duration rows, seven source-explicit People's Library panel rows, five People's Library network-feature rows, and zero rows currently carrying a documentary-completeness proof"
    "missing values are not zero or reverse-engineered from anonymisation markers; missingness is not assumed ignorable, complete cases are not assumed representative, transcript length does not prove documentary completeness, and source regime remains an explicit analysis coordinate"
    "agda -i . DASHI/Governance/OccupyPanelMissingnessAuditRegression.agda"
