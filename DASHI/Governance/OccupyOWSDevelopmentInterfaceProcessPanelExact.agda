module DASHI.Governance.OccupyOWSDevelopmentInterfaceProcessPanelExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.OccupyOWSManifestExact as Manifest

------------------------------------------------------------------------
-- DEVELOPMENT-ONLY OWS INTERFACE / ORGANISATIONAL PROCESS PANEL.
--
-- All coordinates are DASHI-derived paragraph-level lexical observables over
-- the 38 development records. Protected holdout records are excluded.
--
-- The vocabulary is chosen to expose possible empirical surfaces relevant to
-- the bolo counterfactual's boundary/delegation/unresolved-overhead terms:
-- report back/reportback, delegate/delegation, spokes, liaison, inter-group,
-- mediation, tabled, and working group.
--
-- These are text measurements only. A paragraph containing "report back" is
-- not definitionally one delegation event or one unit of overhead; "spokes"
-- is not a unique representative count; and "working group" is not by itself
-- a cross-community boundary interaction.
------------------------------------------------------------------------

record InterfaceProcessRow : Set where
  constructor interfaceProcessRow
  field
    manifestRecord : Manifest.OWSRecord
    reportBackParagraphCount : Nat
    delegateParagraphCount : Nat
    spokesParagraphCount : Nat
    liaisonParagraphCount : Nat
    interGroupParagraphCount : Nat
    mediationParagraphCount : Nat
    tabledParagraphCount : Nat
    workingGroupParagraphCount : Nat

open InterfaceProcessRow public

rowCount : List InterfaceProcessRow → Nat
rowCount [] = 0
rowCount (_ ∷ xs) = 1 + rowCount xs

row1 row2 row3 row4 row5 row6 row7 row8 row9 row10 row11
  row13 row14 row15 row16 row18 row19 row20 row21 row23 row24 row25 row26
  row28 row29 row30 row31 row33 row34 row35 row36 row38 row39 row40 row41
  row43 row44 row45 : InterfaceProcessRow

row1 = interfaceProcessRow Manifest.record1 0 0 0 0 0 0 0 0
row2 = interfaceProcessRow Manifest.record2 0 0 0 0 0 0 0 1
row3 = interfaceProcessRow Manifest.record3 0 0 0 0 0 0 0 0
row4 = interfaceProcessRow Manifest.record4 0 0 0 0 0 0 1 4
row5 = interfaceProcessRow Manifest.record5 0 0 0 0 0 0 0 9
row6 = interfaceProcessRow Manifest.record6 0 0 0 0 0 0 0 3
row7 = interfaceProcessRow Manifest.record7 0 0 0 0 0 0 0 2
row8 = interfaceProcessRow Manifest.record8 0 0 0 0 1 0 0 2
row9 = interfaceProcessRow Manifest.record9 0 0 0 0 0 0 1 3
row10 = interfaceProcessRow Manifest.record10 0 0 0 0 0 0 0 7
row11 = interfaceProcessRow Manifest.record11 0 0 0 1 0 0 0 10
row13 = interfaceProcessRow Manifest.record13 1 0 0 0 1 0 0 7
row14 = interfaceProcessRow Manifest.record14 1 0 0 1 0 1 0 11
row15 = interfaceProcessRow Manifest.record15 0 0 0 0 0 0 0 12
row16 = interfaceProcessRow Manifest.record16 0 0 1 2 0 0 0 8
row18 = interfaceProcessRow Manifest.record18 0 0 0 0 0 1 0 4
row19 = interfaceProcessRow Manifest.record19 4 1 3 0 0 0 0 19
row20 = interfaceProcessRow Manifest.record20 2 0 0 0 0 0 0 3
row21 = interfaceProcessRow Manifest.record21 4 0 0 0 0 2 0 10
row23 = interfaceProcessRow Manifest.record23 0 0 1 0 0 3 0 5
row24 = interfaceProcessRow Manifest.record24 4 0 0 0 0 0 0 17
row25 = interfaceProcessRow Manifest.record25 1 0 0 0 0 2 0 10
row26 = interfaceProcessRow Manifest.record26 0 0 1 0 0 0 2 12
row28 = interfaceProcessRow Manifest.record28 0 0 28 0 0 1 1 34
row29 = interfaceProcessRow Manifest.record29 1 0 1 0 0 0 0 10
row30 = interfaceProcessRow Manifest.record30 1 0 1 0 0 2 0 16
row31 = interfaceProcessRow Manifest.record31 0 0 0 0 0 4 1 12
row33 = interfaceProcessRow Manifest.record33 1 0 19 0 0 1 0 23
row34 = interfaceProcessRow Manifest.record34 0 0 0 0 0 1 2 5
row35 = interfaceProcessRow Manifest.record35 0 1 2 0 0 0 3 24
row36 = interfaceProcessRow Manifest.record36 0 0 0 0 0 0 0 6
row38 = interfaceProcessRow Manifest.record38 1 0 1 0 0 1 0 17
row39 = interfaceProcessRow Manifest.record39 0 0 7 0 0 0 1 5
row40 = interfaceProcessRow Manifest.record40 0 0 0 0 0 0 0 5
row41 = interfaceProcessRow Manifest.record41 3 0 0 0 0 0 3 15
row43 = interfaceProcessRow Manifest.record43 0 3 2 0 0 0 1 13
row44 = interfaceProcessRow Manifest.record44 1 1 1 0 0 0 0 22
row45 = interfaceProcessRow Manifest.record45 2 0 3 0 0 1 0 14

canonicalInterfaceProcessRows : List InterfaceProcessRow
canonicalInterfaceProcessRows =
  row1 ∷ row2 ∷ row3 ∷ row4 ∷ row5 ∷ row6 ∷ row7 ∷ row8 ∷ row9 ∷ row10 ∷ row11 ∷
  row13 ∷ row14 ∷ row15 ∷ row16 ∷ row18 ∷ row19 ∷ row20 ∷ row21 ∷ row23 ∷ row24 ∷ row25 ∷ row26 ∷
  row28 ∷ row29 ∷ row30 ∷ row31 ∷ row33 ∷ row34 ∷ row35 ∷ row36 ∷ row38 ∷ row39 ∷ row40 ∷ row41 ∷ row43 ∷ row44 ∷ row45 ∷ []

------------------------------------------------------------------------
-- Frozen extraction aggregates. These are parser-result receipts, not semantic
-- event counts.
------------------------------------------------------------------------

totalReportBackParagraphs : Nat
totalReportBackParagraphs = 27

totalDelegateParagraphs : Nat
totalDelegateParagraphs = 6

totalSpokesParagraphs : Nat
totalSpokesParagraphs = 71

totalLiaisonParagraphs : Nat
totalLiaisonParagraphs = 4

totalInterGroupParagraphs : Nat
totalInterGroupParagraphs = 2

totalMediationParagraphs : Nat
totalMediationParagraphs = 20

totalTabledParagraphs : Nat
totalTabledParagraphs = 16

totalWorkingGroupParagraphs : Nat
totalWorkingGroupParagraphs = 380

record InterfaceProcessBoundary : Set where
  constructor interfaceProcessBoundary
  field
    protectedHoldoutParsedForInterfaceMarkers : Bool
    lexicalInterfaceSurfacePresent : Bool
    boundaryCalibrationObservableSurfacePresent : Bool
    delegationCalibrationObservableSurfacePresent : Bool
    unresolvedCalibrationObservableSurfacePresent : Bool
    interfaceLexemesEqualFederationOverheadCosts : Bool
    reportBackParagraphEqualsDelegationEvent : Bool
    spokesParagraphEqualsUniqueRepresentative : Bool
    workingGroupParagraphEqualsBoundaryInteraction : Bool
    lexicalCountsIdentifyCostCoefficientOrBound : Bool

open InterfaceProcessBoundary public

canonicalInterfaceProcessBoundary : InterfaceProcessBoundary
canonicalInterfaceProcessBoundary =
  interfaceProcessBoundary
    false
    true
    true
    true
    true
    false
    false
    false
    false
    false

canonicalOWSDevelopmentInterfaceProcessReceipt : GenericReceipt.GenericReceipt
canonicalOWSDevelopmentInterfaceProcessReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "OWS development-only interface-process lexical panel"
    "DASHI.Governance.OccupyOWSDevelopmentInterfaceProcessPanelExact"
    "canonicalInterfaceProcessBoundary"
    "adds a thirty-eight-record development-only lexical surface for report-back, delegate, spokes, liaison, inter-group, mediation, tabled and working-group language, demonstrating that the archived corpus contains observable process vocabulary relevant to boundary, delegation and unresolved-dependency calibration sockets"
    "the lexical rows do not identify semantic interface events, unique representatives, coordination costs or statistical bounds; protected holdout records remain excluded and any mapping from these text observables into bolo cost terms still requires a separately justified measurement model"
    "agda -i . DASHI/Governance/OccupyOWSDevelopmentInterfaceProcessPanelRegression.agda"
