module DASHI.Governance.OccupyOWSDevelopmentInterfaceProcessPanelRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyOWSDevelopmentInterfaceProcessPanelExact as Panel

rowCountPinned : Panel.rowCount Panel.canonicalInterfaceProcessRows ≡ 38
rowCountPinned = refl

reportBackAggregatePinned : Panel.totalReportBackParagraphs ≡ 27
reportBackAggregatePinned = refl

delegateAggregatePinned : Panel.totalDelegateParagraphs ≡ 6
delegateAggregatePinned = refl

spokesAggregatePinned : Panel.totalSpokesParagraphs ≡ 71
spokesAggregatePinned = refl

liaisonAggregatePinned : Panel.totalLiaisonParagraphs ≡ 4
liaisonAggregatePinned = refl

interGroupAggregatePinned : Panel.totalInterGroupParagraphs ≡ 2
interGroupAggregatePinned = refl

mediationAggregatePinned : Panel.totalMediationParagraphs ≡ 20
mediationAggregatePinned = refl

tabledAggregatePinned : Panel.totalTabledParagraphs ≡ 16
tabledAggregatePinned = refl

workingGroupAggregatePinned : Panel.totalWorkingGroupParagraphs ≡ 380
workingGroupAggregatePinned = refl

holdoutUnparsed :
  Panel.protectedHoldoutParsedForInterfaceMarkers Panel.canonicalInterfaceProcessBoundary ≡ false
holdoutUnparsed = refl

lexemesNotCosts :
  Panel.interfaceLexemesEqualFederationOverheadCosts Panel.canonicalInterfaceProcessBoundary ≡ false
lexemesNotCosts = refl
