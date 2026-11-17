module DASHI.Governance.OccupyOWSDevelopmentTextProcessPanelRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.OccupyOWSDevelopmentTextProcessPanelExact as Panel

thirtyEightDevelopmentRows : Panel.rowCount Panel.canonicalTextProcessRows ≡ 38
thirtyEightDevelopmentRows = refl

record3ConsensusParagraphsPinned : Panel.consensusParagraphCount Panel.row3 ≡ 3
record3ConsensusParagraphsPinned = refl

record28VolumePinned : Panel.normalizedWordCount Panel.row28 ≡ 14678
record28VolumePinned = refl

record43ProposalParagraphsPinned : Panel.proposalParagraphCount Panel.row43 ≡ 72
record43ProposalParagraphsPinned = refl

record44BlockParagraphsPinned : Panel.blockParagraphCount Panel.row44 ≡ 47
record44BlockParagraphsPinned = refl

record44AnonMarkersPinned : Panel.anonymizationMarkerCount Panel.row44 ≡ 135
record44AnonMarkersPinned = refl

lexemeCountIsNotDecisionCount : Panel.consensusParagraphCountEqualsConsensusDecisionCount Panel.canonicalTextProcessBoundary ≡ false
lexemeCountIsNotDecisionCount = refl

holdoutsAreExcluded : Panel.protectedHoldoutParsedForProcessMarkers Panel.canonicalTextProcessBoundary ≡ false
holdoutsAreExcluded = refl
