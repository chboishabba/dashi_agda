module DASHI.Governance.OccupyOWSDevelopmentTextProcessPanelExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.OccupyOWSManifestExact as Manifest

------------------------------------------------------------------------
-- DEVELOPMENT-ONLY OWS TEXT/PROCESS OBSERVABLE PANEL.
--
-- All fields below are DASHI-derived textual measurements over development
-- records only. They are deliberately lexical rather than semantic:
--   normalizedWordCount: tokenizer output;
--   consensusParagraphCount: paragraphs containing the lexeme "consensus";
--   blockParagraphCount: paragraphs containing block/blocks/blocking;
--   proposalParagraphCount: paragraphs containing proposal/proposed;
--   anonymizationMarkerCount: literal occurrences of ***.
--
-- These are reproducible text observables, not counts of actual decisions,
-- blockers, proposals, participants, or political authority.
------------------------------------------------------------------------

record TextProcessRow : Set where
  constructor textProcessRow
  field
    manifestRecord : Manifest.OWSRecord
    normalizedWordCount : Nat
    consensusParagraphCount : Nat
    blockParagraphCount : Nat
    proposalParagraphCount : Nat
    anonymizationMarkerCount : Nat

open TextProcessRow public

rowCount : List TextProcessRow → Nat
rowCount [] = 0
rowCount (_ ∷ xs) = 1 + rowCount xs

row1 = textProcessRow Manifest.record1 869 0 0 0 4
row2 = textProcessRow Manifest.record2 152 0 0 0 2
row3 = textProcessRow Manifest.record3 182 3 0 0 0
row4 = textProcessRow Manifest.record4 2049 1 0 2 0
row5 = textProcessRow Manifest.record5 4180 1 2 1 32
row6 = textProcessRow Manifest.record6 1148 5 5 7 12
row7 = textProcessRow Manifest.record7 1634 0 0 1 7
row8 = textProcessRow Manifest.record8 2229 2 1 2 5
row9 = textProcessRow Manifest.record9 2172 1 0 1 15
row10 = textProcessRow Manifest.record10 6179 5 3 9 32
row11 = textProcessRow Manifest.record11 6640 3 12 5 30
row13 = textProcessRow Manifest.record13 2418 0 0 0 23
row14 = textProcessRow Manifest.record14 7077 0 0 7 68
row15 = textProcessRow Manifest.record15 4849 7 12 12 43
row16 = textProcessRow Manifest.record16 5019 4 5 5 49
row18 = textProcessRow Manifest.record18 3605 1 2 10 24
row19 = textProcessRow Manifest.record19 4819 3 1 6 58
row20 = textProcessRow Manifest.record20 3301 2 6 6 20
row21 = textProcessRow Manifest.record21 4156 2 7 16 6
row23 = textProcessRow Manifest.record23 2186 5 0 6 12
row24 = textProcessRow Manifest.record24 5367 3 1 4 59
row25 = textProcessRow Manifest.record25 4545 8 6 15 32
row26 = textProcessRow Manifest.record26 5337 4 0 13 8
row28 = textProcessRow Manifest.record28 14678 24 20 65 17
row29 = textProcessRow Manifest.record29 3578 2 0 2 40
row30 = textProcessRow Manifest.record30 5275 8 8 32 47
row31 = textProcessRow Manifest.record31 6797 11 11 43 21
row33 = textProcessRow Manifest.record33 8299 27 27 34 38
row34 = textProcessRow Manifest.record34 372 2 1 4 4
row35 = textProcessRow Manifest.record35 12288 15 6 31 40
row36 = textProcessRow Manifest.record36 496 1 0 0 17
row38 = textProcessRow Manifest.record38 2708 1 1 3 21
row39 = textProcessRow Manifest.record39 8302 5 19 32 51
row40 = textProcessRow Manifest.record40 2673 0 1 2 32
row41 = textProcessRow Manifest.record41 6497 9 6 44 51
row43 = textProcessRow Manifest.record43 14643 31 26 72 99
row44 = textProcessRow Manifest.record44 15954 32 47 64 135
row45 = textProcessRow Manifest.record45 9634 3 7 1 82

canonicalTextProcessRows : List TextProcessRow
canonicalTextProcessRows =
  row1 ∷ row2 ∷ row3 ∷ row4 ∷ row5 ∷ row6 ∷ row7 ∷ row8 ∷ row9 ∷ row10 ∷ row11 ∷
  row13 ∷ row14 ∷ row15 ∷ row16 ∷ row18 ∷ row19 ∷ row20 ∷ row21 ∷ row23 ∷ row24 ∷ row25 ∷ row26 ∷
  row28 ∷ row29 ∷ row30 ∷ row31 ∷ row33 ∷ row34 ∷ row35 ∷ row36 ∷ row38 ∷ row39 ∷ row40 ∷ row41 ∷ row43 ∷ row44 ∷ row45 ∷ []

record TextProcessBoundary : Set where
  constructor textProcessBoundary
  field
    consensusParagraphCountEqualsConsensusDecisionCount : Bool
    blockParagraphCountEqualsDistinctBlockingParticipants : Bool
    proposalParagraphCountEqualsDistinctProposals : Bool
    anonymizationMarkerCountEqualsParticipantCount : Bool
    wordCountEqualsMeetingDuration : Bool
    protectedHoldoutParsedForProcessMarkers : Bool
    developmentLexicalPanelPaid : Bool

open TextProcessBoundary public

canonicalTextProcessBoundary : TextProcessBoundary
canonicalTextProcessBoundary =
  textProcessBoundary false false false false false false true

canonicalTextProcessReceipt : GenericReceipt.GenericReceipt
canonicalTextProcessReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "OWS development-only lexical process panel"
    "DASHI.Governance.OccupyOWSDevelopmentTextProcessPanelExact"
    "canonicalTextProcessBoundary"
    "records reproducible normalized word counts and paragraph-level consensus/block/proposal lexeme counts plus literal anonymization-marker counts for thirty-eight development OWS records"
    "lexical observables are DASHI-derived text measurements rather than semantic counts of decisions, blocks, proposals or participants; protected holdout records are excluded from process-marker parsing"
    "agda -i . DASHI/Governance/OccupyOWSDevelopmentTextProcessPanelRegression.agda"
