module DASHI.Culture.AmyEskridgeBemOriginalProtocolCorrespondenceWeldExact where

-- DIRECT ORIGINAL AUTHOR ↔ CRITIC CORRESPONDENCE, 5–15 Jan 2018.
-- https://replicationindex.com/2018/01/20/bemcorrespondence/
-- Source origin is a dated BLOG TRANSCRIPTION of correspondence, not a
-- verified original attachment/dataset. The transcript contains author
-- replies and explicit published-test-vs-reanalysis clarifications.
-- Avoid presenting a disputed calculation as a proven reporting error.
--
-- The archived email text supports:
--  (1) Bem says 2011 Experiments 5 and 6 were a 100-session negative-
--      only protocol, plus a distinct 150-session expanded protocol;
--  (2) Schimmack initially saw divergent t-tests for Exp 6, then on
--      12 January acknowledged he had used a paired control-difference
--      t-test instead of Bem's one-sample test against fixed 50%;
--  (3) Bem confirms the 50% analysis and the original Exp 6 protocol
--      CHANGED across chronological ranges 1..91, 92..110, 111..150;
--  (4) Bem's 15 January table explicitly splits Exp 1 into 40+60
--      participants in 2006. None of these records independently proves
--      preregistered effect moderation or improper selection.
-- Obtain exact original datafiles before reproducing any participant t.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.AmyEskridgeBemSteelmanRealisticIdentifiabilityExact as Bem

record ProtocolEra : Set where
  constructor protocol-era
  field
    experimentNumber : Nat
    firstSession : Nat
    lastSession : Nat
    sampleCount : Nat
    sourceSays : String
open ProtocolEra public

bemExp1First40 : ProtocolEra
bemExp1First40 = protocol-era 1 1 40 40
  "Bem 15 Jan 2018 author table: Experiment 1 2006 first 40 participants"

bemExp1Later60 : ProtocolEra
bemExp1Later60 = protocol-era 1 41 100 60
  "Bem 15 Jan 2018 author table: Experiment 1 2006 remaining 60 participants"

bemExp6First91 : ProtocolEra
bemExp6First91 = protocol-era 6 1 91 91
  "2002 16 negative / 16 erotic / 16 neutral critical picture exposures per participant"

bemExp6Next19 : ProtocolEra
bemExp6Next19 = protocol-era 6 92 110 19
  "2002 12 negative / 12 stronger erotic / 24 neutral picture exposures"

bemExp6Final40 : ProtocolEra
bemExp6Final40 = protocol-era 6 111 150 40
  "2002 15 negative / 15 stronger erotic / 30 neutral picture exposures"

bemOriginalFirstExp1PhasesTotal :
  sampleCount bemExp1First40 + sampleCount bemExp1Later60 ≡ 100
bemOriginalFirstExp1PhasesTotal = refl

bemOriginalExp6PhasesTotal :
  sampleCount bemExp6First91 +
  sampleCount bemExp6Next19 +
  sampleCount bemExp6Final40 ≡ 150
bemOriginalExp6PhasesTotal = refl

data AnalysisChoice : Set where
  oneSampleAgainstFixedHalf : AnalysisChoice
  pairedAgainstNeutralControl : AnalysisChoice

record CorrespondenceAnalysis : Set where
  constructor correspondence-analysis
  field
    experiment : Nat
    authorPublishedAnalysis : AnalysisChoice
    criticInitiallyReanalysed : AnalysisChoice
    criticAcknowledgedDifference : Bool
    exactParticipantReanalysisCompletedHere : Bool
open CorrespondenceAnalysis public

exp6January2018Clarification : CorrespondenceAnalysis
exp6January2018Clarification = correspondence-analysis
  6 oneSampleAgainstFixedHalf pairedAgainstNeutralControl true false

criticClarifiedTestMismatch :
  criticAcknowledgedDifference exp6January2018Clarification ≡ true
criticClarifiedTestMismatch = refl

notYetReplayedOriginalParticipantFiles :
  exactParticipantReanalysisCompletedHere exp6January2018Clarification ≡ false
notYetReplayedOriginalParticipantFiles = refl

correspondenceSource : Attribution.AttributedSource
correspondenceSource = Attribution.mkNoDOISource
  "Daryl J. Bem; Ulrich Schimmack"
  "January 2018 emails on Feeling the Future data and published methods"
  "Original dated email correspondence transcribed in Replicability-Index, posted 20 Jan 2018"
  "2018"
  "https://replicationindex.com/2018/01/20/bemcorrespondence/"
  Attribution.archivalSource
  "Documents Exp 1 40+60 epochs, Exp 6 91+19+40 changing protocol and the two test definitions, followed by critic's clarification"
  Attribution.publicAttribution

-- Programmatically retaining this receipt in the Bem hypothesis model
-- does not warrant attributing intentional cherry-picking to Bem.
sameOriginalExperimentOneOverall :
  Bem.reportedTrialCount (Bem.observed Bem.strongestSteelman) ≡ 1560
sameOriginalExperimentOneOverall = refl

data ProtocolChangeProvesFraud : Set where
data InitialCriticDiscrepancyStillUnresolved : Set where
data ChronologicalSplitProvesEffectModeration : Set where

noProtocolChangeFraudInference : ProtocolChangeProvesFraud → ⊥
noProtocolChangeFraudInference ()
noIncorrectCriticTestAsProof :
  InitialCriticDiscrepancyStillUnresolved → ⊥
noIncorrectCriticTestAsProof ()
noChronologyModerationWithoutData :
  ChronologicalSplitProvesEffectModeration → ⊥
noChronologyModerationWithoutData ()
