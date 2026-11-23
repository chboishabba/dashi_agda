module DASHI.Culture.AmyEskridgeBemAristotleExperimentalProofSearchWeldExact where

-- Source-exact Aristotle / DASHI proof-search *integration*, not a new
-- Monte-Carlo tree search or invented original Bem statistics.
-- Import the actual proof-bearing loop and transition dynamics from:
--   AristotleMergeExperimentDesignExact
--   AristotleActiveExperimentalProofSearchLoopExact
--   AristotleActiveExperimentalProofSearchDynamicsExact
-- plus canonical ExperimentBundle/DiscriminatorSynthesis.
--
-- A research decision is only escalated after its predecessor has
-- ORIGINAL independent source receipts. Published archive links are
-- discovery, not data acquisition. Actual workbook bytes still needed.
--
-- Original authority: Bem 2011 DOI 10.1037/a0021524; Transparent Psi
-- 2023 DOI 10.1098/rsos.191375. Original XLSX archive at
-- https://replicationindex.com/2018/01/20/bemcorrespondence/
-- This is a source-specific planner; it does not run Aristotle software or
-- claim an observed experiment/proof state.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Core.DiscriminatorSynthesisExact as Disc
import DASHI.Reasoning.AristotleMergeExperimentDesignExact as Aristotle
import DASHI.Reasoning.AristotleActiveExperimentalProofSearchLoopExact as Search
import DASHI.Reasoning.AristotleActiveExperimentalProofSearchDynamicsExact as Dynamics
import DASHI.Culture.AmyEskridgeBemNativeStatisticsDiscriminatorWeldExact as BemDisc
import DASHI.Culture.AmyEskridgeBemOriginalProtocolCorrespondenceWeldExact as Correspondence
import DASHI.Statistics.TukeyKramerPostHocExact as TukeyHSD

-- Distinguish exact source status from bibliographic presence.
record ResearchReceiptState : Set where
  constructor research-receipt
  field
    originalWorkbookBytesInspected : Bool
    originalPublishedTestReproduced : Bool
    transparentPsiPreregisteredDataReplayed : Bool
    moderatorFamilyPredeclared : Bool
    nuisanceAndVarianceAssumptionsChecked : Bool
open ResearchReceiptState public

data NextExperiment : Set where
  acquireExp1Workbook : NextExperiment
  replayOriginalPublishedStatistic : NextExperiment
  replayTransparentPsiPreregistration : NextExperiment
  inspectSteelmanModeratorCoordinates : NextExperiment
  runDeclaredPostHocDiscriminator : NextExperiment

-- Search-first policy prioritises ORIGINAL evidence and source-true
-- statistical reproduction over convenient model-side proofs.
nextExperiment : ResearchReceiptState → NextExperiment
nextExperiment (research-receipt false _ _ _ _) = acquireExp1Workbook
nextExperiment (research-receipt true false _ _ _) = replayOriginalPublishedStatistic
nextExperiment (research-receipt true true false _ _) = replayTransparentPsiPreregistration
nextExperiment (research-receipt true true true false _) = inspectSteelmanModeratorCoordinates
nextExperiment (research-receipt true true true true false) = inspectSteelmanModeratorCoordinates
nextExperiment (research-receipt true true true true true) = runDeclaredPostHocDiscriminator

-- Current source status: XLSX links exist but bytes unavailable. Therefore
-- this planner cannot legally select a Tukey/HSD measurement on the original.
currentSourceStatus : ResearchReceiptState
currentSourceStatus = research-receipt false false false false false

currentlyMustAcquireOriginal :
  nextExperiment currentSourceStatus ≡ acquireExp1Workbook
currentlyMustAcquireOriginal = refl

afterWorkbookAcquisition : ResearchReceiptState
afterWorkbookAcquisition = research-receipt true false false false false

afterAcquisitionMustReproducePrimary :
  nextExperiment afterWorkbookAcquisition ≡ replayOriginalPublishedStatistic
afterAcquisitionMustReproducePrimary = refl

afterOnlyTwoReplications : ResearchReceiptState
afterOnlyTwoReplications = research-receipt true true true false false

stillNeedsModeratorPlan :
  nextExperiment afterOnlyTwoReplications ≡ inspectSteelmanModeratorCoordinates
stillNeedsModeratorPlan = refl

syntheticFullyAdmitted : ResearchReceiptState
syntheticFullyAdmitted = research-receipt true true true true true

syntheticOnlyThenPostHoc :
  nextExperiment syntheticFullyAdmitted ≡ runDeclaredPostHocDiscriminator
syntheticOnlyThenPostHoc = refl

-- These are ORIGINAL canonical Aristotle proof-search owners.
-- The dynamics distinguish live iteration vs legitimate consumer closure,
-- and guarded branch merge and provenance are already formalized there.
aristotleOriginalOneIteration :
  Dynamics.LoopPath Search.liveHypotheses Search.liveHypotheses
aristotleOriginalOneIteration = Dynamics.canonicalOneIterationCycle

aristotleOriginalClosurePath :
  Dynamics.LoopPath Search.liveHypotheses Search.consumerClosed
aristotleOriginalClosurePath = Dynamics.canonicalClosurePath

aristotleOriginalProofSearchBoundary :
  Search.ActiveExperimentalProofSearchBoundary
aristotleOriginalProofSearchBoundary =
  Search.canonicalActiveExperimentalProofSearchBoundary

aristotleOriginalExperimentBoundary :
  Aristotle.AristotleMergeExperimentBoundary
aristotleOriginalExperimentBoundary =
  Aristotle.canonicalAristotleMergeExperimentBoundary

actualConsumerDiscriminator :
  Disc.DiscriminatingLanguageExtension BemDisc.publishedAggregate
actualConsumerDiscriminator = BemDisc.sameReportedNumberNeedsNewDiscriminator

-- Tukey-Kramer is an *optional secondary test for suitable groups*.
-- It is NOT a replacement for the one-sample exact primary Bem test,
-- for mixed logit in Transparent Psi, or for source verification.
tukeyActualComparisonExample :
  TukeyHSD.decide
    TukeyHSD.syntheticDesign
    TukeyHSD.groupMean10
    TukeyHSD.groupMean16
    ≡ TukeyHSD.familyAdjustedReject
tukeyActualComparisonExample = refl

data ExistenceOfXlsxURLCountsAsAnalysedData : Set where
data AristotleProofSearchConvertsHypothesisIntoEmpiricalFact : Set where
data TukeyHSDCanReplaceOriginalOneSampleTest : Set where

noURLAsEvidenceBytes : ExistenceOfXlsxURLCountsAsAnalysedData → ⊥
noURLAsEvidenceBytes ()
noProofSearchAsPhysicalEvidence :
  AristotleProofSearchConvertsHypothesisIntoEmpiricalFact → ⊥
noProofSearchAsPhysicalEvidence ()
noHSDAsOriginalTest :
  TukeyHSDCanReplaceOriginalOneSampleTest → ⊥
noHSDAsOriginalTest ()
