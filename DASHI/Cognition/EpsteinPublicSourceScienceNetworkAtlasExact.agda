module DASHI.Cognition.EpsteinPublicSourceScienceNetworkAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- PUBLIC-SOURCE SCIENCE-NETWORK ACQUISITION ATLAS
--
-- Purpose: stop acquisition rounds from being driven only by already-dense
-- in-repo seams. Each round begins with a fresh public-source sweep spanning
-- institutional reviews, primary/public records, high-quality reporting and
-- broad corpus indexes. Locator/index sources nominate targets only; they do
-- not pay relationship, funding, wrongdoing, coordination or authority edges.
------------------------------------------------------------------------

data SourceTier : Set where
  institutionalPrimary : SourceTier
  governmentPrimary : SourceTier
  highQualityReporting : SourceTier
  publicCorpusLocator : SourceTier
  secondaryResearchLocator : SourceTier

record PublicSourceReceipt : Set where
  constructor public-source-receipt
  field
    sourceTier : SourceTier
    sourceLabel : String
    subject : String
    documentedRelation : String
    usableAsPaidEdge : Bool
    locatorOnly : Bool
    wrongdoingInferred : Bool
open PublicSourceReceipt public

harvardReview : PublicSourceReceipt
harvardReview = public-source-receipt
  institutionalPrimary
  "Harvard Report Regarding Jeffrey Epstein's Connections to Harvard"
  "Harvard / Martin Nowak / George Church"
  "USD 9.179m Harvard giving; USD 6.5m to establish Program for Evolutionary Dynamics; >40 PED visits 2010-2018; donor introductions later yielding USD 7.5m to Nowak and USD 2m to Church, without finding that those donor funds were Epstein's."
  true false false

mitReview : PublicSourceReceipt
mitReview = public-source-receipt
  institutionalPrimary
  "MIT fact-finding report"
  "MIT / Media Lab / Joi Ito / Seth Lloyd"
  "Ten Epstein gifts totaling USD 850k and repeated campus visits, with post-conviction handling documented by MIT."
  true false false

kraussOriginsReporting : PublicSourceReceipt
kraussOriginsReporting = public-source-receipt
  highQualityReporting
  "Arizona State Press / public-record reporting on Origins Project"
  "Lawrence Krauss / ASU Origins Project"
  "Approximately USD 250k from Epstein's Enhanced Education foundation plus USD 2m from Leon and Debra Black across nine donations, with public-record correspondence documenting continued post-conviction contact."
  true false false

kraussDirectEmailLocator : PublicSourceReceipt
kraussDirectEmailLocator = public-source-receipt
  publicCorpusLocator
  "DOJ Epstein-file mirrors including EFTA00696862 and EFTA00628945"
  "Lawrence Krauss"
  "Direct correspondence about foundation acknowledgement and Krauss's public defence of Epstein; exact EFTA originals should be acquired before downstream claim promotion."
  false true false

brockmanNYTDOJ : PublicSourceReceipt
brockmanNYTDOJ = public-source-receipt
  highQualityReporting
  "New York Times reporting reproduced in DOJ release"
  "John Brockman / Edge / Murray Gell-Mann / Seth Lloyd"
  "Brockman described as an entree into Epstein's scientific community; 2004 Edge dinner introduced Epstein to Seth Lloyd; Gell-Mann acknowledged Epstein financial support."
  true false false

edgeFundingReporting : PublicSourceReceipt
edgeFundingReporting = public-source-receipt
  highQualityReporting
  "WIRED, Jeffrey Epstein and the Power of Networks"
  "Edge Foundation / John Brockman"
  "Reports USD 505k Epstein giving to Edge Foundation from 1998-2008 and describes Edge as a scientific/technology networking conduit."
  true false false

seedMediaReporting : PublicSourceReceipt
seedMediaReporting = public-source-receipt
  highQualityReporting
  "WIRED citing Mother Jones on Seed Media Group"
  "Seed Media Group / Ghislaine Maxwell / Jeffrey Epstein"
  "Reports board-level involvement in an influential science-media company; exact corporate records and roles require acquisition before stronger control/influence claims."
  false true false

maxwellGellMannProffer : PublicSourceReceipt
maxwellGellMannProffer = public-source-receipt
  governmentPrimary
  "DOJ July 25 2025 Ghislaine Maxwell interview transcript"
  "Ghislaine Maxwell / Murray Gell-Mann / Santa Fe Institute / Jeffrey Epstein"
  "Maxwell states that the Maxwell family had a Santa Fe Institute/Gell-Mann relationship and that she introduced Epstein to Murray Gell-Mann. This is a witness statement, not independent corroboration of every detail."
  true false false

natureScienceOverview : PublicSourceReceipt
natureScienceOverview = public-source-receipt
  highQualityReporting
  "Nature 2026 Epstein science-network reporting/editorial"
  "scientists and research institutions"
  "Documents deeper-than-previously-known scientific ties and donor-governance issues; mathematical biology and AI among funded fields."
  true false false

apAcademiaOverview : PublicSourceReceipt
apAcademiaOverview = public-source-receipt
  highQualityReporting
  "Associated Press 2026 academia overview"
  "academics / universities / private funding"
  "Documents multiple academics maintaining relationships in hopes of research funding and identifies additional institutions/figures for acquisition."
  true false false

broadCorpusAuditLocator : PublicSourceReceipt
broadCorpusAuditLocator = public-source-receipt
  secondaryResearchLocator
  "2026 public full-corpus scientist/academic audits and graph indexes"
  "Krauss, Ito, Chomsky, Nowak, Brockman, Church, Hillis, Trivers and others"
  "Useful for candidate nomination and document-count prioritisation only; AI-generated or independent indexes must be resolved back to EFTA/institutional/credible-reporting sources."
  false true false

------------------------------------------------------------------------
-- Infrastructure hubs that the broader sweep says must compete globally.
------------------------------------------------------------------------

data InfrastructureHub : Set where
  brockmanEdge : InfrastructureHub
  harvardPED : InfrastructureHub
  mitMediaLab : InfrastructureHub
  kraussOrigins : InfrastructureHub
  seedScienceMedia : InfrastructureHub
  santaFeGellMann : InfrastructureHub
  gatesPhilanthropy : InfrastructureHub
  yuConsciousnessEvents : InfrastructureHub
  terraMarNonprofit : InfrastructureHub
  maxwellPergamonPublishing : InfrastructureHub

record HubPriorityBoundary : Set where
  constructor hub-priority-boundary
  field
    freshWebSweepEachRound : Bool
    namedPersonSearchOnly : Bool
    infrastructureSearchRequired : Bool
    publicCorpusIndexCanNominate : Bool
    publicCorpusIndexPaysClaim : Bool
    primaryOrReliableEdgeResolutionRequired : Bool
open HubPriorityBoundary public

canonicalHubPriorityBoundary : HubPriorityBoundary
canonicalHubPriorityBoundary =
  hub-priority-boundary true false true true false true

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data LocatorCreatesRelationship : Set where
data BoardMentionCreatesEditorialControl : Set where
data DonorIntroductionCreatesCommonSourceOfFunds : Set where
data ConveningAccessCreatesScientificInfluence : Set where
data WitnessStatementCreatesIndependentCorroboration : Set where

locatorDoesNotCreateRelationship : LocatorCreatesRelationship → ⊥
locatorDoesNotCreateRelationship ()

boardMentionDoesNotCreateEditorialControl : BoardMentionCreatesEditorialControl → ⊥
boardMentionDoesNotCreateEditorialControl ()

donorIntroductionDoesNotProveCommonSourceOfFunds :
  DonorIntroductionCreatesCommonSourceOfFunds → ⊥
donorIntroductionDoesNotProveCommonSourceOfFunds ()

conveningAccessDoesNotByItselfProveScientificInfluence :
  ConveningAccessCreatesScientificInfluence → ⊥
conveningAccessDoesNotByItselfProveScientificInfluence ()

witnessStatementIsNotIndependentCorroboration :
  WitnessStatementCreatesIndependentCorroboration → ⊥
witnessStatementIsNotIndependentCorroboration ()
