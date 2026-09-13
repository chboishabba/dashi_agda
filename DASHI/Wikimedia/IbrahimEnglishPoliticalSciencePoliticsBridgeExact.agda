module DASHI.Wikimedia.IbrahimEnglishPoliticalSciencePoliticsBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimEnglishParentCoverageGapAtlasExact as Gap
import DASHI.Wikimedia.IbrahimEnglishSocialScienceFunnelBridgeExact as Social

------------------------------------------------------------------------
-- IBRAHIM ENGLISH POLITICAL-SCIENCE / POLITICS BRIDGE
--
-- External navigation observation, inspected 2026-09-10:
--   Political science (Q36442) studies politics (Q7163).
--
-- Current English Wikipedia describes political science as the scientific
-- study of politics, including governance, power, political activity,
-- political thought/behaviour, constitutions and law.  Wikidata likewise
-- identifies Q36442 as political science and Q7163 as politics.
--
-- This owner uses that relation as a revision-sensitive navigation prior for
-- finding DASHI coverage debt.  It does NOT import Wikipedia as a formal
-- theory of politics and does NOT equate politics with political science.
------------------------------------------------------------------------

record PoliticalSciencePoliticsCoordinate : Set where
  constructor political-science-politics-coordinate
  field
    politicalScienceTitle : String
    politicalScienceQid : String
    politicsTitle : String
    politicsQid : String
    observationDate : String
    relationReading : String
open PoliticalSciencePoliticsCoordinate public

currentPoliticalSciencePoliticsCoordinate : PoliticalSciencePoliticsCoordinate
currentPoliticalSciencePoliticsCoordinate =
  political-science-politics-coordinate
    "Political science"
    "Q36442"
    "politics"
    "Q7163"
    "2026-09-10"
    "external navigation coordinate: political science is the scientific study of politics; revision-sensitive and non-authoritative"

------------------------------------------------------------------------
-- Introspective quotient against existing DASHI surfaces.
--
-- The focused parent audit already found no canonical PoliticalScience owner,
-- while related material exists in Governance, SensibLaw, Mabo and political
-- economy.  Therefore the shortest truthful repair is not a fresh theory of
-- politics: it is a canonical bridge/consolidation owner that points into the
-- existing surfaces while keeping the surviving discipline-specific debt
-- explicit.
------------------------------------------------------------------------

record PoliticalScienceExistingSubstrate : Set where
  constructor political-science-existing-substrate
  field
    governanceSurface : String
    lawSurface : String
    nativeTitleSovereigntySurface : String
    politicalEconomySurface : String
    evidenceAuthoritySurface : String
    relatedMaterialObserved : Bool
    canonicalPoliticalScienceOwnerObserved : Bool
open PoliticalScienceExistingSubstrate public

politicalScienceSubstrate : PoliticalScienceExistingSubstrate
politicalScienceSubstrate =
  political-science-existing-substrate
    "DASHI Governance / institutional / decision-rule formulations"
    "SensibLaw legislation, doctrine, authority, causation and source-provenance formulations"
    "Mabo / sovereignty / native-title / Two-Eyed operational-justice formulations"
    "DASHI Economics and capital/political-economy cross-pollination surfaces"
    "evidence, observer, source diligence and authority-status owners"
    true
    false

record PoliticalScienceSurvivingDebt : Set where
  constructor political-science-surviving-debt
  field
    needsGenericPoliticsTheoryFromWikipedia : Bool
    needsCanonicalPoliticalScienceBridge : Bool
    needsPoliticsParentCoordinate : Bool
    needsGovernanceReuse : Bool
    needsLawReuse : Bool
    needsMaboReuse : Bool
    needsPoliticalEconomyReuse : Bool
    needsEmpiricalPoliticalScienceSourceLane : Bool
open PoliticalScienceSurvivingDebt public

politicalScienceDebtAfterQuotient : PoliticalScienceSurvivingDebt
politicalScienceDebtAfterQuotient =
  political-science-surviving-debt
    false
    true
    true
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- Canonical bridge contract.
------------------------------------------------------------------------

record PoliticalScienceBridgeContract : Set where
  constructor political-science-bridge-contract
  field
    externalCoordinate : PoliticalSciencePoliticsCoordinate
    socialScienceParentQid : String
    childCoverageStatus : Gap.DashiParentCoverageStatus
    existingSubstrate : PoliticalScienceExistingSubstrate
    politicsAsObjectOfStudy : Bool
    governanceAndLawAreConstituentSurfaces : Bool
    evidenceMethodsRemainDisciplineSpecific : Bool
    normativePoliticalPhilosophyCollapsedIntoPoliticalScience : Bool
    externalQidCreatesDashiOwner : Bool
open PoliticalScienceBridgeContract public

canonicalPoliticalScienceBridgeContract : PoliticalScienceBridgeContract
canonicalPoliticalScienceBridgeContract =
  political-science-bridge-contract
    currentPoliticalSciencePoliticsCoordinate
    (Social.SocialScienceFunnelCoordinate.qid Social.socialScienceQ34749)
    Gap.parentBridgeMissing
    politicalScienceSubstrate
    true
    true
    true
    false
    false

------------------------------------------------------------------------
-- Admission remains intentionally partial.  The parent coordinate and reuse
-- plan are paid here; a canonical PoliticalScience leaf should become admitted
-- only when a DASHI-side owner actually consolidates the empirical/descriptive
-- discipline over the existing governance/law/economy surfaces.
------------------------------------------------------------------------

record PoliticalScienceBridgeAdmission : Set where
  constructor political-science-bridge-admission
  field
    politicsQidResolved : Bool
    socialScienceQidResolved : Bool
    existingDashiSubstrateLocated : Bool
    canonicalLeafOwnerPaid : Bool
    empiricalSourceLanePaid : Bool
    parentBridgeReady : Bool
open PoliticalScienceBridgeAdmission public

politicalScienceAdmissionNow : PoliticalScienceBridgeAdmission
politicalScienceAdmissionNow =
  political-science-bridge-admission
    true
    true
    true
    false
    false
    true

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PoliticsIsPoliticalScience : Set where
data GovernanceAlonePaysPoliticalScience : Set where
data LawAlonePaysPoliticalScience : Set where
data WikipediaDescriptionPaysEmpiricalDiscipline : Set where
data PoliticalScienceCreatesNormativeAuthority : Set where

politicsIsNotPoliticalScience : PoliticsIsPoliticalScience → ⊥
politicsIsNotPoliticalScience ()

governanceAloneDoesNotPayPoliticalScience : GovernanceAlonePaysPoliticalScience → ⊥
governanceAloneDoesNotPayPoliticalScience ()

lawAloneDoesNotPayPoliticalScience : LawAlonePaysPoliticalScience → ⊥
lawAloneDoesNotPayPoliticalScience ()

wikipediaDoesNotPayEmpiricalDiscipline : WikipediaDescriptionPaysEmpiricalDiscipline → ⊥
wikipediaDoesNotPayEmpiricalDiscipline ()

politicalScienceDoesNotCreateNormativeAuthority : PoliticalScienceCreatesNormativeAuthority → ⊥
politicalScienceDoesNotCreateNormativeAuthority ()

record PoliticalSciencePoliticsBoundary : Set where
  constructor political-science-politics-boundary
  field
    qidIdentitySeparated : Bool
    navigationObservationRevisionSensitive : Bool
    existingDashiSurfacesReused : Bool
    canonicalLeafDebtExplicit : Bool
    empiricalSourceDebtExplicit : Bool
    politicsEqualsPoliticalScience : Bool
    wikipediaCreatesProofAuthority : Bool
open PoliticalSciencePoliticsBoundary public

canonicalPoliticalSciencePoliticsBoundary : PoliticalSciencePoliticsBoundary
canonicalPoliticalSciencePoliticsBoundary =
  political-science-politics-boundary
    true true true true true false false
