module DASHI.Governance.BoloBoloOWSSpokesProposalLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.BoloBoloOWSContemporaneousSpokesWitnessExact as Contemporaneous

------------------------------------------------------------------------
-- OWS WORKING GROUP & CAUCUS SPOKES COUNCIL PROPOSAL LINEAGE
--
-- This owner triangulates an intended-governance artifact without collapsing
-- source roles:
--
-- * original NYCGA proposal locator / title;
-- * contemporaneous People’s Library minutes linking to that proposal;
-- * a preserved later PDF copy exposing the proposal text;
-- * NYU archival finding-aid evidence that the proposal artifact is held;
-- * later scholarship citing the 2011 NYCGA proposal.
--
-- The preserved copy and later scholarship do not silently become the original
-- NYCGA page. Proposal design also does not establish implementation fidelity
-- or realised non-domination.
------------------------------------------------------------------------

data ProposalLineageRole : Set where
  originalLocatorRole : ProposalLineageRole
  contemporaneousLinkedWitnessRole : ProposalLineageRole
  preservedDocumentMirrorRole : ProposalLineageRole
  archivalFindingAidRole : ProposalLineageRole
  laterScholarlyCitationRole : ProposalLineageRole

record ProposalLineageSource : Set where
  constructor proposal-lineage-source
  field
    title : String
    sourceReference : String
    role : ProposalLineageRole
    sourceSupports : String
    sourceDoesNotByItselfSupport : String

open ProposalLineageSource public

originalNYCGAProposalLocator : ProposalLineageSource
originalNYCGAProposalLocator =
  proposal-lineage-source
    "Working Group & Caucus Spokes Council Proposal"
    "http://www.nycga.net/spokes-council/ ; cited as Occupy Wall Street New York City General Assembly, 2011-10-21"
    originalLocatorRole
    "identity and original NYCGA locator of the proposal artifact"
    "current recovery of the original page body, implementation fidelity, or realised governance effect"

libraryLinkedProposalWitness : ProposalLineageSource
libraryLinkedProposalWitness =
  proposal-lineage-source
    "10/22/11 Meeting Minutes"
    "https://peopleslibrary.wordpress.com/2011/10/22/library-working-group-meeting-minutes/"
    contemporaneousLinkedWitnessRole
    "contemporaneous Library minutes linking to nycga.net/spokes-council and recording a Structure Working Group presentation that described rotation every meeting, recall, observer access, modified consensus and the intended operational purpose"
    "the official proposal text, proof that the rules were implemented, or a realised-power audit"

preservedProposalMirror : ProposalLineageSource
preservedProposalMirror =
  proposal-lineage-source
    "STRUCTURE AND PROCESS GUIDE TO OWS / Working Group & Caucus Spokes Council Proposal"
    "https://macc.nyc/img/assemblies/OWSStructure.pdf"
    preservedDocumentMirrorRole
    "a preserved copy whose proposal section describes the GA as central while presenting the Spokes Council as an operational complement and frames accountable, transparent and horizontal relationships as design aims"
    "original-custody identity, implementation fidelity, non-domination, or authority to act"

nyuFindingAidProposal : ProposalLineageSource
nyuFindingAidProposal =
  proposal-lineage-source
    "Working Group and Caucus Spokes Council Proposal"
    "NYU Tamiment Library, Jaime Taylor and Zachary Loeb Collection on the Occupy Wall Street Library, Box 1 Folder 14"
    archivalFindingAidRole
    "independent archival finding-aid evidence that an artifact with this title is preserved in the OWS Library collection"
    "content identity with every circulating draft, adoption status, or realised implementation"

murray2016ProposalCitation : ProposalLineageSource
murray2016ProposalCitation =
  proposal-lineage-source
    "The Sphere, the Screen, and the Square: Locating Occupy in the Public Sphere"
    "Communication Theory 26 (2016); cites Occupy Wall Street New York City General Assembly, 2011-10-21, Working Group & Caucus Spokes Council Proposal"
    laterScholarlyCitationRole
    "later scholarly citation to the NYCGA proposal and its accountable/transparent/horizontal design language"
    "primary-event evidence, exact implementation fidelity, or causal governance effect"

canonicalProposalLineageSources : List ProposalLineageSource
canonicalProposalLineageSources =
  originalNYCGAProposalLocator
  ∷ libraryLinkedProposalWitness
  ∷ preservedProposalMirror
  ∷ nyuFindingAidProposal
  ∷ murray2016ProposalCitation
  ∷ []

------------------------------------------------------------------------
-- Intended-design surface.
------------------------------------------------------------------------

record IntendedSpokesDesign : Set where
  constructor intended-spokes-design
  field
    rotatingSpokeEveryMeeting : Bool
    spokeRecallIfGroupMisrepresented : Bool
    observerAccess : Bool
    modifiedConsensusSurface : Bool
    operationalCoordinationPurpose : Bool
    horizontalAccountableTransparentAim : Bool

open IntendedSpokesDesign public

canonicalIntendedSpokesDesign : IntendedSpokesDesign
canonicalIntendedSpokesDesign =
  intended-spokes-design true true true true true true

contemporaneousBoundaryAnchor : Contemporaneous.ContemporaneousSpokesBoundary
contemporaneousBoundaryAnchor = Contemporaneous.canonicalContemporaneousSpokesBoundary

------------------------------------------------------------------------
-- Intended design cannot determine realised control.
--
-- The fixture is synthetic and information-theoretic: two possible realised
-- worlds share the exact same intended rotation/recall/observer design but
-- differ in whether control remains dispersed/reopenable or concentrates in a
-- restricted realised topology. It does not assert either world occurred at
-- OWS; it blocks design documents from certifying implementation.
------------------------------------------------------------------------

data SpokesImplementationWorld : Set where
  sameDesignDispersedImplementation : SpokesImplementationWorld
  sameDesignConcentratedImplementation : SpokesImplementationWorld

data IntendedDesignCode : Set where
  rotationRecallObserverDesign : IntendedDesignCode

data RealizedSpokesControlCode : Set where
  dispersedReopenableSpokesControl : RealizedSpokesControlCode
  concentratedRestrictedSpokesControl : RealizedSpokesControlCode

intendedDesignProjection : SpokesImplementationWorld → IntendedDesignCode
intendedDesignProjection sameDesignDispersedImplementation = rotationRecallObserverDesign
intendedDesignProjection sameDesignConcentratedImplementation = rotationRecallObserverDesign

realizedControlProjection : SpokesImplementationWorld → RealizedSpokesControlCode
realizedControlProjection sameDesignDispersedImplementation = dispersedReopenableSpokesControl
realizedControlProjection sameDesignConcentratedImplementation = concentratedRestrictedSpokesControl

realizedSpokesControlCodesDiffer :
  realizedControlProjection sameDesignDispersedImplementation ≡
  realizedControlProjection sameDesignConcentratedImplementation → ⊥
realizedSpokesControlCodesDiffer ()

intendedDesignRealizedControlNonFactorability :
  INF.NonFactorabilityWitness intendedDesignProjection realizedControlProjection
intendedDesignRealizedControlNonFactorability =
  INF.nonFactorabilityWitness
    sameDesignDispersedImplementation
    sameDesignConcentratedImplementation
    refl
    realizedSpokesControlCodesDiffer

IntendedDesignDeterminesRealizedControl : Set
IntendedDesignDeterminesRealizedControl =
  INF.FactorsThrough intendedDesignProjection realizedControlProjection

intendedDesignDoesNotDetermineRealizedControl :
  IntendedDesignDeterminesRealizedControl → ⊥
intendedDesignDoesNotDetermineRealizedControl =
  INF.witnessRulesOutEveryFlatFactorisation intendedDesignRealizedControlNonFactorability

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record SpokesProposalLineageBoundary : Set where
  constructor spokes-proposal-lineage-boundary
  field
    proposalArtifactLineagePresent : Bool
    originalNYCGALocatorPresent : Bool
    contemporaneousLinkedWitnessPresent : Bool
    preservedMirrorPresent : Bool
    archivalFindingAidPresent : Bool
    laterScholarlyCitationPresent : Bool

    rotationRecallDesignSurfacePresent : Bool
    observerAccessDesignSurfacePresent : Bool
    operationalCoordinationDesignSurfacePresent : Bool
    horizontalAccountableTransparentAimPresent : Bool

    preservedMirrorEqualsOriginalNYCGAPage : Bool
    proposalDesignProvesRealizedImplementation : Bool
    rotationRuleProvesEqualRealizedInfluence : Bool
    recallRuleProvesEffectiveRecall : Bool
    observerAccessProvesEqualVoice : Bool
    horizontalAimProvesNonDomination : Bool
    proposalLineagePaysPrimarySpokesMinutes : Bool
    proposalLineageIdentifiesCausalEffect : Bool

open SpokesProposalLineageBoundary public

canonicalSpokesProposalLineageBoundary : SpokesProposalLineageBoundary
canonicalSpokesProposalLineageBoundary =
  spokes-proposal-lineage-boundary
    true true true true true true
    true true true true
    false false false false false false false false

canonicalSpokesProposalLineageReceipt : GenericReceipt.GenericReceipt
canonicalSpokesProposalLineageReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "OWS Spokes proposal artifact/source lineage"
    "DASHI.Governance.BoloBoloOWSSpokesProposalLineageExact"
    "canonicalProposalLineageSources / canonicalIntendedSpokesDesign / intendedDesignDoesNotDetermineRealizedControl"
    "triangulates the Working Group & Caucus Spokes Council Proposal across the original NYCGA locator, a contemporaneous People’s Library linked presentation, a preserved document mirror, NYU archival finding-aid evidence and later scholarship; retains rotation, recall, observer access, operational coordination and horizontal/accountable/transparent aims as intended-design coordinates and proves by a synthetic non-factorability witness that this design cannot determine the realised-control consumer"
    "the preserved mirror is not silently promoted to the original NYCGA page; the synthetic collision creates no empirical OWS result; intended design does not prove implementation fidelity, equal influence, effective recall, equal voice, non-domination, primary Spokes-minute content or causal effect"
    "agda -i . DASHI/Governance/BoloBoloOWSSpokesProposalLineageRegression.agda"
