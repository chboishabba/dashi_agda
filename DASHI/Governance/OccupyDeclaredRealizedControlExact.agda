module DASHI.Governance.OccupyDeclaredRealizedControlExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Governance.OccupyRealizedControlAcquisitionExact as Realized
import DASHI.Governance.BoloBoloOWSSpokesPrimaryLocatorAtlasExact as Spokes

------------------------------------------------------------------------
-- OWS DECLARED PURPOSE / REALISED CONTROL BOUNDARY
--
-- Primary adopted NYCGA documents are source-owned constitutional statements.
-- They pay declared purpose/normative commitments only. They do not pay the
-- realised authority graph, actual correction handling or empirical absence of
-- informal leadership. Those remain empirical questions for the primary-minute
-- / realised-control acquisition surface.
------------------------------------------------------------------------

data OccupyPrimaryDocument : Set where
  principlesOfSolidarity20110923 : OccupyPrimaryDocument
  statementOfAutonomy20111110 : OccupyPrimaryDocument

record PrimaryDocumentReceipt : Set where
  constructor primary-document-receipt
  field
    document : OccupyPrimaryDocument
    repositoryReference : String
    blobReference : String
    acceptedDate : String
    declaredPurposeReference : String

open PrimaryDocumentReceipt public

principlesPrimaryReceipt : PrimaryDocumentReceipt
principlesPrimaryReceipt =
  primary-document-receipt
    principlesOfSolidarity20110923
    "OccupyWallStreet/New-York-City-General-Assembly-Documents"
    "131511f48e04ef3c656d9a6e7675227d17d3c2dc"
    "2011-09-23"
    "direct/transparent participatory democracy; personal/collective responsibility; recognition of privilege; empowerment against oppression; individual privacy; open access to technologies, knowledge and culture"

statementAutonomyPrimaryReceipt : PrimaryDocumentReceipt
statementAutonomyPrimaryReceipt =
  primary-document-receipt
    statementOfAutonomy20111110
    "OccupyWallStreet/New-York-City-General-Assembly-Documents"
    "ba3ed875ba13d7b3bd3c7dfdd43269a221e42c26"
    "2011-11-10"
    "people's movement; party-less and leaderless; participatory democracy; welcome dissent; sole/mutual caretakers; supporters should question institutional hierarchy; speak with us not for us; collective resources/dignity/integrity/autonomy; transparent consensus allocation"

canonicalPrimaryDocumentReceipts : List PrimaryDocumentReceipt
canonicalPrimaryDocumentReceipts =
  principlesPrimaryReceipt ∷ statementAutonomyPrimaryReceipt ∷ []

------------------------------------------------------------------------
-- Primary declared-purpose projection.
------------------------------------------------------------------------

data DeclaredGovernanceCommitment : Set where
  directParticipatoryDemocracy : DeclaredGovernanceCommitment
  transparency : DeclaredGovernanceCommitment
  responsibility : DeclaredGovernanceCommitment
  privilegeAwareness : DeclaredGovernanceCommitment
  antiOppression : DeclaredGovernanceCommitment
  privacy : DeclaredGovernanceCommitment
  openKnowledge : DeclaredGovernanceCommitment
  leaderlessness : DeclaredGovernanceCommitment
  dissentWelcome : DeclaredGovernanceCommitment
  antiHierarchyReflection : DeclaredGovernanceCommitment
  collectiveAutonomy : DeclaredGovernanceCommitment

canonicalDeclaredCommitments : List DeclaredGovernanceCommitment
canonicalDeclaredCommitments =
  directParticipatoryDemocracy
  ∷ transparency
  ∷ responsibility
  ∷ privilegeAwareness
  ∷ antiOppression
  ∷ privacy
  ∷ openKnowledge
  ∷ leaderlessness
  ∷ dissentWelcome
  ∷ antiHierarchyReflection
  ∷ collectiveAutonomy
  ∷ []

------------------------------------------------------------------------
-- Exact non-factorability fixture.
--
-- This is a finite DASHI witness, not an empirical assertion that either
-- synthetic world describes OWS. It proves the information-theoretic point:
-- identical declared commitments can coexist with distinct realised-control
-- states, therefore declaration alone is not consumer-sufficient for realised
-- control.
------------------------------------------------------------------------

data OccupyControlWorld : Set where
  sameDeclarationDispersedControl : OccupyControlWorld
  sameDeclarationConcentratedControl : OccupyControlWorld

data DeclaredPurposeCode : Set where
  adoptedLeaderlessParticipatoryCommitments : DeclaredPurposeCode

data RealizedControlCode : Set where
  dispersedReopenableControl : RealizedControlCode
  concentratedRestrictedControl : RealizedControlCode

declaredOccupyProjection : OccupyControlWorld → DeclaredPurposeCode
declaredOccupyProjection sameDeclarationDispersedControl =
  adoptedLeaderlessParticipatoryCommitments
declaredOccupyProjection sameDeclarationConcentratedControl =
  adoptedLeaderlessParticipatoryCommitments

realizedOccupyProjection : OccupyControlWorld → RealizedControlCode
realizedOccupyProjection sameDeclarationDispersedControl =
  dispersedReopenableControl
realizedOccupyProjection sameDeclarationConcentratedControl =
  concentratedRestrictedControl

realizedControlCodesDiffer :
  realizedOccupyProjection sameDeclarationDispersedControl ≡
  realizedOccupyProjection sameDeclarationConcentratedControl → ⊥
realizedControlCodesDiffer ()

declaredRealizedNonFactorabilityWitness :
  INF.NonFactorabilityWitness declaredOccupyProjection realizedOccupyProjection
declaredRealizedNonFactorabilityWitness =
  INF.nonFactorabilityWitness
    sameDeclarationDispersedControl
    sameDeclarationConcentratedControl
    refl
    realizedControlCodesDiffer

DeclaredPurposeDeterminesRealizedControl : Set
DeclaredPurposeDeterminesRealizedControl =
  INF.FactorsThrough declaredOccupyProjection realizedOccupyProjection

declaredPurposeDoesNotDetermineRealizedControl :
  DeclaredPurposeDeterminesRealizedControl → ⊥
declaredPurposeDoesNotDetermineRealizedControl =
  INF.witnessRulesOutEveryFlatFactorisation declaredRealizedNonFactorabilityWitness

------------------------------------------------------------------------
-- Existing owners retained as exact anchors.
------------------------------------------------------------------------

posiwidBoundaryAnchor : POSIWID.OperationalDescriptionBoundary
posiwidBoundaryAnchor = POSIWID.canonicalOperationalDescriptionBoundary

realizedControlBoundaryAnchor : Realized.RealizedControlAcquisitionBoundary
realizedControlBoundaryAnchor = Realized.canonicalRealizedControlAcquisitionBoundary

spokesLocatorBoundaryAnchor : Spokes.SpokesPrimaryLocatorBoundary
spokesLocatorBoundaryAnchor = Spokes.canonicalSpokesPrimaryLocatorBoundary

------------------------------------------------------------------------
-- Secondary reconstruction layer.
--
-- Holmes 2023 cites the exact 7/9/11/14 Nov OWS minutes and reconstructs
-- facilitation, rotation, caucus-delay power, agenda/process breakdown and
-- correction attempts. Those observations are useful secondary evidence, but
-- are deliberately not retyped as the missing primary minute content.
------------------------------------------------------------------------

record SecondaryRealizedControlReconstruction : Set where
  constructor secondary-realized-control-reconstruction
  field
    sourceReference : String
    citedPrimaryMinutesReference : String
    reconstructionReference : String
    primaryMinuteContentRecovered : Bool

open SecondaryRealizedControlReconstruction public

holmes2023SpokesReconstruction : SecondaryRealizedControlReconstruction
holmes2023SpokesReconstruction =
  secondary-realized-control-reconstruction
    "Marisa Holmes, Organizing Occupy Wall Street: This Is Just Practice (2023), Structure chapter"
    "OWS Minutes 2011-11-07 / 11-09 / 11-11 / 11-14"
    "secondary reconstruction records named facilitators, rotating-spoke rule, caucus delay power, repeated spokes after failed rotation communication, facilitation breakdown, de-escalation attempts and reopening/conflict problems"
    false

------------------------------------------------------------------------
-- Terminal declared-vs-realised firewall.
------------------------------------------------------------------------

record OccupyDeclaredRealizedBoundary : Set where
  constructor occupy-declared-realized-boundary
  field
    primaryAdoptedDocumentsPresent : Bool
    primaryDeclaredParticipatoryDemocracyPresent : Bool
    primaryDeclaredLeaderlessPresent : Bool
    primaryDeclaredDissentPresent : Bool
    primaryDeclaredPrivacyPresent : Bool
    primaryDeclaredOpenKnowledgePresent : Bool

    declaredLeaderlessProvesNoRealizedLeadership : Bool
    declaredParticipatoryPurposeProvesRealizedHorizontalControl : Bool
    declaredTransparencyProvesInspectableRealizedAuthority : Bool
    declaredDissentProvesCorrectionWorks : Bool
    secondaryReconstructionPaysPrimaryMinuteContent : Bool
    locatorPaysPrimaryMinuteContent : Bool
    openKnowledgeCancelsIndividualPrivacy : Bool

    realizedControlRequiresIndependentObservation : Bool
    correctionResponseRequiredForRealizedControlAudit : Bool
    informalLeadershipRemainsEmpiricalQuestion : Bool
    primaryMinuteRecoveryStillRequiredForMinuteExactCoding : Bool

open OccupyDeclaredRealizedBoundary public

canonicalOccupyDeclaredRealizedBoundary : OccupyDeclaredRealizedBoundary
canonicalOccupyDeclaredRealizedBoundary =
  occupy-declared-realized-boundary
    true true true true true true
    false false false false false false false
    true true true true

primaryPurposeDoesNotOverrideRealizedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundaryAnchor ≡ false
primaryPurposeDoesNotOverrideRealizedEffect = refl

correctionResponseIsOperationalEvidence :
  POSIWID.correctionResponseIsPartOfObservableOperation posiwidBoundaryAnchor ≡ true
correctionResponseIsOperationalEvidence = refl

canonicalOccupyDeclaredRealizedReceipt : GenericReceipt.GenericReceipt
canonicalOccupyDeclaredRealizedReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "OWS primary declared-purpose / realised-control boundary"
    "DASHI.Governance.OccupyDeclaredRealizedControlExact"
    "canonicalOccupyDeclaredRealizedBoundary / declaredPurposeDoesNotDetermineRealizedControl"
    "pins the adopted 2011 Principles of Solidarity and Statement of Autonomy from the OccupyWallStreet NYCGA document repository as primary declared-purpose evidence, then proves by an exact finite non-factorability witness that identical declared commitments cannot determine the realised-control consumer"
    "the finite collision is synthetic and creates no empirical OWS control result; leaderless/participatory/transparent/dissent-friendly self-description does not establish the realised authority graph; secondary reconstruction and archival locator identity do not pay missing primary Spokes-minute content"
    "agda -i . DASHI/Governance/OccupyDeclaredRealizedControlRegression.agda"
