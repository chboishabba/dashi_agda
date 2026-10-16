module DASHI.Governance.ITIRNonDominationReappropriationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.AnarchistAntiLeadershipSourceAtlasExact as Sources
import DASHI.Governance.OccupyPseudonymousNetworkFeaturesExact as OccupyNetwork
import DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact as GodsEye

------------------------------------------------------------------------
-- ITIR NON-DOMINATION / REAPPROPRIATION BRIDGE
--
-- This is a DASHI governance construction. It does not attribute the resulting
-- formalism to any one anarchist/socialist source, and it does not claim that
-- a political identity, party label, demographic identity or controller class
-- can certify non-domination.
--
-- Governing distinction:
--   useful coordination / expertise / facilitation / delegation
--   != durable arbitrary command over others.
--
-- Reappropriating an information/cybernetic capability means changing its
-- authority, visibility, contestability and purpose conditions. Merely changing
-- the person or ideology controlling the same unilateral architecture is not a
-- proof of non-domination.
------------------------------------------------------------------------

data CoordinationRole : Set where
  facilitator : CoordinationRole
  rotatingSituationalExpert : CoordinationRole
  scopedDelegate : CoordinationRole
  accountableRepresentative : CoordinationRole
  durableController : CoordinationRole

data AuthorityShape : Set where
  informalInfluence : AuthorityShape
  revocableDelegation : AuthorityShape
  scopedMandate : AuthorityShape
  unilateralCommand : AuthorityShape

record NonDominationOperationalReceipt : Set₁ where
  constructor non-domination-operational-receipt
  field
    roleVisibility : Set
    mandateScope : Set
    revocability : Set
    contestability : Set
    affectedPartyVoice : Set
    evidenceInspectability : Set
    unilateralAuthorityBound : Set
    exitOrAppealPath : Set

open NonDominationOperationalReceipt public

-- No canonical inhabitant is provided. A real deployment must pay these
-- coordinates on the same institutional object rather than inherit the label
-- "horizontal", "anarchist", "socialist" or "democratic".

record ReappropriatedCapabilityReceipt : Set₁ where
  constructor reappropriated-capability-receipt
  field
    capabilityReference : String
    formerAuthorityReference : String
    newAuthorityReference : String
    accountabilityReference : String
    affectedConstituencyReference : String
    purposeLimitationReference : String
    nonDominationReceipt : NonDominationOperationalReceipt

open ReappropriatedCapabilityReceipt public

------------------------------------------------------------------------
-- Accountability target.
--
-- Anti-panopticon does NOT mean eliminating observability of consequential
-- power. It means that observation remains scoped, provenance-bearing and
-- authority-separated, while people subject to consequential decisions retain
-- inspectable evidence and contestability routes.
------------------------------------------------------------------------

data AccountabilityTarget : Set where
  consequentialPowerHolder : AccountabilityTarget
  delegatedDecisionProcess : AccountabilityTarget
  sharedInfrastructure : AccountabilityTarget
  ordinaryParticipant : AccountabilityTarget
  privateLifeOutsideDeclaredConsumer : AccountabilityTarget

accountabilityPriority : AccountabilityTarget → Bool
accountabilityPriority consequentialPowerHolder = true
accountabilityPriority delegatedDecisionProcess = true
accountabilityPriority sharedInfrastructure = true
accountabilityPriority ordinaryParticipant = false
accountabilityPriority privateLifeOutsideDeclaredConsumer = false

consequentialPowerIsAccountabilityPriority :
  accountabilityPriority consequentialPowerHolder ≡ true
consequentialPowerIsAccountabilityPriority = refl

privateLifeIsNotDefaultAccountabilityTarget :
  accountabilityPriority privateLifeOutsideDeclaredConsumer ≡ false
privateLifeIsNotDefaultAccountabilityTarget = refl

------------------------------------------------------------------------
-- Existing exact anchors.
------------------------------------------------------------------------

sourceBoundaryAnchor : Sources.AnarchistLeadershipSourceBoundary
sourceBoundaryAnchor = Sources.canonicalAnarchistLeadershipSourceBoundary

occupyNetworkBoundaryAnchor : OccupyNetwork.NetworkFeatureBoundary
occupyNetworkBoundaryAnchor = OccupyNetwork.canonicalNetworkFeatureBoundary

antiPanopticonAnchor : GodsEye.AntiPanopticonBoundary
antiPanopticonAnchor = GodsEye.canonicalAntiPanopticonBoundary

antiPanopticonRequiresInspectableEvidence :
  GodsEye.evidencePathMustRemainInspectable antiPanopticonAnchor ≡ true
antiPanopticonRequiresInspectableEvidence = refl

antiPanopticonDoesNotCreateInterventionAuthority :
  GodsEye.observationCreatesInterventionAuthority antiPanopticonAnchor ≡ false
antiPanopticonDoesNotCreateInterventionAuthority = refl

------------------------------------------------------------------------
-- Terminal boundary.
------------------------------------------------------------------------

record ReappropriationBoundary : Set where
  constructor reappropriation-boundary
  field
    controllerIdentityPaysNonDomination : Bool
    controllerIdeologyPaysNonDomination : Bool
    representativeDemographicsPayNonDomination : Bool
    leadershipFunctionEqualsDurableController : Bool
    facilitationEqualsUnilateralCommand : Bool
    expertiseEqualsSovereignAuthority : Bool
    changingControllerReappropriatesArchitecture : Bool
    capabilitySimilarityTransfersAuthority : Bool

    accountabilityTargetsConsequentialPower : Bool
    ordinaryParticipantsAreDefaultSurveillanceTargets : Bool
    privateLifeIsDefaultSurveillanceTarget : Bool
    affectedVoiceAndContestabilityRemainRequired : Bool
    provenanceAndEvidenceInspectabilityRemainRequired : Bool

open ReappropriationBoundary public

canonicalReappropriationBoundary : ReappropriationBoundary
canonicalReappropriationBoundary =
  reappropriation-boundary
    false false false false false false false false
    true false false true true

canonicalITIRNonDominationReceipt : GenericReceipt.GenericReceipt
canonicalITIRNonDominationReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "ITIR non-domination / reappropriation bridge"
    "DASHI.Governance.ITIRNonDominationReappropriationExact"
    "canonicalReappropriationBoundary"
    "separates facilitation, rotating expertise, scoped delegation and representation from durable arbitrary command; requires same-object transparency, revocability, contestability, affected-party voice and inspectable evidence before a reappropriated capability can be called non-dominating"
    "controller identity or ideology does not pay non-domination; changing personnel does not by itself reappropriate an authority architecture; anti-panopticon accountability targets consequential power rather than making ordinary participants or private life default surveillance targets"
    "agda -i . DASHI/Governance/AnarchistLeadershipNonDominationTSFVRegression.agda"
