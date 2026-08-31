module DASHI.Governance.Lerchner2026AbstractionFallacySourceBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Governance.ConsciousnessAbstractionInstantiationBoundaryExact as Boundary
import DASHI.Governance.EmbodiedLossEmergencyMoralUncertaintyExact as Loss
import DASHI.Governance.EmbodiedSubjectModelInjectionExact as Subject

------------------------------------------------------------------------
-- SOURCE-BOUNDED BRIDGE: LERCHNER 2026, THE ABSTRACTION FALLACY
--
-- Source facts recorded here are bounded metadata / claim summaries.  They do
-- not promote the manuscript into DeepMind policy, peer-reviewed consensus, a
-- kernel theorem, or a complete moral-status decision for artificial systems.
------------------------------------------------------------------------

record SourceReceipt : Set where
  constructor source-receipt
  field
    author : String
    title : String
    date : String
    venueOrHost : String
    identifier : String
    employerDisclaimerPresent : Bool
    peerReviewedJournalArticle : Bool
    boundedRole : String

open SourceReceipt public

lerchner2026Source : SourceReceipt
lerchner2026Source =
  source-receipt
    "Alexander Lerchner"
    "The Abstraction Fallacy: Why AI Can Simulate But Not Instantiate Consciousness"
    "2026-03"
    "Google DeepMind research portal / PhilArchive manuscript"
    "PhilArchive LERTAF; multiple manuscript versions archived in 2026"
    true
    false
    "Source for Lerchner's personal substrate-sensitive argument against computational functionalism; not employer policy, peer-reviewed consensus, or DASHI theorem authority."

------------------------------------------------------------------------
-- Bounded source-claim representation.
------------------------------------------------------------------------

record LerchnerClaimSurface : Set where
  constructor lerchner-claim-surface
  field
    targetsComputationalFunctionalism : Bool
    computationTreatedAsMapmakerDependentAbstraction : Bool
    simulationInstantiationSeparated : Bool
    physicalConstitutionClaimedRelevant : Bool
    biologicalExclusivityClaimed : Bool
    currentDigitalSymbolManipulationClaimedSufficientForExperience : Bool
    artificialConsciousnessInPrincipleExcluded : Bool

open LerchnerClaimSurface public

canonicalLerchnerClaimSurface : LerchnerClaimSurface
canonicalLerchnerClaimSurface =
  lerchner-claim-surface
    true
    true
    true
    true
    false
    false
    false

------------------------------------------------------------------------
-- Source authority boundary.
------------------------------------------------------------------------

record LerchnerSourceAuthorityBoundary : Set where
  constructor lerchner-source-authority-boundary
  field
    hostedOnDeepMindMeansOfficialDeepMindPosition : Bool
    hostedOnDeepMindMeansOfficialDeepMindPositionIsFalse :
      hostedOnDeepMindMeansOfficialDeepMindPosition ≡ false
    manuscriptMeansPeerReviewedConsensus : Bool
    manuscriptMeansPeerReviewedConsensusIsFalse : manuscriptMeansPeerReviewedConsensus ≡ false
    authorUsesProofLanguageMeansAgdaKernelTheorem : Bool
    authorUsesProofLanguageMeansAgdaKernelTheoremIsFalse :
      authorUsesProofLanguageMeansAgdaKernelTheorem ≡ false
    sourceClaimSettlesAllFutureArtificialConsciousness : Bool
    sourceClaimSettlesAllFutureArtificialConsciousnessIsFalse :
      sourceClaimSettlesAllFutureArtificialConsciousness ≡ false
    sourceClaimSettlesMoralStatusPolicy : Bool
    sourceClaimSettlesMoralStatusPolicyIsFalse : sourceClaimSettlesMoralStatusPolicy ≡ false

canonicalLerchnerSourceAuthorityBoundary : LerchnerSourceAuthorityBoundary
canonicalLerchnerSourceAuthorityBoundary =
  lerchner-source-authority-boundary
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Cross-pollination into existing embodied/subject owners.
------------------------------------------------------------------------

abstractionBoundary : Boundary.ConsciousnessAbstractionInstantiationBoundary
abstractionBoundary = Boundary.canonicalConsciousnessAbstractionInstantiationBoundary

lossBoundary : Loss.EmbodiedLossEmergencyBoundary
lossBoundary = Loss.canonicalEmbodiedLossEmergencyBoundary

subjectBoundary : Subject.EmbodiedSubjectModelInjectionBoundary
subjectBoundary = Subject.canonicalEmbodiedSubjectModelInjectionBoundary

record LerchnerDASHICrossPollination : Set where
  constructor lerchner-dashi-cross-pollination
  field
    behaviouralSimulationDistinctFromPhysicalInstantiation : Bool
    abstractFunctionalEquivalenceInsufficientForPhysicalIdentity : Bool
    physicalConstitutionRelevantWithoutBiologicalExclusivity : Bool
    selfDescriptionStillNotPhenomenologyProof : Bool
    replaceableHardwareStillNotNoMoralSubjectProof : Bool
    consciousnessOntologyStillSeparateFromEmergencyAuthority : Bool

canonicalLerchnerDASHICrossPollination : LerchnerDASHICrossPollination
canonicalLerchnerDASHICrossPollination =
  lerchner-dashi-cross-pollination
    true true true true true true
