module DASHI.Biology.SolisSystemSensitivityBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.NeurodivergentSocialEcologySourceRegistryExact as Sources

------------------------------------------------------------------------
-- SOLIS SYSTEM-SENSITIVITY CANDIDATE BOUNDARY
--
-- Provenance discipline is essential here.  The Solis Communicator,
-- "psybernetic dissonance", "sacred data", syntax-checker metaphor, 3-6-9
-- mapping and Solis Phase-Shifted Nash Equilibrium were supplied from prior
-- discussion/conceptual material.  No indexed peer-reviewed source under the
-- Solis name was found in the repository search used for this tranche.
--
-- Therefore this file gives those ideas an explicit candidate carrier and
-- fail-closed boundaries.  It does NOT cite autism literature as if it proved
-- the Solis equations, and it does NOT promote distress into proof of system
-- failure.
------------------------------------------------------------------------

data SystemIntegrity : Set where
  coherentSystem inconsistentSystem : SystemIntegrity

data SignalStrength : Set where
  subThresholdSignal overThresholdSignal : SignalStrength

data SystemRiskFlag : Set where
  noSystemRiskFlag candidateSystemRiskFlag : SystemRiskFlag

data DistressState : Set where
  regulatedDistress elevatedDistress : DistressState

systemicIntegrityCheck : SystemIntegrity → SignalStrength
systemicIntegrityCheck coherentSystem = subThresholdSignal
systemicIntegrityCheck inconsistentSystem = overThresholdSignal

thresholdFlag : SignalStrength → SystemRiskFlag
thresholdFlag subThresholdSignal = noSystemRiskFlag
thresholdFlag overThresholdSignal = candidateSystemRiskFlag

solisCommunicatorCandidate : SystemIntegrity → SystemRiskFlag
solisCommunicatorCandidate system = thresholdFlag (systemicIntegrityCheck system)

inconsistentSystemFlagsCandidateRisk :
  solisCommunicatorCandidate inconsistentSystem ≡ candidateSystemRiskFlag
inconsistentSystemFlagsCandidateRisk = refl

------------------------------------------------------------------------
-- A system-sensitive observer can be represented without universalizing it to
-- all autistic people or treating it as a diagnostic essence.
------------------------------------------------------------------------

data ObserverStyle : Set where
  systemSensitiveObserver otherObserver : ObserverStyle

data AutisticCategory : Set where
  autisticCategory nonAutisticCategory : AutisticCategory

record PersonObserver : Set where
  constructor personObserver
  field
    category : AutisticCategory
    observerStyle : ObserverStyle

open PersonObserver public

data AutismImpliesSystemSensitivityPermission : Set where

autismDoesNotDefinitionallyImplySolisObserver :
  AutismImpliesSystemSensitivityPermission → ⊥
autismDoesNotDefinitionallyImplySolisObserver ()

------------------------------------------------------------------------
-- "Psybernetic dissonance" is preserved as a candidate name for mismatch
-- between an integrity-sensitive observer and an incoherent system.  It is not
-- installed as a clinical construct or validated trauma diagnosis.
------------------------------------------------------------------------

data Dissonance : Set where
  lowDissonance highCandidatePsyberneticDissonance : Dissonance

candidateDissonance : ObserverStyle → SystemIntegrity → Dissonance
candidateDissonance systemSensitiveObserver coherentSystem = lowDissonance
candidateDissonance systemSensitiveObserver inconsistentSystem = highCandidatePsyberneticDissonance
candidateDissonance otherObserver system = lowDissonance

data DistressProvesSystemCollapsePermission : Set where

distressDoesNotProveSystemCollapse : DistressProvesSystemCollapsePermission → ⊥
distressDoesNotProveSystemCollapse ()

------------------------------------------------------------------------
-- "Sacred data" / syntax-checker metaphor is typed as an epistemic stance:
-- distressed reports may carry information worth preserving and investigating.
-- It is not a theorem that every distress signal is correct or system-caused.
------------------------------------------------------------------------

data DistressEvidencePolicy : Set where
  discardAsNoise preserveForInquiry : DistressEvidencePolicy

solisEvidencePolicy : DistressState → DistressEvidencePolicy
solisEvidencePolicy regulatedDistress = preserveForInquiry
solisEvidencePolicy elevatedDistress = preserveForInquiry

data PreservedDistressIsInfalliblePermission : Set where

preservingDistressDoesNotMakeItInfallible :
  PreservedDistressIsInfalliblePermission → ⊥
preservingDistressDoesNotMakeItInfallible ()

------------------------------------------------------------------------
-- Candidate 3-6-9 analogy.
------------------------------------------------------------------------

data SolisStage : Set where
  stage3Assessment stage6Accumulation stage9Reorganisation : SolisStage

data Solis369IsBase369TheoremPermission : Set where

solis369AnalogyDoesNotAutoPromoteToBase369Theorem :
  Solis369IsBase369TheoremPermission → ⊥
solis369AnalogyDoesNotAutoPromoteToBase369Theorem ()

data ThresholdEqualsPadicMinusHalfPermission : Set where

thresholdDoesNotAutoEqualPadicMinusHalf :
  ThresholdEqualsPadicMinusHalfPermission → ⊥
thresholdDoesNotAutoEqualPadicMinusHalf ()

------------------------------------------------------------------------
-- Candidate economic analogy.  The name SPNE is retained for provenance, but
-- no Nash-equilibrium theorem or market-efficiency result is claimed here.
------------------------------------------------------------------------

data MarketPhase : Set where
  incumbentAdvantage temporaryRedistribution expandedVertical : MarketPhase

data SPNEIsGameTheoreticNashProofPermission : Set where

spneNameDoesNotInstallNashProof :
  SPNEIsGameTheoreticNashProofPermission → ⊥
spneNameDoesNotInstallNashProof ()

record SolisBoundary : Set where
  constructor solisBoundary
  field
    conceptHasUserSuppliedProvenance : Bool
    conceptHasUserSuppliedProvenanceIsTrue : conceptHasUserSuppliedProvenance ≡ true
    peerReviewedSolisAutismMechanismInstalled : Bool
    peerReviewedSolisAutismMechanismInstalledIsFalse : peerReviewedSolisAutismMechanismInstalled ≡ false
    everyAutisticPersonIsSystemChecker : Bool
    everyAutisticPersonIsSystemCheckerIsFalse : everyAutisticPersonIsSystemChecker ≡ false
    autisticDistressProvesExternalSystemFailure : Bool
    autisticDistressProvesExternalSystemFailureIsFalse : autisticDistressProvesExternalSystemFailure ≡ false
    distressCanBePreservedAsPotentiallyInformativeEvidence : Bool
    distressCanBePreservedAsPotentiallyInformativeEvidenceIsTrue :
      distressCanBePreservedAsPotentiallyInformativeEvidence ≡ true
    solis369IsEstablishedBase369Identity : Bool
    solis369IsEstablishedBase369IdentityIsFalse : solis369IsEstablishedBase369Identity ≡ false
    spneIsEstablishedNashEquilibriumTheorem : Bool
    spneIsEstablishedNashEquilibriumTheoremIsFalse : spneIsEstablishedNashEquilibriumTheorem ≡ false

canonicalSolisBoundary : SolisBoundary
canonicalSolisBoundary =
  solisBoundary true refl false refl false refl false refl true refl false refl false refl

solisProvenance : Sources.SolisConceptProvenance
solisProvenance = Sources.solisConversationConcept

systemizingLiteratureContext : Sources.SourceReference
systemizingLiteratureContext = Sources.systemizing2009

neuroqueerLiteratureContext : Sources.SourceReference
neuroqueerLiteratureContext = Sources.neuroqueer2021
