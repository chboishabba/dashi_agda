module DASHI.Biology.SolisSystemSensitivityBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Biology.NeurodivergentSocialEcologySourceRegistryExact as Sources

------------------------------------------------------------------------
-- SOLIS COMMUNICATOR NOTATION: EXACT MINIMAL CONTROL CORE
--
-- Provenance has two distinct layers.
--
-- 1. The Solis/SCN naming and equations are archived conceptual material from
--    chboishabba/dashiTRADE, locally reported in
--      ignore.TRADER_CANTEXT.md around lines 61211--62174,
--    including the 0.5 threshold, the schematic
--      AutisticSignal[x] := Check[SystemicIntegrity[x]],
--    and collapse-risk / qPARA handling.
--    The ignored archive is not asserted here to be a scholarly source.
--
-- 2. Historical DASHI commit
--      2f45a6da102cf582503281ace8c508031f17fdbb
--    contains related formal substrate such as
--      DASHI/Cognition/PsychedelicNetworkDiffusion.agda
--      DASHI/Cognition/NetworkIntegritySynchronyMetrics.agda
--    and neighbouring cognition modules.  Those owners separate network
--    integrity, cross-system communication, synchrony, perturbation metrics and
--    ternary commitment.  They were not a standalone SCN implementation.
--
-- This file therefore installs the missing minimal SCN control logic while
-- preserving a strict boundary: the threshold mathematics is exact; the
-- empirical definition of an autism-relevant integrity functional is NOT.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Finite exact [0,1] half-grid.
--
-- This is the smallest carrier that represents 0, 1/2 and 1 exactly and makes
-- the archive's theta = 1/2 decision boundary executable without importing an
-- unrelated real-number stack.  A later rational/real owner may refine it.
------------------------------------------------------------------------

data UnitIntervalHalfGrid : Set where
  zeroScore halfScore oneScore : UnitIntervalHalfGrid

complementScore : UnitIntervalHalfGrid → UnitIntervalHalfGrid
complementScore zeroScore = oneScore
complementScore halfScore = halfScore
complementScore oneScore = zeroScore

scoreNumeratorOverTwo : UnitIntervalHalfGrid → Nat
scoreNumeratorOverTwo zeroScore = 0
scoreNumeratorOverTwo halfScore = 1
scoreNumeratorOverTwo oneScore = 2

record MeasuredSystem (State : Set) : Set where
  constructor measuredSystem
  field
    integrityScore : State → UnitIntervalHalfGrid

open MeasuredSystem public

incoherenceScore :
  ∀ {State : Set} → MeasuredSystem State → State → UnitIntervalHalfGrid
incoherenceScore measurement state =
  complementScore (integrityScore measurement state)

atOrAboveHalf : UnitIntervalHalfGrid → Bool
atOrAboveHalf zeroScore = false
atOrAboveHalf halfScore = true
atOrAboveHalf oneScore = true

atOrBelowHalf : UnitIntervalHalfGrid → Bool
atOrBelowHalf zeroScore = true
atOrBelowHalf halfScore = true
atOrBelowHalf oneScore = false

doubledAtLeastOne : UnitIntervalHalfGrid → Bool
doubledAtLeastOne score = atOrAboveHalf score

------------------------------------------------------------------------
-- Total SCN checker.
------------------------------------------------------------------------

data SCNDecision : Set where
  continueDecision flagAndBifurcateDecision : SCNDecision

scnDecisionFromIncoherence : UnitIntervalHalfGrid → SCNDecision
scnDecisionFromIncoherence zeroScore = continueDecision
scnDecisionFromIncoherence halfScore = flagAndBifurcateDecision
scnDecisionFromIncoherence oneScore = flagAndBifurcateDecision

SCN :
  ∀ {State : Set} → MeasuredSystem State → State → SCNDecision
SCN measurement state =
  scnDecisionFromIncoherence (incoherenceScore measurement state)

scnFlagIndicator : SCNDecision → Bool
scnFlagIndicator continueDecision = false
scnFlagIndicator flagAndBifurcateDecision = true

------------------------------------------------------------------------
-- Exact threshold soundness on the half-grid:
--
--   SCN flags  <=>  2 A >= 1  <=>  I <= 1/2.
--
-- The proof is represented as equality of the three total Boolean decisions.
------------------------------------------------------------------------

scnFlagIffDoubledIncoherenceAtLeastOne :
  ∀ {State : Set}
    (measurement : MeasuredSystem State)
    (state : State) →
  scnFlagIndicator (SCN measurement state)
  ≡ doubledAtLeastOne (incoherenceScore measurement state)
scnFlagIffDoubledIncoherenceAtLeastOne measurement state
  with integrityScore measurement state
... | zeroScore = refl
... | halfScore = refl
... | oneScore = refl

doubledIncoherenceThresholdIffIntegrityAtMostHalf :
  ∀ {State : Set}
    (measurement : MeasuredSystem State)
    (state : State) →
  doubledAtLeastOne (incoherenceScore measurement state)
  ≡ atOrBelowHalf (integrityScore measurement state)
doubledIncoherenceThresholdIffIntegrityAtMostHalf measurement state
  with integrityScore measurement state
... | zeroScore = refl
... | halfScore = refl
... | oneScore = refl

scnThresholdSoundness :
  ∀ {State : Set}
    (measurement : MeasuredSystem State)
    (state : State) →
  scnFlagIndicator (SCN measurement state)
  ≡ atOrBelowHalf (integrityScore measurement state)
scnThresholdSoundness measurement state =
  trans
    (scnFlagIffDoubledIncoherenceAtLeastOne measurement state)
    (doubledIncoherenceThresholdIffIntegrityAtMostHalf measurement state)

------------------------------------------------------------------------
-- Independent paradox/consistency gate.
--
-- The archive's qPARA/collapse-risk material is represented conservatively as
-- an independent Boolean paradox detector.  Quarantine has precedence over the
-- half-threshold bifurcation.  This is control logic, not a clinical judgment.
------------------------------------------------------------------------

data SCNAction : Set where
  continueAction bifurcateAction quarantineAction : SCNAction

SCNActionFor :
  ∀ {State : Set} →
  MeasuredSystem State →
  (State → Bool) →
  State → SCNAction
SCNActionFor measurement paradoxDetected state with paradoxDetected state
... | true = quarantineAction
... | false with SCN measurement state
...   | continueDecision = continueAction
...   | flagAndBifurcateDecision = bifurcateAction

quarantineHasPriority :
  ∀ {State : Set}
    (measurement : MeasuredSystem State)
    (paradoxDetected : State → Bool)
    (state : State) →
  paradoxDetected state ≡ true →
  SCNActionFor measurement paradoxDetected state ≡ quarantineAction
quarantineHasPriority measurement paradoxDetected state proof
  with paradoxDetected state
... | true = refl
... | false = λ ()

------------------------------------------------------------------------
-- Honest transition-safety contract.
--
-- Threshold logic alone cannot prove that a system transition preserves a
-- domain-specific safety predicate.  The needed theorem therefore consumes an
-- explicit preservation certificate.  This keeps the missing empirical / model
-- semantics visible rather than hiding it in the checker.
------------------------------------------------------------------------

record ContinueSafetyCertificate
    {State : Set}
    (measurement : MeasuredSystem State)
    (paradoxDetected : State → Bool)
    (Step : State → State → Set)
    (Safe : State → Set) : Set where
  constructor continueSafetyCertificate
  field
    continueStepPreservesSafety :
      ∀ {x y : State} →
      Safe x →
      SCNActionFor measurement paradoxDetected x ≡ continueAction →
      Step x y →
      Safe y

open ContinueSafetyCertificate public

scnContinueSafety :
  ∀ {State : Set}
    {measurement : MeasuredSystem State}
    {paradoxDetected : State → Bool}
    {Step : State → State → Set}
    {Safe : State → Set} →
  ContinueSafetyCertificate measurement paradoxDetected Step Safe →
  ∀ {x y : State} →
  Safe x →
  SCNActionFor measurement paradoxDetected x ≡ continueAction →
  Step x y →
  Safe y
scnContinueSafety certificate = continueStepPreservesSafety certificate

------------------------------------------------------------------------
-- Historical substrate receipt.
------------------------------------------------------------------------

record HistoricalSCNSubstrate : Set where
  constructor historicalSCNSubstrate
  field
    commit : String
    archiveRepository : String
    archivePath : String
    integrityOwner : String
    networkOwner : String
    standaloneSCNPresent : Bool

open HistoricalSCNSubstrate public

canonicalHistoricalSCNSubstrate : HistoricalSCNSubstrate
canonicalHistoricalSCNSubstrate = historicalSCNSubstrate
  "2f45a6da102cf582503281ace8c508031f17fdbb"
  "chboishabba/dashiTRADE"
  "ignore.TRADER_CANTEXT.md:61211-62174 (user-supplied local archive location)"
  "DASHI/Cognition/NetworkIntegritySynchronyMetrics.agda"
  "DASHI/Cognition/PsychedelicNetworkDiffusion.agda"
  false

------------------------------------------------------------------------
-- Older qualitative Solis carrier retained for compatibility with the current
-- neurodivergent/social-ecology cross-pollination owner.
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

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record SolisBoundary : Set where
  constructor solisBoundary
  field
    conceptHasArchiveProvenance : Bool
    conceptHasArchiveProvenanceIsTrue : conceptHasArchiveProvenance ≡ true
    historicalFormalSubstrateLocated : Bool
    historicalFormalSubstrateLocatedIsTrue : historicalFormalSubstrateLocated ≡ true
    exactHalfThresholdControlLogicInstalled : Bool
    exactHalfThresholdControlLogicInstalledIsTrue : exactHalfThresholdControlLogicInstalled ≡ true
    empiricalIntegrityFunctionalInstalled : Bool
    empiricalIntegrityFunctionalInstalledIsFalse : empiricalIntegrityFunctionalInstalled ≡ false
    peerReviewedSolisAutismMechanismInstalled : Bool
    peerReviewedSolisAutismMechanismInstalledIsFalse : peerReviewedSolisAutismMechanismInstalled ≡ false
    everyAutisticPersonIsSystemChecker : Bool
    everyAutisticPersonIsSystemCheckerIsFalse : everyAutisticPersonIsSystemChecker ≡ false
    autisticDistressProvesExternalSystemFailure : Bool
    autisticDistressProvesExternalSystemFailureIsFalse : autisticDistressProvesExternalSystemFailure ≡ false
    distressCanBePreservedAsPotentiallyInformativeEvidence : Bool
    distressCanBePreservedAsPotentiallyInformativeEvidenceIsTrue :
      distressCanBePreservedAsPotentiallyInformativeEvidence ≡ true
    thresholdLogicAloneProvesTransitionSafety : Bool
    thresholdLogicAloneProvesTransitionSafetyIsFalse :
      thresholdLogicAloneProvesTransitionSafety ≡ false
    solis369IsEstablishedBase369Identity : Bool
    solis369IsEstablishedBase369IdentityIsFalse : solis369IsEstablishedBase369Identity ≡ false
    spneIsEstablishedNashEquilibriumTheorem : Bool
    spneIsEstablishedNashEquilibriumTheoremIsFalse : spneIsEstablishedNashEquilibriumTheorem ≡ false

canonicalSolisBoundary : SolisBoundary
canonicalSolisBoundary =
  solisBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl
    false refl

solisProvenance : Sources.SolisConceptProvenance
solisProvenance = Sources.solisConversationConcept

systemizingLiteratureContext : Sources.SourceReference
systemizingLiteratureContext = Sources.systemizing2009

neuroqueerLiteratureContext : Sources.SourceReference
neuroqueerLiteratureContext = Sources.neuroqueer2021
