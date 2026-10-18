module DASHI.Biology.PMDDHistamineAmplificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Biology.NeurochemicalVocabularyReceipt as Vocabulary
import DASHI.Biology.NeurochemicalAtomicChemistryBridge as AtomicChem

------------------------------------------------------------------------
-- PMDD / HISTAMINE AMPLIFICATION HYPOTHESIS
--
-- This module deliberately does NOT formalise "histamine causes PMDD".
-- It separates:
--
--   (1) source-attributed external observations,
--   (2) existing candidate-only molecular / receptor vocabulary,
--   (3) repo-native cross-source synthesis:
--
--         steroid-sensitive PMDD state
--              +
--         histamine-sensitive signalling state
--              |
--              v
--         possible symptom amplification
--
-- The synthesis is a testable candidate.  It carries no diagnostic,
-- therapeutic, biomarker, prevalence, efficacy, or root-cause authority.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Source attribution.
------------------------------------------------------------------------

hantsooEpperson2020 : Source.AttributedSource
hantsooEpperson2020 =
  Source.mkDOISource
    "Liisa Hantsoo; C. Neill Epperson"
    "Allopregnanolone in premenstrual dysphoric disorder (PMDD): Evidence for dysregulated sensitivity to GABA-A receptor modulating neuroactive steroids across the menstrual cycle"
    "Neurobiology of Stress"
    "2020"
    "10.1016/j.ynstr.2020.100213"
    "https://pubmed.ncbi.nlm.nih.gov/32435664/"
    Source.academicArticleSource
    "External review source for the ALLO / GABA_A steroid-sensitivity account of PMDD; citation does not import a universal mechanism theorem."
    Source.publicAttribution

zaitsuEtAl2007 : Source.AttributedSource
zaitsuEtAl2007 =
  Source.mkDOISource
    "Masafumi Zaitsu et al."
    "Estradiol activates mast cells via a non-genomic estrogen receptor-alpha and calcium influx"
    "Molecular Immunology"
    "2007"
    "10.1016/j.molimm.2006.09.030"
    "https://pubmed.ncbi.nlm.nih.gov/17084457/"
    Source.academicArticleSource
    "External cellular source for estradiol-sensitive mast-cell activation under its reported experimental conditions; not a PMDD study."
    Source.publicAttribution

ito2000 : Source.AttributedSource
ito2000 =
  Source.mkDOISource
    "Chiaki Ito"
    "The role of brain histamine in acute and chronic stresses"
    "Biomedicine & Pharmacotherapy"
    "2000"
    "10.1016/S0753-3322(00)80069-4"
    "https://pubmed.ncbi.nlm.nih.gov/10917464/"
    Source.academicArticleSource
    "External review source for stress-sensitive brain histamine signalling; not evidence that histamine is necessary or sufficient for PMDD."
    Source.publicAttribution

doseClinicReel : Source.AttributedSource
doseClinicReel =
  Source.mkNoDOISource
    "Sera Ghaly / The Dose Clinic"
    "Instagram reel on antihistamines, PMDD, histamine and gut root-cause framing"
    "Instagram / The Dose Clinic"
    "2026"
    "https://www.instagram.com/reel/Dc-dwJAuatg/"
    Source.practitionerSource
    "Practitioner-source prompt for the histamine-amplified PMDD synthesis. The reel's stronger diagnostic/root-cause claims are not promoted."
    Source.publicAttribution

canonicalPMDDHistamineSourceAtlas : Source.AttributedSourceAtlas
canonicalPMDDHistamineSourceAtlas =
  Source.mkSourceAtlas
    "PMDD histamine amplification source atlas"
    "DASHI.Biology.PMDDHistamineAmplificationExact"
    (hantsooEpperson2020
      ∷ zaitsuEtAl2007
      ∷ ito2000
      ∷ doseClinicReel
      ∷ [])
    "Separates PMDD steroid-sensitivity evidence, mast-cell hormone sensitivity, histamine/stress physiology, and practitioner interpretation. Cross-source synthesis remains repo-native and non-promoting."

------------------------------------------------------------------------
-- Existing repo machinery is consumed, not reimplemented.
------------------------------------------------------------------------

histamineVocabularyRow : CandidateOnly.CandidateOnlyRow
histamineVocabularyRow =
  Vocabulary.histamineCandidate

histamineVocabularyReceipt :
  CandidateOnly.CandidateOnlyReceipt histamineVocabularyRow
histamineVocabularyReceipt =
  Vocabulary.histamineCandidateReceipt

atomicChemistryOwner :
  AtomicChem.NeurochemicalAtomicChemistryBridge
atomicChemistryOwner =
  AtomicChem.canonicalNeurochemicalAtomicChemistryBridge

atomicChemistrySlots :
  List AtomicChem.NeurochemicalAtomicChemistrySlot
atomicChemistrySlots =
  AtomicChem.canonicalNeurochemicalAtomicChemistrySlots

------------------------------------------------------------------------
-- Evidence layers.
------------------------------------------------------------------------

data EvidenceLayer : Set where
  externalSourceObservation : EvidenceLayer
  sourceBoundMechanisticObservation : EvidenceLayer
  dashiCrossSourceSynthesis : EvidenceLayer
  untestedClinicalSubtypeHypothesis : EvidenceLayer

data MechanismNode : Set where
  ovarianSteroidTransition : MechanismNode
  alloGABAAResponse : MechanismNode
  stressSensitivity : MechanismNode
  estradiolSensitiveMastCellState : MechanismNode
  histamineSignallingState : MechanismNode
  peripheralHistamineLoad : MechanismNode
  symptomAmplification : MechanismNode
  pmddPhenotype : MechanismNode

record SourceBoundEdge : Set where
  constructor sourceBoundEdge
  field
    from : MechanismNode
    to : MechanismNode
    layer : EvidenceLayer
    source : Source.AttributedSource
    sourceReading : String
    universalPopulationClaim : Bool
    universalPopulationClaimIsFalse :
      universalPopulationClaim ≡ false

open SourceBoundEdge public

pmddSteroidSensitivityEdge : SourceBoundEdge
pmddSteroidSensitivityEdge =
  sourceBoundEdge
    ovarianSteroidTransition
    alloGABAAResponse
    externalSourceObservation
    hantsooEpperson2020
    "PMDD review literature supports dysregulated sensitivity to dynamic allopregnanolone / GABA_A signalling across the menstrual cycle."
    false refl

alloStressEdge : SourceBoundEdge
alloStressEdge =
  sourceBoundEdge
    alloGABAAResponse
    stressSensitivity
    sourceBoundMechanisticObservation
    hantsooEpperson2020
    "The source reviews impaired ALLO-GABA regulation of physiologic stress response in PMDD."
    false refl

estradiolMastCellEdge : SourceBoundEdge
estradiolMastCellEdge =
  sourceBoundEdge
    ovarianSteroidTransition
    estradiolSensitiveMastCellState
    sourceBoundMechanisticObservation
    zaitsuEtAl2007
    "Physiological estradiol activated or potentiated mast-cell mediator release in the reported cellular / primary-culture systems."
    false refl

histamineStressEdge : SourceBoundEdge
histamineStressEdge =
  sourceBoundEdge
    histamineSignallingState
    stressSensitivity
    sourceBoundMechanisticObservation
    ito2000
    "The review reports stress-sensitive brain histamine turnover and histamine participation in stress-related signalling."
    false refl

canonicalExternalEdges : List SourceBoundEdge
canonicalExternalEdges =
  pmddSteroidSensitivityEdge
  ∷ alloStressEdge
  ∷ estradiolMastCellEdge
  ∷ histamineStressEdge
  ∷ []

------------------------------------------------------------------------
-- DASHI synthesis.
--
-- No source above directly establishes this conjunction.  This is therefore
-- represented explicitly as a candidate composition rather than smuggled into
-- an external-source theorem.
------------------------------------------------------------------------

record HistamineAmplifiedPMDDCandidate : Set where
  constructor histamineAmplifiedPMDDCandidate
  field
    pmddPrimaryLane : MechanismNode
    histamineModifierLane : MechanismNode
    jointOutcome : MechanismNode

    evidence : List SourceBoundEdge

    steroidSensitivityPrimary : Bool
    steroidSensitivityPrimaryIsTrue :
      steroidSensitivityPrimary ≡ true

    histamineIsModifierNotUniversalCause : Bool
    histamineIsModifierNotUniversalCauseIsTrue :
      histamineIsModifierNotUniversalCause ≡ true

    interactionRequiresDirectTesting : Bool
    interactionRequiresDirectTestingIsTrue :
      interactionRequiresDirectTesting ≡ true

    h1h2ResponseIsDiagnosticProof : Bool
    h1h2ResponseIsDiagnosticProofIsFalse :
      h1h2ResponseIsDiagnosticProof ≡ false

    gutDysfunctionIsUniversalRootCause : Bool
    gutDysfunctionIsUniversalRootCauseIsFalse :
      gutDysfunctionIsUniversalRootCause ≡ false

    clinicalEfficacyEstablished : Bool
    clinicalEfficacyEstablishedIsFalse :
      clinicalEfficacyEstablished ≡ false

    therapeuticRecommendationImported : Bool
    therapeuticRecommendationImportedIsFalse :
      therapeuticRecommendationImported ≡ false

    synthesisReading : String

open HistamineAmplifiedPMDDCandidate public

canonicalHistamineAmplifiedPMDDCandidate :
  HistamineAmplifiedPMDDCandidate
canonicalHistamineAmplifiedPMDDCandidate =
  histamineAmplifiedPMDDCandidate
    alloGABAAResponse
    histamineSignallingState
    symptomAmplification
    canonicalExternalEdges
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "DASHI synthesis candidate: in a steroid-sensitive PMDD state, independently variable histamine / mast-cell / stress signalling may act as an amplifier of symptom burden in a subset. This is a cross-source mechanistic hypothesis, not an externally established disease mechanism."

------------------------------------------------------------------------
-- Explicit anti-collapse theorems.
------------------------------------------------------------------------

data HistamineCausesAllPMDD : Set where
data AntihistamineResponseDiagnosesHistaminePMDD : Set where
data GutDysfunctionIsThePMDDRootCause : Set where
data CellularEstradiolMastCellResultIsClinicalPMDDProof : Set where
data SourceCompositionAutomaticallyCreatesClinicalAuthority : Set where

histamineDoesNotBecomeUniversalCause :
  HistamineCausesAllPMDD → ⊥
histamineDoesNotBecomeUniversalCause ()

antihistamineResponseIsNotDiagnosticProof :
  AntihistamineResponseDiagnosesHistaminePMDD → ⊥
antihistamineResponseIsNotDiagnosticProof ()

gutRootCauseNotPromoted :
  GutDysfunctionIsThePMDDRootCause → ⊥
gutRootCauseNotPromoted ()

cellularMastCellResultDoesNotBecomePMDDProof :
  CellularEstradiolMastCellResultIsClinicalPMDDProof → ⊥
cellularMastCellResultDoesNotBecomePMDDProof ()

crossSourceCompositionDoesNotCreateClinicalAuthority :
  SourceCompositionAutomaticallyCreatesClinicalAuthority → ⊥
crossSourceCompositionDoesNotCreateClinicalAuthority ()

------------------------------------------------------------------------
-- Testable frontier.
------------------------------------------------------------------------

record PMDDHistamineExperimentalFrontier : Set where
  constructor pmddHistamineExperimentalFrontier
  field
    prospectiveCycleTracking : String
    histamineLaneMeasurement : String
    steroidLaneMeasurement : String
    interventionProtocol : String
    interactionTest : String
    subtypeReplication : String

canonicalPMDDHistamineExperimentalFrontier :
  PMDDHistamineExperimentalFrontier
canonicalPMDDHistamineExperimentalFrontier =
  pmddHistamineExperimentalFrontier
    "prospective within-person symptom tracking across multiple menstrual cycles"
    "protocol-indexed histamine / mast-cell / receptor-relevant readouts with timing preserved"
    "cycle phase plus ovarian-steroid / neurosteroid measurements sufficient to bind the steroid-transition lane"
    "pre-specified controlled intervention rather than retrospective response attribution"
    "test whether the histamine lane explains incremental symptom variance or modifies the steroid-sensitive lane"
    "replicate any apparent responder subgroup before treating it as a biological subtype"
