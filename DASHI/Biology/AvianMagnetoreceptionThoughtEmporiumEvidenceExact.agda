module DASHI.Biology.AvianMagnetoreceptionThoughtEmporiumEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.ScientificMechanismEvidenceBidiExact as Science
import DASHI.Biology.AvianMagnetoreceptionStreamFiniteCore as Finite
import DASHI.Biology.MagnetoreceptionSurface as Generic
import DASHI.Biology.AvianCryptochromeMagnetoreceptionInhabitant as CRY
import DASHI.Biology.AvianHepaticMacrophageMagnetoreception as Hepatic
import DASHI.Biology.AvianMagnetoreceptionSourceRegistry as Registry
import DASHI.Biology.AvianRFOverlayMechanismAdapter as RF

------------------------------------------------------------------------
-- THE THOUGHT EMPORIUM 2020 / AVIAN MAGNETORECEPTION BIDI
--
-- Stream provided by user (17 June 2020):
-- The Thought Emporium, "Genetic Modification To Sense Magnetic Fields -
-- Whose Gene #11", a science discussion, not an implemented human
-- magnetoreception experiment.
--
-- Study authors and original mechanism/evidence owners keep attribution:
-- Nimpf et al. (2019) pigeon vestibular electromagnetic induction;
-- Xu, Jarocha, Zollitsch et al. (2021) European robin CRY4 in vitro;
-- Nordmann, Balay, Kapuruge et al. (2025 online / 2026 issue) pigeon
-- brain/vestibular activity; Lisowski et al. (2026) pigeon hepatic
-- macrophages; Wang et al. (2019) human EEG geomagnetic response.
--
-- No sequence, guide RNA, promoter, AAV, vector, target editing, in vivo
-- dosing, tissue injection or experimental construction instructions.
------------------------------------------------------------------------

thoughtEmporium2020 : Source.AttributedSource
thoughtEmporium2020 =
  Source.mkNoDOISource
    "The Thought Emporium (presenter/creator; Whose Gene #11)"
    "Genetic Modification To Sense Magnetic Fields - Whose Gene #11"
    "YouTube livestream; streamed 2020-06-17; user-provided transcript"
    "2020"
    "https://www.youtube.com/@thethoughtemporium"
    (Source.namedSourceKind "science outreach livestream")
    "Creator proposes a hypothetical biological magnetoreception modification, discusses MagR/CRY4, pigeon vestibular channel hypothesis and human EEG. The speculative edit and its effectiveness were not experimentally demonstrated in the stream."
    Source.publicAttribution

nimpfEtAl2019 : Source.AttributedSource
nimpfEtAl2019 =
  Source.mkDOISource
    "Simon Nimpf; Gregory Charles Nordmann; Daniel Kagerbauer; Erich Pascal Malkemper; Lukas Landler; Artemis Papadaki-Anastasopoulou; Lyubov Ushakova; Andrea Wenninger-Weinzierl; Maria Novatchkova; Peter Vincent; Thomas Lendl; Martin Colombini; Matthew J Mason; David Anthony Keays"
    "A putative mechanism for magnetoreception by electromagnetic induction in the pigeon inner ear"
    "Current Biology 29(23):4052-4059.e4"
    "2019"
    "10.1016/j.cub.2019.09.048"
    "https://doi.org/10.1016/j.cub.2019.09.048"
    Source.academicArticleSource
    "Pigeon light-independent vestibular nucleus activation, physical induction modelling, CaV1.3 isoform/electroreceptive machinery. Authors propose inner-ear induction; direct complete magnetic receptor-to-navigation causal sufficiency is not demonstrated."
    Source.publicAttribution

xuEtAl2021 : Source.AttributedSource
xuEtAl2021 =
  Source.mkDOISource
    "J. Xu; L. E. Jarocha; T. Zollitsch; and collaborators"
    "Magnetic sensitivity of cryptochrome 4 from a migratory songbird"
    "Nature 594:535-540"
    "2021"
    "10.1038/s41586-021-03618-9"
    "https://doi.org/10.1038/s41586-021-03618-9"
    Source.academicArticleSource
    "Reported CRY4 magnetic sensitivity in vitro from migratory European robin, stronger than chicken and pigeon controls. Molecular photochemical sensitivity does not establish an intact retina-to-brain-to-navigation mechanism."
    Source.publicAttribution

nordmannEtAl2025 : Source.AttributedSource
nordmannEtAl2025 =
  Source.mkDOISource
    "Gregory C. Nordmann; Spencer D. Balay; Thamari N. Kapuruge; Marco Numi; Christoph Leeb; Simon Nimpf; E. Pascal Malkemper; Lukas Landler; David A. Keays"
    "A global screen for magnetically induced neuronal activity in the pigeon brain"
    "Science 391(6790):1155-1160 (2026 issue); online 2025-11-20"
    "2025"
    "10.1126/science.aea6425"
    "https://doi.org/10.1126/science.aea6425"
    Source.academicArticleSource
    "Reported light-independent activation in medial vestibular nuclei and caudal mesopallium, plus type-II vestibular hair cell candidate molecular machinery. Supports an induction pathway model, but does not uniquely prove all mechanisms or human transduction."
    Source.publicAttribution

wangEtAl2019 : Source.AttributedSource
wangEtAl2019 =
  Source.mkDOISource
    "Connie X. Wang; Isaac A. Hilburn; Daw-An Wu; Yuki Mizuhara; Christopher P. Couste; Jacob N. H. Abrahams; Sam E. Bernstein; Ayumu Matani; Shinsuke Shimojo; Joseph L. Kirschvink"
    "Transduction of the geomagnetic field as evidenced from alpha-band activity in the human brain"
    "eNeuro 6(2):ENEURO.0483-18.2019"
    "2019"
    "10.1523/ENEURO.0483-18.2019"
    "https://doi.org/10.1523/ENEURO.0483-18.2019"
    Source.academicArticleSource
    "Reported direction-specific EEG alpha desynchronization under controlled Earth-strength field rotations. Does not demonstrate conscious human magnetic navigation, a particular gene or successful genetic enhancement."
    Source.publicAttribution

lisowski2026 : Source.AttributedSource
lisowski2026 =
  Source.mkDOISource
    "Clivia Lisowski; Michael Quetting; Daniela Klaus; Lisa Lazarevski; Lea Seep; Maximilian Germer; Jian Li; Inge Mueller; Daniel Zuniga; Wolfgang Fiedler; Dina K. N. Dechmann; Kasper Thorup; Jan Hasenauer; Lars Fester; Stefanie Kuerten; Michael Farle; Ulf Wiedwald; Martin Wikelski; Christian Kurts"
    "Homing pigeon navigation relies on superparamagnetic macrophages under overcast conditions"
    "Science 392(6801):985-991"
    "2026"
    "10.1126/science.ady2486"
    "https://doi.org/10.1126/science.ady2486"
    Source.academicArticleSource
    "Reported iron-bearing hepatic macrophages and context-conditional macrophage-depletion homing intervention. Existing Lisowski original-owner science remains separate from cryptochrome and vestibular theories; afferent signaling remains proposed."
    Source.publicAttribution

sourceAtlas : Source.AttributedSourceAtlas
sourceAtlas =
  Source.mkSourceAtlas
    "Thought Emporium magnetoreception stream and independent bird/human papers"
    "The Thought Emporium (outreach); Nimpf, Xu, Nordmann, Wang, Lisowski et al. (original experiments); DASHI (typed evidence crosswalk)"
    (thoughtEmporium2020
    ∷ nimpfEtAl2019
    ∷ xuEtAl2021
    ∷ nordmannEtAl2025
    ∷ wangEtAl2019
    ∷ lisowski2026
    ∷ [])
    "Mechanism-plural, source-scoped observations and hypotheses. The video provides neither a new animal experiment nor proof of human biological enhancement."

------------------------------------------------------------------------
-- VERIFIED REPOSITORY ARTIFACT METADATA, SEPARATE FROM THE 2020 STREAM.
--
-- The Thought Emporium / Justin Atkin's public GitHub repository states
-- CC BY-SA 4.0 attribution and share-alike licensing for its plasmid
-- collection. A magnetoreception .gb artifact was added on 2020-07-04.
-- The 2020-06-17 stream itself says final design was postponed.
-- DO NOT import its sequence or infer correct assembly, viable biology,
-- independent validation, delivery safety, or a human phenotype.
------------------------------------------------------------------------

thoughtEmporiumDigitalArchive : Source.AttributedSource
thoughtEmporiumDigitalArchive =
  Source.mkNoDOISource
    "The Thought Emporium; Justin Atkin (original creator and repository attribution)"
    "Whose-gene-is-it-anyway: magnetoreception digital GenBank artifact"
    "GitHub public archive; artifact commit f83aaf2b3ada085d02d8a25cfdc4ae32c80fe09d; 2020-07-04T03:23:52Z"
    "2020"
    "https://github.com/thethoughtemporium/Whose-gene-is-it-anyway/tree/master/magnetoreception"
    (Source.namedSourceKind "digital genetic-design archive; metadata only")
    "Author-published GenBank file exists after the original 17 June 2020 livestream. Archive presence cannot establish which later session completed it, sequence/assembly correctness, actual synthesis, physiological function, or genetic enhancement."
    Source.publicAttribution

record SourcePublishedDesignReceipt : Set where
  constructor sourcePublishedDesignReceipt
  field
    originalPublisher : Source.AttributedSource
    namedDigitalArtifact : String
    archivedFileSizeBytes : Nat
    sourceCommitSHA : String
    sourceCommitTimestampUTC : String
    sourceRepositoryLicense : String

    originalStreamCompletedOnJune17 : Bool
    originalStreamCompletedOnJune17IsFalse :
      originalStreamCompletedOnJune17 ≡ false

    archivedDesignCorrectnessIndependentlyChecked : Bool
    archivedDesignCorrectnessIndependentlyCheckedIsFalse :
      archivedDesignCorrectnessIndependentlyChecked ≡ false

    physicalAssemblyOrExpressionVerifiedHere : Bool
    physicalAssemblyOrExpressionVerifiedHereIsFalse :
      physicalAssemblyOrExpressionVerifiedHere ≡ false

    magnetoreceptionInEditedOrganismProven : Bool
    magnetoreceptionInEditedOrganismProvenIsFalse :
      magnetoreceptionInEditedOrganismProven ≡ false

sourcePublishedMagnetoreceptionDesign : SourcePublishedDesignReceipt
sourcePublishedMagnetoreceptionDesign =
  sourcePublishedDesignReceipt
    thoughtEmporiumDigitalArchive
    "magnetoreception/paav syn with pigeonized human cacna1d.gb"
    18278
    "f83aaf2b3ada085d02d8a25cfdc4ae32c80fe09d"
    "2020-07-04T03:23:52Z"
    "CC BY-SA 4.0 (as stated in repository README)"
    false refl
    false refl
    false refl
    false refl

digitalArchiveCitationImportsNoProof :
  Source.citationImportsProof thoughtEmporiumDigitalArchive ≡ false
digitalArchiveCitationImportsNoProof = refl

------------------------------------------------------------------------
-- Existing mechanism-neutral owner: vestibular route is one inhabitant,
-- not a replacement for the already-present retinal / hepatic branches.
-- A finite token model cannot prove real afferent encoding.
------------------------------------------------------------------------

vestibularCandidateSurface : Generic.MagnetoreceptionSurface
vestibularCandidateSurface =
  record
    { MagneticStimulus = Generic.MagnetoToken
    ; ReceptorState = Generic.MagnetoToken
    ; TransductionState = Generic.MagnetoToken
    ; AfferentSignal = Generic.MagnetoToken
    ; NavigationCue = Generic.MagnetoToken
    ; NavigationContext = Generic.MagnetoToken
    ; NavigationPolicy = Generic.MagnetoToken
    ; OrientationOutput = Generic.MagnetoToken
    ; receptorResponse = λ _ _ → Generic.transductionStateToken
    ; afferentEncode = λ _ → Generic.afferentSignalToken
    ; cueFromAfference = λ _ _ → Generic.navigationCueToken
    ; navigationUse = λ _ _ → Generic.orientationOutputToken
    ; channel = Generic.vestibularCandidateChannel
    ; afferentRoute = Generic.vestibularCandidateRoute
    ; receptorEvidence = Generic.correlationalReceipt
    ; afferentEvidence = Generic.correlationalReceipt
    ; navigationEvidence = Generic.structuralHypothesis
    ; boundaries = Generic.canonicalMechanismNeutralBoundaries
    ; surfaceReading =
        "Pigeon vestibular candidate from Nimpf 2019 and Nordmann 2025/2026. The model is symbolic; afferent code, primary receptor and behavior-level causal necessity are not established by this source bundle."
    }

vestibularEvidenceReceipt :
  Generic.MagnetoreceptionEvidenceReceipt vestibularCandidateSurface
vestibularEvidenceReceipt =
  record
    { receptorEvidenceCarried = Generic.correlationalReceipt
    ; receptorEvidenceMatches = refl
    ; afferentEvidenceCarried = Generic.correlationalReceipt
    ; afferentEvidenceMatches = refl
    ; navigationEvidenceCarried = Generic.structuralHypothesis
    ; navigationEvidenceMatches = refl
    ; mechanismExclusive = false
    ; mechanismExclusiveIsFalse = refl
    ; phenomenalContentRecovered = false
    ; phenomenalContentRecoveredIsFalse = refl
    ; receiptReading =
        "Source-reported neuronal activity and candidate molecular machinery do not establish a complete or unique functional pigeon magnetic compass."
    }

------------------------------------------------------------------------
-- Explicit reuse of independently maintained owners.
------------------------------------------------------------------------

record CrossChannelOwners : Set₂ where
  field
    retinalCryptochromeCandidate : Generic.MagnetoreceptionSurface
    retinalOwnerMatches :
      retinalCryptochromeCandidate ≡ CRY.cryptochromeGenericSurface

    hepaticMacrophageCandidate : Generic.MagnetoreceptionSurface
    hepaticOwnerMatches :
      hepaticMacrophageCandidate ≡ Hepatic.hepaticMacrophageGenericSurface

    vestibularInductionCandidate : Generic.MagnetoreceptionSurface
    vestibularOwnerMatches :
      vestibularInductionCandidate ≡ vestibularCandidateSurface

    hepaticOriginalRegistry : Registry.AvianMagnetoreceptionSource
    hepaticOriginalRegistryMatches :
      hepaticOriginalRegistry ≡ Registry.lisowskiEtAl2026

    oldRFMechanismAdapter : RF.AvianRFOverlayMechanismAdapter
    oldRFMechanismAdapterMatches :
      oldRFMechanismAdapter ≡ RF.canonicalAvianRFOverlayMechanismAdapter

    singleCompetingMechanismProven : Bool
    singleCompetingMechanismProvenIsFalse :
      singleCompetingMechanismProven ≡ false

    causalHumanGeneTransferPaid : Bool
    causalHumanGeneTransferPaidIsFalse :
      causalHumanGeneTransferPaid ≡ false

crossChannelOwners : CrossChannelOwners
crossChannelOwners =
  record
    { retinalCryptochromeCandidate = CRY.cryptochromeGenericSurface
    ; retinalOwnerMatches = refl
    ; hepaticMacrophageCandidate = Hepatic.hepaticMacrophageGenericSurface
    ; hepaticOwnerMatches = refl
    ; vestibularInductionCandidate = vestibularCandidateSurface
    ; vestibularOwnerMatches = refl
    ; hepaticOriginalRegistry = Registry.lisowskiEtAl2026
    ; hepaticOriginalRegistryMatches = refl
    ; oldRFMechanismAdapter = RF.canonicalAvianRFOverlayMechanismAdapter
    ; oldRFMechanismAdapterMatches = refl
    ; singleCompetingMechanismProven = false
    ; singleCompetingMechanismProvenIsFalse = refl
    ; causalHumanGeneTransferPaid = false
    ; causalHumanGeneTransferPaidIsFalse = refl
    }

------------------------------------------------------------------------
-- Existing ScientificMechanismEvidenceBidiExact owner. Each scientific
-- reading carries its own evidence class. Neither the 2020 livestream
-- nor the in vitro 2021 study demonstrates the proposed human edit.
------------------------------------------------------------------------

videoProposal : Science.ScientificMechanismReceipt
videoProposal =
  Science.scientific-mechanism-receipt
    "Thought Emporium Whose Gene #11; 2020"
    "One pigeon-associated channel difference might permit magnetic sensing after a hypothetical human genetic change."
    Science.sourceInterpretation
    Science.preliminary
    "The Thought Emporium; livestream 2020-06-17; user-provided transcript"
    "Speculation, no successful modification, no evaluated intervention, and no demonstrated sufficiency. No sequence or delivery recipe is imported."

pigeonInductionStudy : Science.ScientificMechanismReceipt
pigeonInductionStudy =
  Science.scientific-mechanism-receipt
    "Nimpf et al. 2019 pigeon inner ear"
    "The paper reports vestibular neural responses, an electroinduction-compatible physical model and an electroreceptive channel isoform."
    Science.experimentalObservation
    Science.sourceBacked
    "10.1016/j.cub.2019.09.048"
    "These observations support a proposed induction mechanism but not complete receptor-to-behavior or human-edit causal proof."

robinCryptochromeStudy : Science.ScientificMechanismReceipt
robinCryptochromeStudy =
  Science.scientific-mechanism-receipt
    "Xu et al. 2021 migratory European robin"
    "The paper reports molecular magnetic sensitivity of robin CRY4 in vitro."
    Science.experimentalObservation
    Science.sourceBacked
    "10.1038/s41586-021-03618-9"
    "In vitro radical-pair sensitivity is not direct whole-animal compass proof; robin is not a pigeon or human."

pigeonBrainScreen : Science.ScientificMechanismReceipt
pigeonBrainScreen =
  Science.scientific-mechanism-receipt
    "Nordmann et al. 2025 online; 2026 issue"
    "The paper reports light-independent pigeon vestibular and pallial neuronal activation and candidate hair-cell machinery."
    Science.experimentalObservation
    Science.sourceBacked
    "10.1126/science.aea6425"
    "Strengthens a pigeon vestibular/brain circuit model; no unique receptor necessity or human genotype-to-perception transfer."

humanEEGStudy : Science.ScientificMechanismReceipt
humanEEGStudy =
  Science.scientific-mechanism-receipt
    "Wang et al. 2019 human EEG"
    "The paper reports repeatable selective EEG alpha-band responses to controlled geomagnetic rotations."
    Science.experimentalObservation
    Science.sourceBacked
    "10.1523/ENEURO.0483-18.2019"
    "A neural correlate is not an established human conscious compass, channel target, or gene-therapy efficacy receipt."

hepaticContext2026 : Science.ScientificMechanismReceipt
hepaticContext2026 =
  Science.scientific-mechanism-receipt
    "Lisowski et al. 2026 homing pigeons"
    "The paper reports hepatic magnetic macrophages and impaired overcast homing after macrophage depletion with visible-Sun controls."
    Science.experimentalObservation
    Science.sourceBacked
    "10.1126/science.ady2486"
    "Conditional behavior intervention is stronger than a mere model but does not prove the proposed macrophage-afferent neural code."

scientificReadings : List Science.ScientificMechanismReceipt
scientificReadings =
  videoProposal
  ∷ pigeonInductionStudy
  ∷ robinCryptochromeStudy
  ∷ pigeonBrainScreen
  ∷ humanEEGStudy
  ∷ hepaticContext2026
  ∷ []

------------------------------------------------------------------------
-- No-promotional reverse obligations, reusing the shared science owner.
------------------------------------------------------------------------

vestibularCausalWeldObligation : Science.ScientificReverseObligation
vestibularCausalWeldObligation =
  Science.scientific-reverse-obligation
    "Pigeon vestibular transduction mechanism"
    Science.mechanismToObservationWeld
    "Identify a source-matched receptor necessity/sufficiency and afferent code with controlled context"
    "Bounded pigeon vestibular mechanism conclusion only"
    "Does not prove human magnetic sensing from channel sequence similarity"

retinalCausalWeldObligation : Science.ScientificReverseObligation
retinalCausalWeldObligation =
  Science.scientific-reverse-obligation
    "European robin CRY4 in vitro to navigation"
    Science.mechanismToObservationWeld
    "Matched in vivo light/retina-specific causal and navigation evidence"
    "Species- and context-indexed photochemical compass claim"
    "Does not disprove vestibular/hepatic alternatives or establish subjective vision"

humanProposalValidationObligation : Science.ScientificReverseObligation
humanProposalValidationObligation =
  Science.scientific-reverse-obligation
    "Thought Emporium 2020 proposed human gain of function"
    Science.independentReplicationReceipt
    "Independent non-operational published evidence of human genotype, nervous-system function, causal perception and safety"
    "An evidence-scoped claim only if actually demonstrated by independently attributed sources"
    "Neither species similarity nor single-channel expression implies editing safety, tissue specificity, neural decoding or conscious magnetoreception"

citationDoesNotImportTheorem :
  Source.citationImportsProof thoughtEmporium2020 ≡ false
citationDoesNotImportTheorem = refl

atlasDoesNotCreateScience :
  Source.atlasCreatesAuthority sourceAtlas ≡ false
atlasDoesNotCreateScience = refl
