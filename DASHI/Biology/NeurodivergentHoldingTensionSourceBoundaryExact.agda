module DASHI.Biology.NeurodivergentHoldingTensionSourceBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NEURODIVERGENT RELATIONAL-PROCESSING / "HOLDING TENSION" SOURCE LEDGER
--
-- This module is deliberately source-bounded.  It does not duplicate the
-- #618 processing-geometry implementation on this separate draft ancestry.
-- Instead it records peer-reviewed evidence that can later be consumed by a
-- thin bridge after branch ancestry is reconciled.
--
-- Crucially:
--   structural representational burden != measured metabolic energy;
--   precision-weighting hypotheses are contested, not universal laws;
--   hyperfocus/monotropism measures show method-dependent convergence;
--   information-transfer effects do not validate a DASHI-specific mechanism.
------------------------------------------------------------------------

data EvidenceRole : Set where
  dynamicMultiscaleMathematicalFramework
  activeInferencePrecisionUpdating
  precisionWeightingNullCorrective
  transdiagnosticHyperfocusContextualEffects
  hyperfocusMeasurementNonConvergence
  stickySpringyAttentionOperationalisation
  crossNeurotypeInformationTransfer
  precisionReviewContext
  : EvidenceRole

record SourceReference : Set where
  constructor sourceReference
  field
    authors : String
    title : String
    venue : String
    year : Nat
    doi : String
    role : EvidenceRole
    boundedReading : String

open SourceReference public

adamouEtAl2026 : SourceReference
adamouEtAl2026 =
  sourceReference
    "Marios Adamou; Athanasios Kehagias; Grigoris Antoniou"
    "A multi-scale mathematical framework for modelling the dynamic nature of autism spectrum disorder symptoms: integrating predictive coding, information theory, and network principles"
    "Frontiers in Psychiatry 17:1787120"
    2026
    "10.3389/fpsyt.2026.1787120"
    dynamicMultiscaleMathematicalFramework
    "Theoretical multi-scale mathematical models of context-dependent autism-related symptom dynamics. The paper explicitly states that its equations and parameter values require empirical validation; it does not establish a measured neural-energy law."

arthurEtAl2023 : SourceReference
arthurEtAl2023 =
  sourceReference
    "Tom Arthur; Sam Vine; Gavin Buckingham; Mark Brosnan; Mark Wilson; David Harris"
    "Testing predictive coding theories of autism spectrum disorder using models of active inference"
    "PLOS Computational Biology 19(9):e1011473"
    2023
    "10.1371/journal.pcbi.1011473"
    activeInferencePrecisionUpdating
    "Computational modelling found task-dependent differences in priors, belief updating and precision weighting, with difficulty flexibly adapting learning rates to volatility; it did not support generic prediction deficits or persistently high prediction-error precision."

wardBuitelaarHunnius2024 : SourceReference
wardBuitelaarHunnius2024 =
  sourceReference
    "Emma K. Ward; Jan K. Buitelaar; Sabine Hunnius"
    "Autistic and nonautistic adolescents do not differ in adaptation to gaze direction"
    "Autism Research 17"
    2024
    "10.1002/aur.3118"
    precisionWeightingNullCorrective
    "Bayesian behavioural evidence strongly supported absence of the predicted group difference in gaze adaptation; this challenges any universal autism-wide precision-weighting claim."

dwyerWilliamsLawsonRivera2024 : SourceReference
dwyerWilliamsLawsonRivera2024 =
  sourceReference
    "Patrick Dwyer; Zachary J. Williams; Wenn B. Lawson; Susan M. Rivera"
    "A trans-diagnostic investigation of attention, hyper-focus, and monotropism in autism, attention dysregulation hyperactivity development, and the general population"
    "Neurodiversity 2"
    2024
    "10.1177/27546330241237883"
    transdiagnosticHyperfocusContextualEffects
    "Questionnaire study found hyperfocus and inattention elevated and correlated across neurodivergent groups, with both positive and negative quality-of-life associations; deep/persistent attention is therefore not represented as uniformly beneficial or uniformly costly."

dwyerSillasSaronRivera2025 : SourceReference
dwyerSillasSaronRivera2025 =
  sourceReference
    "Patrick Dwyer; Andre Sillas; Clifford D. Saron; Susan M. Rivera"
    "Investigating autistic hyperfocus and monotropism: Limited convergence of event-related potentials, laboratory tasks, and questionnaire responses"
    "Research in Autism 127:202683"
    2025
    "10.1016/j.reia.2025.202683"
    hyperfocusMeasurementNonConvergence
    "Reports elevated questionnaire hyperfocus alongside limited convergence with ERP/laboratory measures; blocks promotion of self-report or one behavioural coordinate into a universal neural mechanism."

dwyerEtAl2024StickySpringy : SourceReference
dwyerEtAl2024StickySpringy =
  sourceReference
    "Patrick Dwyer; Andre Sillas; Melanie Prieto; Emily Camp; Christine Wu Nordahl; Susan M. Rivera"
    "Hyper-focus, sticky attention, and springy attention in young autistic children: Associations with sensory behaviors and cognitive ability"
    "Autism Research 17(8):1677-1695"
    2024
    "10.1002/aur.3174"
    stickySpringyAttentionOperationalisation
    "Eye-tracking study operationalises sticky and springy attention and reports distinct correlates; it found no evidence of a global autistic increase in sticky attention and treats springy-attention findings as requiring further targeted study."

cromptonEtAl2025 : SourceReference
cromptonEtAl2025 =
  sourceReference
    "Catherine J. Crompton et al."
    "Information transfer within and between autistic and non-autistic people"
    "Nature Human Behaviour 9:1488-1500"
    2025
    "10.1038/s41562-025-02163-z"
    crossNeurotypeInformationTransfer
    "Provides an empirical information-transfer paradigm across autistic, non-autistic and mixed chains; motivates measurable relational communication variables without proving a DASHI trusted-friend or double-empathy mechanism identity."

laoRodriguezEtAl2026 : SourceReference
laoRodriguezEtAl2026 =
  sourceReference
    "A. B. Lao-Rodriguez; S. Cacciato-Salcedo; M. S. Malmierca"
    "The predictive processing embodied in brain conditions: the role of precision"
    "Frontiers in Psychology 17:1887747"
    2026
    "10.3389/fpsyg.2026.1887747"
    precisionReviewContext
    "Review-level context for precision weighting and context-sensitive updating across brain conditions; it summarizes autism predictive-processing work but is not itself evidence for a universal autistic precision phenotype."

holdingTensionSources : List SourceReference
holdingTensionSources =
  adamouEtAl2026
  ∷ arthurEtAl2023
  ∷ wardBuitelaarHunnius2024
  ∷ dwyerWilliamsLawsonRivera2024
  ∷ dwyerSillasSaronRivera2025
  ∷ dwyerEtAl2024StickySpringy
  ∷ cromptonEtAl2025
  ∷ laoRodriguezEtAl2026
  ∷ []

------------------------------------------------------------------------
-- Exact no-promotion boundary.
------------------------------------------------------------------------

record NeurodivergentHoldingTensionBoundary : Set where
  constructor neurodivergentHoldingTensionBoundary
  field
    literatureSupportsMultiaxialDynamicModelling : Bool
    literatureSupportsMultiaxialDynamicModellingIsTrue :
      literatureSupportsMultiaxialDynamicModelling ≡ true

    oneUniversalAutisticPrecisionWeightingLawEstablished : Bool
    oneUniversalAutisticPrecisionWeightingLawEstablishedIsFalse :
      oneUniversalAutisticPrecisionWeightingLawEstablished ≡ false

    hyperfocusIsOneUniversalNeuralMarker : Bool
    hyperfocusIsOneUniversalNeuralMarkerIsFalse :
      hyperfocusIsOneUniversalNeuralMarker ≡ false

    hyperfocusIsUniformlyCostly : Bool
    hyperfocusIsUniformlyCostlyIsFalse :
      hyperfocusIsUniformlyCostly ≡ false

    structuralRepresentationBurdenIsMeasuredMetabolicEnergy : Bool
    structuralRepresentationBurdenIsMeasuredMetabolicEnergyIsFalse :
      structuralRepresentationBurdenIsMeasuredMetabolicEnergy ≡ false

    citedLiteratureValidatesDASHIHoldingTensionMechanism : Bool
    citedLiteratureValidatesDASHIHoldingTensionMechanismIsFalse :
      citedLiteratureValidatesDASHIHoldingTensionMechanism ≡ false

    crossNeurotypeInformationTransferIsMeasurable : Bool
    crossNeurotypeInformationTransferIsMeasurableIsTrue :
      crossNeurotypeInformationTransferIsMeasurable ≡ true

canonicalNeurodivergentHoldingTensionBoundary :
  NeurodivergentHoldingTensionBoundary
canonicalNeurodivergentHoldingTensionBoundary =
  neurodivergentHoldingTensionBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
