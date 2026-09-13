module DASHI.Empirical.DarkDimensionEmpiricalDiscriminationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Diligence
import DASHI.Core.GenericReceipt as Receipt
import DASHI.Empirical.GRQuantumPredictionProtocol as Prediction
import DASHI.Physics.Closure.DarkDimensionStringPromotionBoundaryExact as DarkDimension

------------------------------------------------------------------------
-- DARK-DIMENSION EMPIRICAL DISCRIMINATION
--
-- This owner admits published Dark-Dimension phenomenology into an empirical
-- comparison lane without relabelling a fit to already-observed cosmological
-- data as a preregistered held-out prediction.  It also retains a concrete
-- 2026 alternative mechanism capable of producing a similar apparent
-- evolving-dark-energy signal.
--
-- Therefore:
--
--   published fit != held-out prediction
--   preference over one baseline != unique model identity
--   phenomenological agreement != ultraviolet/string-theory identification
------------------------------------------------------------------------

false≢true : false ≡ true → ⊥
false≢true ()

record DecimalRatio : Set where
  constructor decimalRatio
  field
    numerator : Nat
    denominator : Nat

open DecimalRatio public

cPrimeBestFitFiveHundredths : DecimalRatio
cPrimeBestFitFiveHundredths = decimalRatio 5 100

cPrimeUncertaintyOneHundredth : DecimalRatio
cPrimeUncertaintyOneHundredth = decimalRatio 1 100

cPrimeFifthForceUpperBoundTwoTenths : DecimalRatio
cPrimeFifthForceUpperBoundTwoTenths = decimalRatio 2 10

------------------------------------------------------------------------
-- Source attribution and diligence.
------------------------------------------------------------------------

darkAcousticOscillationSource : Source.AttributedSource
darkAcousticOscillationSource =
  Source.mkDOISource
    "Mathias Garny; Florian Niedermann; Martin S. Sloth"
    "Dark acoustic oscillations as an early-Universe explanation of the DESI anomaly"
    "Physical Review D 114, 043523"
    "2026"
    "10.1103/y31p-9g5k"
    "https://doi.org/10.1103/y31p-9g5k"
    Source.academicArticleSource
    "competing phenomenological explanation showing that a percent-level dark-acoustic-oscillation feature can produce an apparent DESI distance shift and fit improvement similar to evolving dark energy; retained as a comparator, not as a refutation of the Dark Dimension"
    Source.publicAttribution

bedroyaFitDiligence : Diligence.SourceDiligence
bedroyaFitDiligence =
  Diligence.source-diligence
    "Bedroya-Obied-Vafa-Wu 2026 evolving-dark-sector fit"
    DarkDimension.bedroyaObiedVafaWu2026
    Diligence.primaryProposition
    true
    refl
    "APS accepted-paper abstract and arXiv same-title primary manuscript inspected"
    Diligence.primaryLocated
    "accepted-paper abstract: DESI DR2 + DES/Union3/Pantheon+ fit; c' approximately 0.05 +/- 0.01; c' less than approximately 0.2 fifth-force bound"
    "Phys. Rev. D accepted 3 August 2026; DOI 10.1103/1rsq-cv2m"
    "same evolving-dark-sector / Dark-Dimension model object"
    "DESI DR2 and supernova data available before publication; result is a retrospective fit, not a future holdout"
    "bounded to the model and datasets described by the paper"
    "explicit comparator search retained; see Garny-Niedermann-Sloth 2026 dark-acoustic-oscillation explanation"
    "reported agreement and parameter preference do not uniquely identify the mechanism or its ultraviolet origin"
    "admitted as external model-specific empirical evidence; does not become DASHI-derived GR/QG empirical completion"

darkAcousticOscillationDiligence : Diligence.SourceDiligence
darkAcousticOscillationDiligence =
  Diligence.source-diligence
    "Garny-Niedermann-Sloth 2026 DESI dark-acoustic-oscillation comparator"
    darkAcousticOscillationSource
    Diligence.contestingEvidence
    true
    refl
    "APS published article/abstract inspected"
    Diligence.primaryLocated
    "abstract: percent-level DAO near BAO can bias extracted BAO scale and yield fit improvement similar to evolving dark energy"
    "Phys. Rev. D 114, 043523; published 14 August 2026; DOI 10.1103/y31p-9g5k"
    "same DESI-anomaly phenomenological target, different physical mechanism"
    "DESI DR2-era cosmological interpretation"
    "comparator only; does not claim exhaustive alternative-model coverage"
    "other evolving-dark-energy and modified-dark-sector explanations may also remain live"
    "similar fit improvement is not same-model identity and does not prove the DAO mechanism"
    "used to block uniqueness promotion from phenomenological agreement alone"

------------------------------------------------------------------------
-- Published-fit carrier.
------------------------------------------------------------------------

record PublishedModelFit : Set where
  constructor publishedModelFit
  field
    fitLabel : String
    source : Source.AttributedSource
    diligence : Diligence.SourceDiligence
    bestFitCPrime : DecimalRatio
    uncertaintyCPrime : DecimalRatio
    externalUpperBoundCPrime : DecimalRatio
    observedDatasetReused : Bool
    preregisteredBeforeDataset : Bool
    heldOutPrediction : Bool
    competingMechanismLocated : Bool
    uniqueModelIdentityEstablished : Bool
    ultravioletOriginEstablished : Bool

open PublishedModelFit public

bedroyaReportedFit : PublishedModelFit
bedroyaReportedFit =
  publishedModelFit
    "Dark-Dimension evolving-dark-sector DESI DR2 + supernova fit"
    DarkDimension.bedroyaObiedVafaWu2026
    bedroyaFitDiligence
    cPrimeBestFitFiveHundredths
    cPrimeUncertaintyOneHundredth
    cPrimeFifthForceUpperBoundTwoTenths
    true
    false
    false
    true
    false
    false

darkAcousticOscillationComparator : Source.AttributedSource
darkAcousticOscillationComparator = darkAcousticOscillationSource

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

record HeldOutPredictionWitness (fit : PublishedModelFit) : Set where
  constructor heldOutPredictionWitness
  field
    heldOutPaid : heldOutPrediction fit ≡ true

open HeldOutPredictionWitness public

record UniqueModelIdentityWitness (fit : PublishedModelFit) : Set where
  constructor uniqueModelIdentityWitness
  field
    uniqueIdentityPaid : uniqueModelIdentityEstablished fit ≡ true

open UniqueModelIdentityWitness public

record UniqueUltravioletOriginWitness (fit : PublishedModelFit) : Set where
  constructor uniqueUltravioletOriginWitness
  field
    ultravioletIdentityPaid : ultravioletOriginEstablished fit ≡ true

open UniqueUltravioletOriginWitness public

reportedFitDoesNotEqualHeldOutPrediction :
  HeldOutPredictionWitness bedroyaReportedFit → ⊥
reportedFitDoesNotEqualHeldOutPrediction witness =
  false≢true (heldOutPaid witness)

reportedPreferenceDoesNotUniquelyIdentifyDarkDimension :
  UniqueModelIdentityWitness bedroyaReportedFit → ⊥
reportedPreferenceDoesNotUniquelyIdentifyDarkDimension witness =
  false≢true (uniqueIdentityPaid witness)

alternativeMechanismKeepsModelIdentityOpen :
  UniqueUltravioletOriginWitness bedroyaReportedFit → ⊥
alternativeMechanismKeepsModelIdentityOpen witness =
  false≢true (ultravioletIdentityPaid witness)

------------------------------------------------------------------------
-- Direct weld to the existing GR/quantum quantitative-prediction boundary.
-- The externally published model fit is admitted as evidence, but does not
-- mutate the repository's statement that no DASHI-derived quantitative GR/QG
-- prediction has yet been produced under its own locked protocol.
------------------------------------------------------------------------

externalPublishedFitDoesNotPayDASHIDerivedPrediction :
  Prediction.PredictionBoundary.quantitativePredictionDerived
    Prediction.canonicalPredictionBoundary
  ≡ false
externalPublishedFitDoesNotPayDASHIDerivedPrediction =
  Prediction.PredictionBoundary.quantitativePredictionDerivedIsFalse
    Prediction.canonicalPredictionBoundary

------------------------------------------------------------------------
-- Admission is deliberately non-promoting.  It records that the literature
-- supplies a real empirical comparison lane while preserving the separate
-- requirements for locked prediction, holdout, model discrimination,
-- replication, and GR/QG authority.
------------------------------------------------------------------------

darkDimensionPredictionAdmission : Receipt.GenericReceipt
darkDimensionPredictionAdmission =
  Receipt.mkNonPromotingReceipt
    "Dark-Dimension external empirical discrimination admission"
    "DASHI.Empirical.DarkDimensionEmpiricalDiscriminationExact"
    "Bedroya-Obied-Vafa-Wu 2026 fit + Garny-Niedermann-Sloth 2026 comparator"
    "admits source-bound published fit values and a concrete alternative phenomenological mechanism into the GR/quantum empirical investigation"
    "retrospective dataset fit is not a preregistered held-out prediction; model preference is not unique mechanism identity; neither source pays string-theory or DASHI unification promotion"
    "static source/diligence/discrimination contract plus future Agda typecheck"

darkDimensionPredictionAdmissionStillNonPromoting :
  Receipt.promotesClaim darkDimensionPredictionAdmission ≡ false
darkDimensionPredictionAdmissionStillNonPromoting =
  Receipt.promotesClaimIsFalse darkDimensionPredictionAdmission
