module DASHI.Environment.GlyphosateSauerkrautBioremediationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Environment.SoilBiogeochemistryProcessNetworkExact as Soil

------------------------------------------------------------------------
-- GLYPHOSATE / RAW-SAUERKRAUT-JUICE SOIL REMEDIATION
-- BIDI experimental-design and residual-bound owner.
--
-- Primary empirical source:
--   Dieter Harle, Michael J. McNeill, Don M. Huber, Michael Maney,
--   Raul J. Cano, Martha Carlin (2024), "Saga of Soggy Sauerkraut",
--   HortScience 59(11), 1618--1628.
--   DOI: 10.21273/HORTSCI18041-24
--
-- Source boundary:
--   The source reports field observations/trials in which raw sauerkraut juice
--   (RSKJ) and other biological treatments were followed by large reductions in
--   measured soil glyphosate/AMPA over roughly six months.  This module records
--   those treatment/observation relations while refusing to identify measured
--   residue loss with one specific microbial mechanism unless an independent
--   mechanism receipt is supplied.
--
-- DASHI extension:
--   Where experimental design does not identify a causal component exactly, a
--   backward BIDI pass may return a typed approximation/error envelope assembled
--   from known quantities and explicit unresolved residual components.  Such an
--   envelope constrains what remains possible; it is not promoted to an exact
--   causal decomposition.
------------------------------------------------------------------------

sourceDOI : String
sourceDOI = "10.21273/HORTSCI18041-24"

------------------------------------------------------------------------
-- Intervention and analyte vocabulary.
------------------------------------------------------------------------

data TreatmentKind : Set where
  untreatedWaterControl
  rawSauerkrautJuice
  PB027InWater
  PB027PlusRawSauerkrautJuice
  catawaterPlusRawSauerkrautJuice
  catawaterInWater
  : TreatmentKind

data ResidueAnalyte : Set where
  glyphosateAnalyte
  ampaAnalyte
  totalEffectiveGlyphosateAnalyte
  : ResidueAnalyte

data SoilSite : Set where
  shioctonSiltLoam
  kidderSandyLoam
  : SoilSite

data DesignKind : Set where
  longitudinalStripComparison
  randomizedCompleteBlock
  : DesignKind

shioctonAndKidderDistinct : shioctonSiltLoam ≡ kidderSandyLoam → ⊥
shioctonAndKidderDistinct ()

stripAndRCBDDistinct : longitudinalStripComparison ≡ randomizedCompleteBlock → ⊥
stripAndRCBDDistinct ()

------------------------------------------------------------------------
-- Quantities are kept as scaled naturals with the scale named explicitly.
-- This prevents an untyped number from silently changing unit or precision.
------------------------------------------------------------------------

record ScaledMeasurement : Set where
  constructor scaledMeasurement
  field
    magnitude : Nat
    scaleLabel : String
    unitLabel : String
    assayOrDerivationReference : String

open ScaledMeasurement public

record TreatmentDose : Set where
  constructor treatmentDose
  field
    treatment : TreatmentKind
    magnitude : Nat
    scaleLabel : String
    unitLabel : String
    applicationAreaReference : String
    applicationTimingReference : String
    compositionReference : String

open TreatmentDose public

-- 140.25 L/ha represented at 0.01 L/ha scale.
reportedRSKJDose : TreatmentDose
reportedRSKJDose = treatmentDose
  rawSauerkrautJuice
  14025
  "0.01"
  "L/ha"
  "field application area as reported by Harle et al. 2024"
  "source-specific field application timing"
  "raw sauerkraut juice; composition is multicomponent and not reduced to Lactiplantibacillus alone"

------------------------------------------------------------------------
-- Chemistry identities.  These are analyte/model carriers, not a claim that
-- one disappearance pathway has been established.
------------------------------------------------------------------------

glyphosateSpecies : Chemistry.Species
glyphosateSpecies = record
  { Chemistry.speciesId = "glyphosate"
  ; Chemistry.phase = Chemistry.dissolved
  ; Chemistry.chargeLabel = "pH-dependent ionic state; application model required"
  ; Chemistry.compositionLabel = "N-(phosphonomethyl)glycine"
  ; Chemistry.mobilityClass = Chemistry.restricted
  ; Chemistry.activityModelLabel = "soil solution/sorption speciation model required"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

ampaSpecies : Chemistry.Species
ampaSpecies = record
  { Chemistry.speciesId = "AMPA"
  ; Chemistry.phase = Chemistry.dissolved
  ; Chemistry.chargeLabel = "pH-dependent ionic state; application model required"
  ; Chemistry.compositionLabel = "aminomethylphosphonic acid"
  ; Chemistry.mobilityClass = Chemistry.restricted
  ; Chemistry.activityModelLabel = "soil solution/sorption speciation model required"
  ; Chemistry.opticalRoleLabel = "not asserted"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

------------------------------------------------------------------------
-- Distinguish chemical state from analytical observability.
------------------------------------------------------------------------

data GlyphosateStateKind : Set where
  dissolvedGlyphosate
  adsorbedGlyphosate
  bioavailableGlyphosate
  microbialSubstrateGlyphosate
  extractableMeasuredGlyphosate
  : GlyphosateStateKind

dissolvedNotMeasured : dissolvedGlyphosate ≡ extractableMeasuredGlyphosate → ⊥
dissolvedNotMeasured ()

adsorbedNotMeasured : adsorbedGlyphosate ≡ extractableMeasuredGlyphosate → ⊥
adsorbedNotMeasured ()

bioavailableNotMeasured : bioavailableGlyphosate ≡ extractableMeasuredGlyphosate → ⊥
bioavailableNotMeasured ()

------------------------------------------------------------------------
-- Candidate mechanisms remain disjoint alternatives unless independently
-- welded.  In particular, an RSKJ-associated residue decline does not select
-- Lactiplantibacillus causation by constructor choice.
------------------------------------------------------------------------

data CandidateMechanism : Set where
  introducedLacticAcidBacterialDegradation
  stimulatedIndigenousMicrobialDegradation
  acidityDrivenSpeciationOrAvailabilityShift
  organicCarbonNutrientStimulation
  sorptionDesorptionRedistribution
  ionicStrengthPerturbation
  combinedMechanism
  unresolvedMechanism
  : CandidateMechanism

introducedLABNotIndigenous :
  introducedLacticAcidBacterialDegradation ≡ stimulatedIndigenousMicrobialDegradation → ⊥
introducedLABNotIndigenous ()

introducedLABNotSorption :
  introducedLacticAcidBacterialDegradation ≡ sorptionDesorptionRedistribution → ⊥
introducedLABNotSorption ()

------------------------------------------------------------------------
-- Experimental observations and design receipts.
------------------------------------------------------------------------

record ResidueObservation : Set where
  constructor residueObservation
  field
    site : SoilSite
    analyte : ResidueAnalyte
    measuredValue : ScaledMeasurement
    samplingTimeReference : String
    soilDepthReference : String
    samplingCompositeReference : String
    assayReference : String

open ResidueObservation public

record ExperimentDesignReceipt : Set where
  constructor experimentDesignReceipt
  field
    design : DesignKind
    site : SoilSite
    treatmentArms : List TreatmentKind
    nominalReplicates : Nat
    residueReplicatesActuallyAnalysed : Nat
    allocationReference : String
    contemporaneousControlAtResidueEndpoint : Bool
    repeatedMeasureOrPairingReference : String
    newGlyphosateInputDuringWindowReference : String
    weatherMoistureControlReference : String
    assayReference : String
    designLimitReference : String

open ExperimentDesignReceipt public

shioctonDesign : ExperimentDesignReceipt
shioctonDesign = experimentDesignReceipt
  longitudinalStripComparison
  shioctonSiltLoam
  (untreatedWaterControl ∷ rawSauerkrautJuice ∷ [])
  6
  4
  "alternating treated/non-treated field strips reported by source"
  false
  "published headline residue comparison is across different sampling dates; pairing does not recover a same-time counterfactual"
  "record explicitly if any glyphosate entered the system between samples"
  "weather/moisture remain potential time-varying contributors unless independently controlled"
  "LC-MS/MS residue analysis reported by source"
  "large longitudinal residue decline is observed, but the headline percent decline is not definitionally an RSKJ-only causal effect"

kidderDesign : ExperimentDesignReceipt
kidderDesign = experimentDesignReceipt
  randomizedCompleteBlock
  kidderSandyLoam
  ( untreatedWaterControl
  ∷ rawSauerkrautJuice
  ∷ PB027InWater
  ∷ PB027PlusRawSauerkrautJuice
  ∷ catawaterPlusRawSauerkrautJuice
  ∷ catawaterInWater
  ∷ [])
  4
  4
  "one-factor randomized complete block design reported by source"
  true
  "block structure supplies contemporaneous treatment comparison; repeated-residue trajectory remains source-specific"
  "corn herbicide management during trial must remain in the material-input ledger"
  "irrigated field conditions reported; exact environmental equivalence is not assumed"
  "soil glyphosate/AMPA residue analysis reported by source"
  "randomization strengthens treatment contrast but does not identify which microbial/chemical submechanism caused residue loss"

shioctonEvidenceNotKidderEvidence : shioctonDesign ≡ kidderDesign → ⊥
shioctonEvidenceNotKidderEvidence ()

------------------------------------------------------------------------
-- Published Shiocton residue specimen.
-- Values are hundredths of ng/g, preserving the reported decimal values:
-- glyphosate 38.37 -> 6.57; AMPA 112.59 -> 13.35; TEG 207.26 -> 26.59.
------------------------------------------------------------------------

shioctonGlyphosateBefore : ScaledMeasurement
shioctonGlyphosateBefore = scaledMeasurement 3837 "0.01" "ng/g" "Harle et al. 2024 Table 10"

shioctonGlyphosateAfter : ScaledMeasurement
shioctonGlyphosateAfter = scaledMeasurement 657 "0.01" "ng/g" "Harle et al. 2024 Table 10"

shioctonAMPABefore : ScaledMeasurement
shioctonAMPABefore = scaledMeasurement 11259 "0.01" "ng/g" "Harle et al. 2024 Table 10"

shioctonAMPAAfter : ScaledMeasurement
shioctonAMPAAfter = scaledMeasurement 1335 "0.01" "ng/g" "Harle et al. 2024 Table 10"

shioctonTEGBefore : ScaledMeasurement
shioctonTEGBefore = scaledMeasurement 20726 "0.01" "ng/g" "Harle et al. 2024 Table 10"

shioctonTEGAfter : ScaledMeasurement
shioctonTEGAfter = scaledMeasurement 2659 "0.01" "ng/g" "Harle et al. 2024 Table 10"

------------------------------------------------------------------------
-- BIDI residual/backpropagation layer.
--
-- A missing control or nonidentified mechanism is represented by a residual
-- component with provenance and an explicit bound status.  Known quantities can
-- shrink an admissible interval, but unresolved components remain visible.
------------------------------------------------------------------------

data BoundStatus : Set where
  exactFromMeasurement
  intervalFromKnownQuantities
  oneSidedBound
  unresolvedBound
  : BoundStatus

data ResidualKind : Set where
  treatmentAssociatedComponent
  elapsedTimeNaturalDecay
  indigenousMicrobiomeComponent
  weatherMoistureComponent
  samplingAssayComponent
  newGlyphosateInputComponent
  sorptionAvailabilityComponent
  unmodelledResidualComponent
  : ResidualKind

record ApproximationEnvelope : Set where
  constructor approximationEnvelope
  field
    targetLabel : String
    lower : ScaledMeasurement
    upper : ScaledMeasurement
    status : BoundStatus
    knownQuantityReferences : List String
    unresolvedComponents : List ResidualKind
    derivationReference : String
    validationRequired : Bool

open ApproximationEnvelope public

record BidiResidualBackpropagation : Set where
  constructor bidiResidualBackpropagation
  field
    designReceipt : ExperimentDesignReceipt
    forwardObservationReference : String
    backwardTargetReference : String
    admissibleEnvelope : ApproximationEnvelope
    causalMechanism : CandidateMechanism
    mechanismIdentifiedExactly : Bool
    exactIdentificationReceipt : String
    residualClosureReference : String

open BidiResidualBackpropagation public

------------------------------------------------------------------------
-- Fail-closed constructors.
------------------------------------------------------------------------

shioctonHeadlineBackpropagation : BidiResidualBackpropagation
shioctonHeadlineBackpropagation = bidiResidualBackpropagation
  shioctonDesign
  "observed TEG decline from 207.26 to 26.59 ng/g across reported sampling dates"
  "incremental RSKJ-attributable contribution to observed residue decline"
  (approximationEnvelope
    "RSKJ-attributable component, bounded only after accounting for time/control/input residuals"
    (scaledMeasurement 0 "0.01" "ng/g-equivalent contribution" "conservative nonnegative lower bound; no exact treatment attribution claimed")
    (scaledMeasurement 18067 "0.01" "ng/g-equivalent contribution" "raw observed TEG difference gives only a loose upper envelope before residual subtraction")
    oneSidedBound
    ( "TEG before 207.26 ng/g"
    ∷ "TEG after 26.59 ng/g"
    ∷ "RSKJ nominal dose 140.25 L/ha"
    ∷ "elapsed sampling interval"
    ∷ [])
    ( elapsedTimeNaturalDecay
    ∷ indigenousMicrobiomeComponent
    ∷ weatherMoistureComponent
    ∷ samplingAssayComponent
    ∷ newGlyphosateInputComponent
    ∷ sorptionAvailabilityComponent
    ∷ [])
    "backpropagate the observed decline as a ceiling on treatment-attributable loss; subtract or tighten only with independently warranted component bounds"
    true)
  unresolvedMechanism
  false
  "no exact mechanism receipt in the published headline contrast"
  "all unresolved residual components must remain explicit until bounded or measured"

------------------------------------------------------------------------
-- Generic non-promotion theorems.
------------------------------------------------------------------------

data ExactMechanismIdentification : Set where
  introducedLABExactlyIdentified
  indigenousExactlyIdentified
  acidityExactlyIdentified
  sorptionExactlyIdentified
  combinedExactlyIdentified
  : ExactMechanismIdentification

data ApproximateConstraint : Set where
  boundedButNotIdentified : ApproximateConstraint

approximationIsNotExactIdentification :
  ApproximateConstraint → ExactMechanismIdentification → Set
approximationIsNotExactIdentification boundedButNotIdentified introducedLABExactlyIdentified = ⊥
approximationIsNotExactIdentification boundedButNotIdentified indigenousExactlyIdentified = ⊥
approximationIsNotExactIdentification boundedButNotIdentified acidityExactlyIdentified = ⊥
approximationIsNotExactIdentification boundedButNotIdentified sorptionExactlyIdentified = ⊥
approximationIsNotExactIdentification boundedButNotIdentified combinedExactlyIdentified = ⊥

noExactMechanismFromApproximation :
  (m : ExactMechanismIdentification) →
  approximationIsNotExactIdentification boundedButNotIdentified m
noExactMechanismFromApproximation introducedLABExactlyIdentified = λ ()
noExactMechanismFromApproximation indigenousExactlyIdentified = λ ()
noExactMechanismFromApproximation acidityExactlyIdentified = λ ()
noExactMechanismFromApproximation sorptionExactlyIdentified = λ ()
noExactMechanismFromApproximation combinedExactlyIdentified = λ ()

------------------------------------------------------------------------
-- Positive interpretation: an observed treatment-associated decline can be
-- retained as evidence without overclaiming the submechanism.
------------------------------------------------------------------------

record TreatmentAssociatedResidueEvidence : Set where
  constructor treatmentAssociatedResidueEvidence
  field
    experiment : ExperimentDesignReceipt
    treatment : TreatmentKind
    beforeReference : String
    afterReference : String
    measuredDeclineReference : String
    causalAttributionLimitReference : String

open TreatmentAssociatedResidueEvidence public

shioctonTreatmentAssociatedEvidence : TreatmentAssociatedResidueEvidence
shioctonTreatmentAssociatedEvidence = treatmentAssociatedResidueEvidence
  shioctonDesign
  rawSauerkrautJuice
  "Harle et al. 2024 Table 10 pre-treatment/baseline residue report"
  "Harle et al. 2024 Table 10 later residue report"
  "large decline in measured glyphosate, AMPA, and TEG reported"
  "treatment association retained; exact RSKJ-only causal fraction and microbial submechanism remain unpromoted"

------------------------------------------------------------------------
-- Cross-weld to the existing soil-biogeochemistry architecture.
------------------------------------------------------------------------

record GlyphosateSoilBiogeochemistryWeld
    (soil : Soil.SoilCNProcessNetwork) : Set₁ where
  constructor glyphosateSoilBiogeochemistryWeld
  field
    glyphosateChemistry : Chemistry.ReactionNetwork
    soilNetwork : Soil.SoilCNProcessNetwork
    soilNetworkIsProvidedNetwork : soilNetwork ≡ soil

    glyphosateStateIdentificationReference : String
    microbialBiomassCouplingReference : String
    moistureTemperatureCouplingReference : String
    sorptionInterfaceReference : String
    glyphosateToAMPAPathwayReference : String
    furtherTransformationOrMineralisationReference : String
    assayObservationMapReference : String
    experimentDesign : ExperimentDesignReceipt
    identifiabilityReference : String
    heldOutValidationReference : String

open GlyphosateSoilBiogeochemistryWeld public

------------------------------------------------------------------------
-- Explicit authority boundary.
------------------------------------------------------------------------

record GlyphosateSauerkrautBoundary : Set where
  constructor glyphosateSauerkrautBoundary
  field
    residueDisappearanceEqualsCompleteMineralisation : Bool
    residueDisappearanceEqualsCompleteMineralisationIsFalse :
      residueDisappearanceEqualsCompleteMineralisation ≡ false

    RSKJDeclineProvesLABMechanism : Bool
    RSKJDeclineProvesLABMechanismIsFalse :
      RSKJDeclineProvesLABMechanism ≡ false

    headlinePercentDeclineEqualsTreatmentCausalFraction : Bool
    headlinePercentDeclineEqualsTreatmentCausalFractionIsFalse :
      headlinePercentDeclineEqualsTreatmentCausalFraction ≡ false

    randomizedBlockDesignIdentifiesSubmechanismAutomatically : Bool
    randomizedBlockDesignIdentifiesSubmechanismAutomaticallyIsFalse :
      randomizedBlockDesignIdentifiesSubmechanismAutomatically ≡ false

    knownQuantitiesMayConstrainMissingComponent : Bool
    knownQuantitiesMayConstrainMissingComponentIsTrue :
      knownQuantitiesMayConstrainMissingComponent ≡ true

    approximateBoundIsExactRecoveredMechanism : Bool
    approximateBoundIsExactRecoveredMechanismIsFalse :
      approximateBoundIsExactRecoveredMechanism ≡ false

    independentValidationCanTightenEnvelope : Bool
    independentValidationCanTightenEnvelopeIsTrue :
      independentValidationCanTightenEnvelope ≡ true

canonicalGlyphosateSauerkrautBoundary : GlyphosateSauerkrautBoundary
canonicalGlyphosateSauerkrautBoundary = glyphosateSauerkrautBoundary
  false refl
  false refl
  false refl
  false refl
  true refl
  false refl
  true refl
