module DASHI.Environment.GlyphosateSauerkrautBlockedClaimExperimentBackpropExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.CostedResidualInformationChoiceExact as Costed
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone
import DASHI.Reasoning.BlockedImplicationExperimentBackpropExact as Backprop
import DASHI.Environment.GlyphosateSauerkrautAssertionPNFConeExact as Claim

------------------------------------------------------------------------
-- BLOCKED SHIOCTON CAUSAL CLAIM -> NEXT-EXPERIMENT DESIGN SPACE
------------------------------------------------------------------------

fullCausalBlockedEdge : Cone.ImplicationEdge
fullCausalBlockedEdge = Cone.implicationEdge
  "measured-shiocton-teg-decline"
  "full-rskj-causal-effect"
  Cone.attributesCausalEffect
  Cone.blockedEdge
  "headline contrast lacks the required same-time causal identification receipt"
  "gross decline cannot be equated with treatment-only effect"

fullCausalTarget : Backprop.BlockedImplicationTarget
fullCausalTarget = Backprop.blockedImplicationTarget
  Claim.fullCausalNode
  fullCausalBlockedEdge
  "the blocked edge targets the full-RSKJ-causal-effect node in the Shiocton implication cone"
  refl
  "identify or more tightly bound the incremental RSKJ-attributable component, not merely restate the observed decline"

fullCausalRequirement : Backprop.MissingDesignRequirement fullCausalTarget
fullCausalRequirement = Backprop.missingDesignRequirement
  Claim.causalObligation
  Cone.causalIdentificationSlot
  "headline Table-10 values are separated in time and do not carry a same-time endpoint causal contrast"
  "contemporaneous treated/control or otherwise causally identifying longitudinal design with explicit material-input and nuisance ledger"
  "elapsed time, indigenous microbiome, weather/moisture, assay error, new glyphosate input and sorption/availability remain live residuals"
  "new evidence must be reaudited for the causal-force obligation before the blocked edge can change status"

specificLABBlockedEdge : Cone.ImplicationEdge
specificLABBlockedEdge = Cone.implicationEdge
  "bounded-rskj-causal-envelope"
  "specific-lab-mechanism"
  Cone.identifiesMechanism
  Cone.blockedEdge
  "no mechanism-isolation receipt identifies introduced LAB as the unique cause"
  "indigenous microbes, chemistry/sorption and combined mechanisms remain live"

specificLABTarget : Backprop.BlockedImplicationTarget
specificLABTarget = Backprop.blockedImplicationTarget
  Claim.labNode
  specificLABBlockedEdge
  "the blocked edge targets the specific-LAB-mechanism node"
  refl
  "discriminate introduced-LAB causation from indigenous microbial, physicochemical and combined mechanisms"

specificLABRequirement : Backprop.MissingDesignRequirement specificLABTarget
specificLABRequirement = Backprop.missingDesignRequirement
  Claim.mechanismObligation
  Cone.mechanismIdentificationSlot
  "field residue decline does not isolate a microbial submechanism"
  "mechanism-discriminating intervention/assay with microbial identity/viability, glyphosate/AMPA transformation and matched abiotic/indigenous-microbiome controls"
  "introduced LAB, stimulated indigenous microbiome, pH/organic-carbon effects, sorption and combined mechanisms remain alternatives"
  "mechanism promotion requires a separately admissible mechanism receipt after discrimination"

------------------------------------------------------------------------
-- Candidate design vocabulary.
------------------------------------------------------------------------

data GlyphosateNextExperiment : Set where
  contemporaneousTreatedControlResidueTimeSeries
  materialInputLedgerPlusResidueTimeSeries
  indigenousMicrobiomeMatchedControl
  viableLABTrackingAndResidueTimeSeries
  sterileOrAbioticBrineControl
  pHCarbonIonicMatchedControl
  sorptionDesorptionFractionationAssay
  isotopeOrMassBalanceTransformationStudy
  independentFieldReplication
  : GlyphosateNextExperiment

record GlyphosateCandidateDesign : Set where
  constructor glyphosateCandidateDesign
  field
    experiment : GlyphosateNextExperiment
    targetsObligation : PNF.AssertionObligation
    targetsSlot : Cone.ExperimentalDesignSlot
    controlledCoordinatesReference : String
    measuredCoordinatesReference : String
    expectedDiscriminationReference : String
    calibrationNeededReference : String
    costReference : String
    replicationReference : String

open GlyphosateCandidateDesign public

causalCandidateDesigns : List GlyphosateCandidateDesign
causalCandidateDesigns =
  glyphosateCandidateDesign
    contemporaneousTreatedControlResidueTimeSeries
    Claim.causalObligation
    Cone.causalIdentificationSlot
    "hold sampling time/site management comparable while retaining treated versus untreated/control assignment"
    "glyphosate, AMPA/TEG, time, treatment and environmental covariates"
    "separates treatment-associated change from gross elapsed-time decline more directly than the headline contrast"
    "prospective variance/effect-size or pilot calibration required before assigning certified information gain"
    "field sampling and LC-MS/MS cost must be declared from actual protocol"
    "replicate across blocks/plots and ideally sites"
  ∷ glyphosateCandidateDesign
    materialInputLedgerPlusResidueTimeSeries
    Claim.causalObligation
    Cone.nuisanceControlSlot
    "record every glyphosate input/application plus relevant field interventions over the observation window"
    "material-input ledger plus repeated residue measurements"
    "bounds the new-input residual and prevents hidden re-entry from contaminating the causal budget"
    "gain depends on current uncertainty in the material-input coordinate"
    "ledger and sampling cost must be protocol-derived"
    "repeat across treatment/control units"
  ∷ glyphosateCandidateDesign
    indigenousMicrobiomeMatchedControl
    Claim.causalObligation
    Cone.nuisanceControlSlot
    "match treatment conditions while varying/characterising indigenous microbial contribution"
    "microbiome state plus glyphosate/AMPA trajectory"
    "narrows the indigenous-microbiome residual in the treatment-attribution fibre"
    "microbiome assay sensitivity and intervention fidelity require calibration"
    "sequencing/culture and residue-assay cost must be declared"
    "replicated matched controls required"
  ∷ []

mechanismCandidateDesigns : List GlyphosateCandidateDesign
mechanismCandidateDesigns =
  glyphosateCandidateDesign
    viableLABTrackingAndResidueTimeSeries
    Claim.mechanismObligation
    Cone.mechanismIdentificationSlot
    "track introduced LAB identity/viability while preserving matched soil/treatment controls"
    "LAB abundance/identity plus glyphosate and AMPA/other transformation products over time"
    "tests whether introduced LAB presence/activity covaries with the transformation trajectory"
    "viability/identity assay and mechanistic attribution still require calibration and controls"
    "culture/qPCR/metagenomic plus residue-analysis cost must be declared"
    "biological and field replication required"
  ∷ glyphosateCandidateDesign
    sterileOrAbioticBrineControl
    Claim.mechanismObligation
    Cone.mechanismIdentificationSlot
    "compare live RSKJ with appropriately matched non-live/abiotic brine while controlling chemistry as far as feasible"
    "residue trajectory plus viability and chemistry coordinates"
    "discriminates live-biological contribution from nonliving brine chemistry"
    "sterilisation may alter chemistry and therefore needs its own equivalence/perturbation receipt"
    "control preparation and analytical cost must be declared"
    "replicated treatment arms required"
  ∷ glyphosateCandidateDesign
    pHCarbonIonicMatchedControl
    Claim.mechanismObligation
    Cone.nuisanceControlSlot
    "match pH, organic-carbon/nutrient and ionic perturbations without assuming microbial equivalence"
    "soil chemistry plus residue trajectory"
    "narrows physicochemical alternatives to a specific microbial explanation"
    "matching quality must be measured rather than assumed"
    "chemistry and residue-analysis cost must be declared"
    "replicated matched controls required"
  ∷ glyphosateCandidateDesign
    sorptionDesorptionFractionationAssay
    Claim.mechanismObligation
    Cone.assaySlot
    "separate extractable/dissolved/adsorbed or otherwise operationally fractionated glyphosate states"
    "fractionated glyphosate/AMPA plus soil chemistry"
    "tests whether apparent residue loss reflects transformation versus redistribution/availability change"
    "fractionation recovery and assay model require validation"
    "fractionation and LC-MS/MS cost must be declared"
    "method and field replication required"
  ∷ glyphosateCandidateDesign
    isotopeOrMassBalanceTransformationStudy
    Claim.mechanismObligation
    Cone.mechanismIdentificationSlot
    "follow a labelled or otherwise mass-balanced glyphosate transformation pathway under controlled treatments"
    "parent compound, AMPA and downstream labelled/mass-balance products"
    "stronger discrimination of true transformation/mineralisation pathways from disappearance or sorption"
    "tracer recovery, pathway coverage and system fidelity require calibration"
    "specialised tracer/mass-spectrometry cost must be declared"
    "independent replication required"
  ∷ []

------------------------------------------------------------------------
-- Calibration gate into the generic cost/gain selector.
--
-- The candidate list does not invent a numeric expected gain. A design enters
-- `CostedResidualInformationChoiceExact` only after an application-specific
-- prospective/pilot or analytic calibration constructs the actual residual
-- move and its certified gain/cost.
------------------------------------------------------------------------

record CalibratedGlyphosateMove
    {Hidden : Set}
    (candidate : GlyphosateCandidateDesign) : Set₁ where
  constructor calibratedGlyphosateMove
  field
    residualMove : Costed.ResidualInformationMove Hidden
    experimentMatchesCandidateReference : String
    prospectiveGainCalibrationReference : String
    protocolCostCalibrationReference : String
    admissibilityForTargetObligationReference : String
    outcomeContingencyReference : String

open CalibratedGlyphosateMove public

record GlyphosateBackpropBoundary : Set where
  constructor glyphosateBackpropBoundary
  field
    candidateDesignListAlreadySuppliesCertifiedGain : Bool
    candidateDesignListAlreadySuppliesCertifiedGainIsFalse :
      candidateDesignListAlreadySuppliesCertifiedGain ≡ false
    sameTimeControlDirectlyIdentifiesLABMechanism : Bool
    sameTimeControlDirectlyIdentifiesLABMechanismIsFalse :
      sameTimeControlDirectlyIdentifiesLABMechanism ≡ false
    mechanismExperimentMayNeedMultipleOrthogonalControls : Bool
    mechanismExperimentMayNeedMultipleOrthogonalControlsIsTrue :
      mechanismExperimentMayNeedMultipleOrthogonalControls ≡ true
    calibrationRequiredBeforeCostGainSelection : Bool
    calibrationRequiredBeforeCostGainSelectionIsTrue :
      calibrationRequiredBeforeCostGainSelection ≡ true

canonicalGlyphosateBackpropBoundary : GlyphosateBackpropBoundary
canonicalGlyphosateBackpropBoundary =
  glyphosateBackpropBoundary false refl false refl true refl true refl
