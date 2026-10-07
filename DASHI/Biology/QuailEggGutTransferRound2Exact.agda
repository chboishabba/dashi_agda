module DASHI.Biology.QuailEggGutTransferRound2Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.QuailEggHistamineGutSnowballExact as Gut
import DASHI.Biology.QuailEggHumanOralTransferExact as Oral
import DASHI.Biology.QuailEggAllergySafetyBoundaryExact as Safety
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Design

ovomucoidStability1994Source : Source.AttributedSource
ovomucoidStability1994Source = Source.mkDOISource
  "Japanese quail ovomucoid study authors as indexed by Journal of Nutritional Science and Vitaminology"
  "Inhibitory Specificity against Various Trypsins and Stability of Ovomucoid from Japanese Quail Egg White"
  "Journal of Nutritional Science and Vitaminology 40(6):593-601" "1994"
  "10.3177/jnsv.40.593" "https://doi.org/10.3177/jnsv.40.593"
  Source.academicArticleSource
  "Pays biochemical stability/trypsin-inhibitory evidence for Japanese-quail ovomucoid across broad pH, heat and pepsin-digestion conditions. It does not pay intact human intestinal exposure, anti-mast-cell activity after digestion, or IBS efficacy."
  Source.publicAttribution

gao2025Source : Source.AttributedSource
gao2025Source = Source.mkDOISource
  "Jun Gao; Allen A Lee; Shabnam Abtahi; Jerrold R Turner; Madhusudan Grover; Alexander Schmidt; Thomas M Schmidt; Judy W Nee; Johanna Iturrino; Anthony Lembo; William D Chey; John W Wiley; Prashant Singh"
  "Low Fermentable Oligosaccharides, Disaccharides, Monosaccharides, and Polyols Diet Improves Colonic Barrier Function and Mast Cell Activation in Patients With Diarrhea-Predominant Irritable Bowel Syndrome: A Mechanistic Trial"
  "Gastroenterology 170(1):132-147" "2026"
  "10.1053/j.gastro.2025.07.016" "https://doi.org/10.1053/j.gastro.2025.07.016"
  Source.academicArticleSource
  "Pays a human IBS-D dietary-mechanism surface: low-FODMAP intervention was associated with improved colonic barrier structure/function, mast-cell number and mediators; linked mouse experiments implicated fecal LPS/TLR4/mast-cell signaling. This is not evidence for quail egg."
  Source.publicAttribution

record QuailOvomucoidStabilityReceipt : Set where
  constructor quail-ovomucoid-stability-receipt
  field source : Source.AttributedSource
        broadPHStabilityObserved : Bool
        heatStabilityObserved : Bool
        pepsinResistanceObserved : Bool
        trypsinInhibitoryActivityRetained : Bool
        antiMastCellActivityAfterDigestionPaid : Bool
        humanGutTargetEngagementPaid : Bool

quailOvomucoidStability1994Receipt : QuailOvomucoidStabilityReceipt
quailOvomucoidStability1994Receipt = quail-ovomucoid-stability-receipt
  ovomucoidStability1994Source true true true true false false

record IBSDietMastCellMechanismReceipt : Set where
  constructor ibs-diet-mast-cell-mechanism-receipt
  field source : Source.AttributedSource
        humanIBSDPopulation : Bool
        dietIntervention : Bool
        barrierEndpoint : Bool
        mastCellEndpoint : Bool
        histamineMediatorEndpoint : Bool
        mouseTLR4Mechanism : Bool
        quailSpecificEvidence : Bool
        clinicalResponseEqualsPhysiologyChange : Bool

gao2025IBSDietMastCellReceipt : IBSDietMastCellMechanismReceipt
gao2025IBSDietMastCellReceipt = ibs-diet-mast-cell-mechanism-receipt
  gao2025Source true true true true true true false false

data BiochemicalStabilityPaysTargetEngagementPermission : Set where
biochemicalStabilityDoesNotPayTargetEngagement :
  BiochemicalStabilityPaysTargetEngagementPermission → ⊥
biochemicalStabilityDoesNotPayTargetEngagement ()

data OtherDietMechanismPaysQuailEfficacyPermission : Set where
otherDietDoesNotPayQuailEfficacy : OtherDietMechanismPaysQuailEfficacyPermission → ⊥
otherDietDoesNotPayQuailEfficacy ()

record SameObjectQuailGutExperiment : Set where
  constructor same-object-quail-gut-experiment
  field sourcePopulationSlot : Design.ExperimentalDesignSlot
        treatmentAssignmentSlot : Design.ExperimentalDesignSlot
        comparatorSlot : Design.ExperimentalDesignSlot
        baselineSlot : Design.ExperimentalDesignSlot
        endpointSlot : Design.ExperimentalDesignSlot
        timeSlot : Design.ExperimentalDesignSlot
        assaySlot : Design.ExperimentalDesignSlot
        nuisanceSlot : Design.ExperimentalDesignSlot
        mechanismSlot : Design.ExperimentalDesignSlot
        practicalSignificanceSlot : Design.ExperimentalDesignSlot
        treatmentIdentityReference : String
        digestionExposureReference : String
        histamineMastCellReference : String
        barrierReference : String
        microbiomeReference : String
        clinicalEndpointReference : String
        safetyReference : String

canonicalSameObjectQuailGutExperiment : SameObjectQuailGutExperiment
canonicalSameObjectQuailGutExperiment = same-object-quail-gut-experiment
  Design.sourcePopulationSlot Design.treatmentAssignmentSlot Design.comparatorSlot
  Design.baselineMeasurementSlot Design.endpointMeasurementSlot Design.timeSlot
  Design.assaySlot Design.nuisanceControlSlot Design.mechanismIdentificationSlot
  Design.practicalSignificanceSlot
  "quantified quail product with ovomucoid/albumen composition and preparation retained"
  "measure or validate digestion survival / intestinal exposure rather than infer from in-vitro stability"
  "mucosal or validated proxy histamine/tryptase/mast-cell activation endpoints"
  "barrier endpoint such as permeability/tight-junction measure where justified"
  "strain-/function-resolved histamine-producing microbiome and relevant substrate/pH context"
  "predeclared IBS symptom/pain/visceral-sensitivity outcome"
  "reuse QuailEggAllergySafetyBoundaryExact, including quail-specific allergy assessment and adverse-event monitoring"

record QuailEggGutTransferRound2Boundary : Set where
  constructor quail-egg-gut-transfer-round2-boundary
  field preclinicalMastCellLinkPaid : Bool
        humanOralExposureLinkPaid : Bool
        ovomucoidSurvivalPlausibilityPaid : Bool
        humanIBSDietMastCellPlasticityPaid : Bool
        quailSpecificHumanGutTargetEngagementPaid : Bool
        quailSpecificIBSEfficacyPaid : Bool
        safetyGateRetained : Bool
        sameObjectExperimentSpecified : Bool

canonicalQuailEggGutTransferRound2Boundary : QuailEggGutTransferRound2Boundary
canonicalQuailEggGutTransferRound2Boundary = quail-egg-gut-transfer-round2-boundary
  true true true true false false true true
