module DASHI.Biology.BemethylMechanismInterventionAcquisitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record MechanismInterventionAcquisition : Set where
  field
    glutathioneHypoxiaPMID : String
    model : String
    bemethylDose : String
    actinomycinDInterventionObserved : Bool
    protectiveEffectDependsOnTranscriptionCompatibleProcess : Bool
    glutathioneReductaseProtectionReported : Bool
    glutathionePeroxidaseProtectionReported : Bool

    cytochromeP450PMID : String
    humanLymphocyteInVitroEvidence : Bool
    p450InductionObserved : Bool
    p450InductionIdentifiesActoprotectiveTarget : Bool

    metabolismDockingPMID : String
    gstDockingSupportsConjugationPathway : Bool
    gstDockingProvesTherapeuticTarget : Bool

    interventionIdentifiesDirectBemethylTarget : Bool
    interventionProvesGenomeBinding : Bool
    interventionTransportsToHumanPerformance : Bool

    reading : String

open MechanismInterventionAcquisition public

canonicalMechanismInterventionAcquisition : MechanismInterventionAcquisition
canonicalMechanismInterventionAcquisition = record
  { glutathioneHypoxiaPMID = "12227091"
  ; model = "rat liver during acute hypoxic hypoxia"
  ; bemethylDose = "25 mg/kg intraperitoneal"
  ; actinomycinDInterventionObserved = true
  ; protectiveEffectDependsOnTranscriptionCompatibleProcess = true
  ; glutathioneReductaseProtectionReported = true
  ; glutathionePeroxidaseProtectionReported = true
  ; cytochromeP450PMID = "12227093"
  ; humanLymphocyteInVitroEvidence = true
  ; p450InductionObserved = true
  ; p450InductionIdentifiesActoprotectiveTarget = false
  ; metabolismDockingPMID = "34445727"
  ; gstDockingSupportsConjugationPathway = true
  ; gstDockingProvesTherapeuticTarget = false
  ; interventionIdentifiesDirectBemethylTarget = false
  ; interventionProvesGenomeBinding = false
  ; interventionTransportsToHumanPerformance = false
  ; reading = "Actinomycin-D inhibition provides causal evidence that one rat hepatic antioxidant effect requires a transcription-compatible process. Human lymphocyte P450 induction and GST docking add pathway evidence, but none identifies the direct actoprotective molecular target, direct genome binding, or a human performance mechanism."
  }

transcriptionDependencePaid :
  protectiveEffectDependsOnTranscriptionCompatibleProcess canonicalMechanismInterventionAcquisition ≡ true
transcriptionDependencePaid = refl

directTargetStillOpen :
  interventionIdentifiesDirectBemethylTarget canonicalMechanismInterventionAcquisition ≡ false
directTargetStillOpen = refl

gstDockingIsMetabolismEvidenceNotActoprotectionTarget :
  gstDockingProvesTherapeuticTarget canonicalMechanismInterventionAcquisition ≡ false
gstDockingIsMetabolismEvidenceNotActoprotectionTarget = refl
