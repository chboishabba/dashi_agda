module DASHI.Biology.Microbiology.BaldEyesalveMechanismExperimentSelectionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as TK
import DASHI.Biology.Microbiology.BaldEyesalveNineDayMechanismWeldExact as Weld

------------------------------------------------------------------------
-- MECHANISM-DISCRIMINATING EXPERIMENT SELECTION
------------------------------------------------------------------------

timeResolvedSulfurSpeciation : TK.ExperimentCandidate
timeResolvedSulfurSpeciation = record
  { experimentId = "BE-X1 time-resolved sulfur speciation fresh-to-day-9"
  ; measuredCarrier = "LC-MS/GC-MS target-preparation profile: allicin, ajoenes, vinyl dithiins, diallyl polysulfides and related sulfur species"
  ; uncertaintyTarget = "which source-backed Allium transformation branches actually occur in the reconstructed preparation, and when"
  ; expectedModelSpaceReduction = record { lower = 8 ; upper = 10 }
  ; protocolReceiptRequired = true
  }

staphThiolomeUnderPreparation : TK.ExperimentCandidate
staphThiolomeUnderPreparation = record
  { experimentId = "BE-X2 S. aureus thiolome under fresh and matured complete preparation"
  ; measuredCarrier = "protein S-thioallylation / low-molecular-weight thiol redox state / BSH pathway response"
  ; uncertaintyTarget = "whether the direct pure-allicin S. aureus thiolome transfers to the complete target preparation"
  ; expectedModelSpaceReduction = record { lower = 7 ; upper = 10 }
  ; protocolReceiptRequired = true
  }

proteinFunctionCellStatePanel : TK.ExperimentCandidate
proteinFunctionCellStatePanel = record
  { experimentId = "BE-X2F protein-function and coupled-cell-state panel"
  ; measuredCarrier = "target activity/translation/metabolic flux plus matched proteome, RNA/regulatory and redox-recovery state"
  ; uncertaintyTarget = "which observed S-thioallylations alter protein function and which functional changes propagate into coupled cell state"
  ; expectedModelSpaceReduction = record { lower = 6 ; upper = 10 }
  ; protocolReceiptRequired = true
  }

quorumReporterPanel : TK.ExperimentCandidate
quorumReporterPanel = record
  { experimentId = "BE-X3 organism-appropriate quorum/virulence reporter panel"
  ; measuredCarrier = "signal-system reporter output, virulence-regulatory output and biofilm phenotype under matched exposure"
  ; uncertaintyTarget = "whether quorum-associated regulation changes under the complete preparation"
  ; expectedModelSpaceReduction = record { lower = 4 ; upper = 8 }
  ; protocolReceiptRequired = true
  }

mechanismPerturbationRescue : TK.ExperimentCandidate
mechanismPerturbationRescue = record
  { experimentId = "BE-X4 perturbation/rescue mediation panel"
  ; measuredCarrier = "matched chemical, thiol/redox, protein-function, regulatory, cell-state and phenotype readouts under branch-selective perturbation or rescue"
  ; uncertaintyTarget = "causal mediation rather than association"
  ; expectedModelSpaceReduction = record { lower = 8 ; upper = 10 }
  ; protocolReceiptRequired = true
  }

candidateExperiments : List TK.ExperimentCandidate
candidateExperiments =
  timeResolvedSulfurSpeciation ∷
  staphThiolomeUnderPreparation ∷
  proteinFunctionCellStatePanel ∷
  quorumReporterPanel ∷
  mechanismPerturbationRescue ∷ []

canonicalMechanismExperimentSelection : TK.ExperimentSelection
canonicalMechanismExperimentSelection = record
  { candidates = candidateExperiments
  ; rankingCriterion = "resolve target-preparation chemistry; then target-system modification; then protein function/cell state; then regulatory association; finally perturbation/rescue mediation"
  ; selectedExperiment = "BE-X1 time-resolved sulfur speciation fresh-to-day-9"
  ; selectionValidated = false
  }

record ExperimentOrderingBoundary : Set where
  constructor experimentOrderingBoundary
  field
    sourceBackedCandidateEqualsTargetPreparationPresence : Bool
    sourceBackedCandidateEqualsTargetPreparationPresenceIsFalse :
      sourceBackedCandidateEqualsTargetPreparationPresence ≡ false
    proteinModificationEqualsFunctionalPerturbation : Bool
    proteinModificationEqualsFunctionalPerturbationIsFalse :
      proteinModificationEqualsFunctionalPerturbation ≡ false
    functionalPerturbationEqualsWholeCellState : Bool
    functionalPerturbationEqualsWholeCellStateIsFalse :
      functionalPerturbationEqualsWholeCellState ≡ false
    reporterShiftEqualsMediation : Bool
    reporterShiftEqualsMediationIsFalse : reporterShiftEqualsMediation ≡ false
    phenotypeCovariationEqualsCausation : Bool
    phenotypeCovariationEqualsCausationIsFalse : phenotypeCovariationEqualsCausation ≡ false
    resolvingChemicalTrajectoryBeforeDownstreamMediationReducesConfounding : Bool
    resolvingChemicalTrajectoryBeforeDownstreamMediationReducesConfoundingIsTrue :
      resolvingChemicalTrajectoryBeforeDownstreamMediationReducesConfounding ≡ true

canonicalExperimentOrderingBoundary : ExperimentOrderingBoundary
canonicalExperimentOrderingBoundary =
  experimentOrderingBoundary false refl false refl false refl false refl false refl true refl

existingNineDayBoundary : Weld.NineDayMechanismBoundary
existingNineDayBoundary = Weld.canonicalNineDayMechanismBoundary
