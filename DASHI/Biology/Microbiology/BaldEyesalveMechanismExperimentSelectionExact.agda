module DASHI.Biology.Microbiology.BaldEyesalveMechanismExperimentSelectionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as TK
import DASHI.Biology.Microbiology.BaldEyesalveNineDayMechanismWeldExact as Weld

------------------------------------------------------------------------
-- MECHANISM-DISCRIMINATING EXPERIMENT SELECTION
--
-- This x-pollinates the generic Chemistry.TransitionKernel experiment-search
-- carrier into the Bald's-eyesalve mechanism frontier.  Scores are ordinal
-- qualitative priorities, not measured information gains.
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
  ; measuredCarrier = "matched chemical, thiol/redox, regulatory and phenotype readouts under branch-selective perturbation or rescue"
  ; uncertaintyTarget = "causal mediation rather than association"
  ; expectedModelSpaceReduction = record { lower = 8 ; upper = 10 }
  ; protocolReceiptRequired = true
  }

candidateExperiments : List TK.ExperimentCandidate
candidateExperiments =
  timeResolvedSulfurSpeciation ∷
  staphThiolomeUnderPreparation ∷
  quorumReporterPanel ∷
  mechanismPerturbationRescue ∷ []

canonicalMechanismExperimentSelection : TK.ExperimentSelection
canonicalMechanismExperimentSelection = record
  { candidates = candidateExperiments
  ; rankingCriterion = "first resolve target-preparation molecular identity/trajectory; then direct target-system molecular action; then regulatory association; finally causal mediation"
  ; selectedExperiment = "BE-X1 time-resolved sulfur speciation fresh-to-day-9"
  ; selectionValidated = false
  }

record ExperimentOrderingBoundary : Set where
  constructor experimentOrderingBoundary
  field
    sourceBackedCandidateEqualsTargetPreparationPresence : Bool
    sourceBackedCandidateEqualsTargetPreparationPresenceIsFalse :
      sourceBackedCandidateEqualsTargetPreparationPresence ≡ false

    reporterShiftEqualsMediation : Bool
    reporterShiftEqualsMediationIsFalse : reporterShiftEqualsMediation ≡ false

    phenotypeCovariationEqualsCausation : Bool
    phenotypeCovariationEqualsCausationIsFalse : phenotypeCovariationEqualsCausation ≡ false

    resolvingChemicalTrajectoryBeforeDownstreamMediationReducesConfounding : Bool
    resolvingChemicalTrajectoryBeforeDownstreamMediationReducesConfoundingIsTrue :
      resolvingChemicalTrajectoryBeforeDownstreamMediationReducesConfounding ≡ true

canonicalExperimentOrderingBoundary : ExperimentOrderingBoundary
canonicalExperimentOrderingBoundary =
  experimentOrderingBoundary false refl false refl false refl true refl

-- The selection consumes the current welded frontier rather than inventing a
-- separate list of mechanism claims.
existingNineDayBoundary : Weld.NineDayMechanismBoundary
existingNineDayBoundary = Weld.canonicalNineDayMechanismBoundary
