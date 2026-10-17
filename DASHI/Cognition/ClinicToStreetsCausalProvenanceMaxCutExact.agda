module DASHI.Cognition.ClinicToStreetsCausalProvenanceMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Cognition.ClinicToStreetsCausalProvenanceExact as CTS
import DASHI.Biology.EmbodiedCausalConeFeedbackExact as Cone

------------------------------------------------------------------------
-- MAX-CUT: LITERAL FINITE CAUSAL DAG
--
-- The previous owner proved a Boolean provenance-erasure witness.  This owner
-- refines that witness onto one literal finite graph so that we can ask which
-- upstream edges disappear, how salience/responsibility moves, and whether the
-- represented action cone contracts.  The numbers below are model coordinates,
-- not empirical estimates and not claims about any person or therapy.
------------------------------------------------------------------------

data Node : Set where
  structuralCondition familySite psychicState collectiveAction individualAction : Node

data Edge : Set where
  structuralToFamily familyToPsychic structuralToPsychic psychicToCollective psychicToIndividual : Edge

edgeSource : Edge → Node
edgeSource structuralToFamily = structuralCondition
edgeSource familyToPsychic = familySite
edgeSource structuralToPsychic = structuralCondition
edgeSource psychicToCollective = psychicState
edgeSource psychicToIndividual = psychicState

edgeTarget : Edge → Node
edgeTarget structuralToFamily = familySite
edgeTarget familyToPsychic = psychicState
edgeTarget structuralToPsychic = psychicState
edgeTarget psychicToCollective = collectiveAction
edgeTarget psychicToIndividual = individualAction

edgeWeight : Edge → Nat
edgeWeight structuralToFamily = 4
edgeWeight familyToPsychic = 3
edgeWeight structuralToPsychic = 2
edgeWeight psychicToCollective = 3
edgeWeight psychicToIndividual = 1

data InterpretationView : Set where
  fullView atomisedView reskilledView : InterpretationView

edgeVisible : InterpretationView → Edge → Bool
edgeVisible fullView _ = true
edgeVisible atomisedView structuralToFamily = false
edgeVisible atomisedView structuralToPsychic = false
edgeVisible atomisedView _ = true
edgeVisible reskilledView _ = true

------------------------------------------------------------------------
-- Exact deletion receipts.
------------------------------------------------------------------------

structuralFamilyDeletedByAtomisation :
  edgeVisible fullView structuralToFamily ≡ true
  × (edgeVisible atomisedView structuralToFamily ≡ false)
structuralFamilyDeletedByAtomisation = refl , refl

structuralPsychicDeletedByAtomisation :
  edgeVisible fullView structuralToPsychic ≡ true
  × (edgeVisible atomisedView structuralToPsychic ≡ false)
structuralPsychicDeletedByAtomisation = refl , refl

familyPsychicRetainedByAtomisation :
  edgeVisible atomisedView familyToPsychic ≡ true
familyPsychicRetainedByAtomisation = refl

reskillingRestoresStructuralFamily :
  edgeVisible reskilledView structuralToFamily ≡ true
reskillingRestoresStructuralFamily = refl

reskillingRestoresStructuralPsychic :
  edgeVisible reskilledView structuralToPsychic ≡ true
reskillingRestoresStructuralPsychic = refl

------------------------------------------------------------------------
-- Weighted ancestor/salience coordinate.
--
-- `psychicUpstreamSalience` is deliberately a finite model metric: sum of the
-- weights of represented upstream explanatory edges into the psychic/family
-- path.  It is not a calibrated psychological quantity.
------------------------------------------------------------------------

psychicUpstreamSalience : InterpretationView → Nat
psychicUpstreamSalience fullView = 9
psychicUpstreamSalience atomisedView = 3
psychicUpstreamSalience reskilledView = 9

atomisationDeletesSixUnitsOfRepresentedUpstreamSalience :
  psychicUpstreamSalience fullView ≡ 9
  × psychicUpstreamSalience atomisedView ≡ 3
atomisationDeletesSixUnitsOfRepresentedUpstreamSalience = refl , refl

reskillingRestoresFullRepresentedUpstreamSalience :
  psychicUpstreamSalience reskilledView ≡ psychicUpstreamSalience fullView
reskillingRestoresFullRepresentedUpstreamSalience = refl

------------------------------------------------------------------------
-- Responsibility-attribution redistribution.
--
-- This does NOT assert moral/legal responsibility.  It is a coordinate of the
-- represented explanatory narrative: where causal responsibility is assigned
-- after the interpretation operator acts.
------------------------------------------------------------------------

record ResponsibilityProfile : Set where
  constructor responsibility-profile
  field
    structuralShare : Nat
    intimateShare : Nat
    individualShare : Nat

fullResponsibility : ResponsibilityProfile
fullResponsibility = responsibility-profile 6 3 1

atomisedResponsibility : ResponsibilityProfile
atomisedResponsibility = responsibility-profile 0 3 7

reskilledResponsibility : ResponsibilityProfile
reskilledResponsibility = responsibility-profile 6 3 1

atomisationReassignsStructuralShareToIndividual :
  ResponsibilityProfile.structuralShare fullResponsibility ≡ 6
  × ResponsibilityProfile.structuralShare atomisedResponsibility ≡ 0
  × ResponsibilityProfile.individualShare fullResponsibility ≡ 1
  × ResponsibilityProfile.individualShare atomisedResponsibility ≡ 7
atomisationReassignsStructuralShareToIndividual = refl , refl , refl , refl

reskillingRestoresResponsibilityProfile :
  ResponsibilityProfile.structuralShare reskilledResponsibility
    ≡ ResponsibilityProfile.structuralShare fullResponsibility
  × ResponsibilityProfile.intimateShare reskilledResponsibility
    ≡ ResponsibilityProfile.intimateShare fullResponsibility
  × ResponsibilityProfile.individualShare reskilledResponsibility
    ≡ ResponsibilityProfile.individualShare fullResponsibility
reskillingRestoresResponsibilityProfile = refl , refl , refl

------------------------------------------------------------------------
-- Action-cone contraction.
------------------------------------------------------------------------

data ActionOption : Set where
  individualAdaptation collectiveCoordination structuralIntervention : ActionOption

actionAvailable : InterpretationView → ActionOption → Bool
actionAvailable fullView _ = true
actionAvailable atomisedView individualAdaptation = true
actionAvailable atomisedView collectiveCoordination = false
actionAvailable atomisedView structuralIntervention = false
actionAvailable reskilledView _ = true

actionConeCardinality : InterpretationView → Nat
actionConeCardinality fullView = 3
actionConeCardinality atomisedView = 1
actionConeCardinality reskilledView = 3

atomisationContractsRepresentedActionCone :
  actionConeCardinality fullView ≡ 3
  × actionConeCardinality atomisedView ≡ 1
atomisationContractsRepresentedActionCone = refl , refl

reskillingReopensRepresentedActionCone :
  actionConeCardinality reskilledView ≡ actionConeCardinality fullView
reskillingReopensRepresentedActionCone = refl

------------------------------------------------------------------------
-- Cross-pollination: embodied causal-cone machinery.
--
-- The embodied donor proves that history can deform a transition gate without
-- deleting the carrier.  This is exactly the firewall needed here: reduced
-- represented accessibility is not ontological deletion of the underlying
-- action/transition.
------------------------------------------------------------------------

historyCanDeformGateWithoutDeletingCarrier :
  Cone.gate Cone.baselineLaw Cone.approachSafety
  ≡ Cone.gate Cone.learnedThreatLaw Cone.approachSafety → ⊥
historyCanDeformGateWithoutDeletingCarrier =
  Cone.historyDeformationCanCloseApproachWithoutDeletingTransition

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data ModelWeightImpliesEmpiricalMagnitude : Set where
modelWeightDoesNotEstablishEmpiricalMagnitude :
  ModelWeightImpliesEmpiricalMagnitude → ⊥
modelWeightDoesNotEstablishEmpiricalMagnitude ()

data ResponsibilityCoordinateImpliesMoralFault : Set where
responsibilityCoordinateDoesNotEstablishMoralFault :
  ResponsibilityCoordinateImpliesMoralFault → ⊥
responsibilityCoordinateDoesNotEstablishMoralFault ()

data ActionConeContractionImpliesIntent : Set where
actionConeContractionDoesNotEstablishIntent :
  ActionConeContractionImpliesIntent → ⊥
actionConeContractionDoesNotEstablishIntent ()

record MaxCutBoundary : Set where
  constructor max-cut-boundary
  field
    literalDAGPresent : Bool
    upstreamDeletionMeasured : Bool
    responsibilityRedistributionRepresented : Bool
    actionConeContractionRepresented : Bool
    reskillingRestorationRepresented : Bool
    modelWeightsAreEmpiricalMagnitudes : Bool
    explanatoryResponsibilityIsMoralFault : Bool
    actionConeContractionEstablishesIntent : Bool
    underlyingCarrierDeletedByAccessibilityChange : Bool

canonicalMaxCutBoundary : MaxCutBoundary
canonicalMaxCutBoundary =
  max-cut-boundary true true true true true false false false false
