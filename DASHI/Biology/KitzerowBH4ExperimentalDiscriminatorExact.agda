module DASHI.Biology.KitzerowBH4ExperimentalDiscriminatorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.KitzerowBH4CascadeExact as Cascade
import DASHI.Biology.KitzerowBH4HepaticCompetitionDiscriminatorExact as Hepatic
import DASHI.Biology.KitzerowBH4NeuralContextDiscriminatorExact as Neural
import DASHI.Biology.KitzerowBH4RedoxSpatialDiscriminatorExact as RedoxSpatial
import DASHI.Biology.KitzerowBH4TransportCarrierProbeExact as TransportProbe
import DASHI.Biology.KitzerowBH4NeuralInVivoRouteStateProbeExact as RouteState
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone
import DASHI.Reasoning.BlockedImplicationExperimentBackpropExact as Backprop

record ExperimentalDiscriminator : Set where
  constructor experimentalDiscriminator
  field
    targetEdge : Cascade.CascadeEdge
    missingDesignSlots : List Cone.ExperimentalDesignSlot
    interventionReference : String
    comparatorReference : String
    assayReference : String
    causalIdentificationReference : String
    alternativeArchitectureReference : String
    closureCriterionReference : String
    centralBH4AllocationClosed : Bool
    centralBH4AllocationClosedIsFalse : centralBH4AllocationClosed ≡ false
    selectedExperimentIsEvidence : Bool
    selectedExperimentIsEvidenceIsFalse : selectedExperimentIsEvidence ≡ false

open ExperimentalDiscriminator public

centralBH4AllocationEdge : Cascade.CascadeEdge
centralBH4AllocationEdge =
  Cascade.cascadeEdge
    "chronic allostasis -> redox/GCH1-mediated BH4 resource allocation"
    Cascade.chronicAllostasis
    Cascade.gch1RedoxBH4Allocation
    Cascade.unpaid
    "live central edge requiring one target-relevant same-object intervention that distinguishes adaptive spatial allocation from downstream/parallel/context-history explanations after accounting for supply buffering, redox regeneration, carrier context, intracellular/extracellular route, donor-recipient transfer, enzyme state and region/cell/developmental context"

canonicalCentralBH4Discriminator : ExperimentalDiscriminator
canonicalCentralBH4Discriminator =
  experimentalDiscriminator
    centralBH4AllocationEdge
    (Cone.treatmentAssignmentSlot
      ∷ Cone.comparatorSlot
      ∷ Cone.assaySlot
      ∷ Cone.nuisanceControlSlot
      ∷ Cone.causalIdentificationSlot
      ∷ Cone.mechanismIdentificationSlot
      ∷ [])
    "extend the paid hepatic, neural, redox/spatial, transport-carrier and in-vivo route/state precedents: perturb donor BH4 synthesis/recycling or transfer with isotope-resolved donor labeling while independently controlling extracellular BH4 exposure and redox-regeneration state"
    "matched target-relevant neural condition preserving cell/region/developmental state; include route controls that distinguish intracellular cofactor elevation from extracellular BH4 effects, and transporter/passive-route controls where relevant"
    "same-object donor/recipient BH4/BH2, isotope-resolved transfer rate/direction, NAD(P)H/redox, NOS-bound BH4/coupling, simultaneous TH/TPH/NOS/AGMO branch activity or flux, enzyme abundance/localization, transporter state, compartment/cell/region identity and calibrated time course"
    "estimate whether manipulation of donor BH4 supply/transfer temporally mediates simultaneous branch changes after conditioning on intracellular/extracellular route, enzyme state and parallel redox effects; quantify transfer rather than infer it from release, uptake, coculture or total tissue biopterin"
    "compare adaptive spatial allocator, downstream consequence, parallel-redox response and context/state-history models; total tissue BH4, generic extracellular exposure, universal passive diffusion and universal dedicated-carrier models are already excluded as sufficient descriptions by paid evidence"
    "central edge closes only if one target-relevant same-object intervention links donor-resolved BH4/BH2 transfer to simultaneous multi-branch mediation strongly enough to distinguish the declared alternatives; separate historical TH and TPH responses or extracellular dopamine-release effects do not satisfy closure"
    false refl
    false refl

historicalSameObjectConstraint : Hepatic.HepaticCompetitionDiscriminator
historicalSameObjectConstraint = Hepatic.canonicalHepaticCompetitionDiscriminator

historicalNeuralContextConstraint : Neural.NeuralContextDiscriminator
historicalNeuralContextConstraint = Neural.canonicalNeuralContextDiscriminator

historicalRedoxSpatialConstraint : RedoxSpatial.RedoxSpatialDiscriminator
historicalRedoxSpatialConstraint = RedoxSpatial.canonicalRedoxSpatialDiscriminator

historicalTransportCarrierConstraint : TransportProbe.TransportTopologyUpgrade
historicalTransportCarrierConstraint = TransportProbe.canonicalTransportTopologyUpgrade

historicalRouteStateConstraint : RouteState.RouteStateBackprop
historicalRouteStateConstraint = RouteState.canonicalRouteStateBackprop

historicalTwoBranchConstraintPaid : Bool
historicalTwoBranchConstraintPaid = true
historicalTwoBranchConstraintPaidIsTrue : historicalTwoBranchConstraintPaid ≡ true
historicalTwoBranchConstraintPaidIsTrue = refl

historicalNeuralContextConstraintPaid : Bool
historicalNeuralContextConstraintPaid = true
historicalNeuralContextConstraintPaidIsTrue : historicalNeuralContextConstraintPaid ≡ true
historicalNeuralContextConstraintPaidIsTrue = refl

historicalRedoxSpatialConstraintPaid : Bool
historicalRedoxSpatialConstraintPaid = true
historicalRedoxSpatialConstraintPaidIsTrue : historicalRedoxSpatialConstraintPaid ≡ true
historicalRedoxSpatialConstraintPaidIsTrue = refl

historicalTransportCarrierConstraintPaid : Bool
historicalTransportCarrierConstraintPaid = true
historicalTransportCarrierConstraintPaidIsTrue : historicalTransportCarrierConstraintPaid ≡ true
historicalTransportCarrierConstraintPaidIsTrue = refl

historicalRouteStateConstraintPaid : Bool
historicalRouteStateConstraintPaid = true
historicalRouteStateConstraintPaidIsTrue : historicalRouteStateConstraintPaid ≡ true
historicalRouteStateConstraintPaidIsTrue = refl

historicalConstraintsCloseCentralEdge : Bool
historicalConstraintsCloseCentralEdge = false
historicalConstraintsCloseCentralEdgeIsFalse : historicalConstraintsCloseCentralEdge ≡ false
historicalConstraintsCloseCentralEdgeIsFalse = refl

remainingExperimentalResidual : String
remainingExperimentalResidual =
  "one target-relevant neural same-object perturbation with donor-labelled BH4/BH2 transfer, simultaneous TH/TPH/NOS/AGMO branch activity/flux, NAD(P)H/redox and enzyme-state measurements by compartment/cell/region/time; route-specific branch responses, transport existence and separate in-vivo TH/TPH activation are paid, but donor-resolved transfer-mediated simultaneous allocation remains unpaid"

backpropBoundaryConsumed : Backprop.BlockedImplicationBackpropBoundary
backpropBoundaryConsumed = Backprop.canonicalBlockedImplicationBackpropBoundary

experimentalSelectionDoesNotPromoteClaim :
  Backprop.cheapestSelectedExperimentAutomaticallySupportsClaim backpropBoundaryConsumed ≡ false
experimentalSelectionDoesNotPromoteClaim = refl
