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
    "live central edge requiring a same-object intervention that distinguishes adaptive BH4 allocation from downstream/parallel stress responses after accounting for supply buffering, redox regeneration, context-specific carrier mechanisms, cellular uptake, intracellular/extracellular route, donor-recipient transfer, spatial pool topology, developmental history, enzyme abundance and region/cell context"

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
    "extend the paid hepatic, neural, redox/spatial and transport-carrier precedents: perturb GCH1/BH4 availability or redox-dependent BH4 allocation while independently manipulating intracellular supply, extracellular exposure and reductive-regeneration context; isotope-label donor pterin/BH4 to measure target neural donor-to-recipient transfer rather than inferring it from release, uptake, coculture function or non-neural transcellular rates"
    "matched stress/allostasis condition with BH4 allocation held or rescued independently; preserve hepatic phenylalanine/DAHP/BH4 logic, neural developmental/region stratification, route-specific intracellular versus extracellular controls and transporter/passive-route controls with orthogonal downstream/redox perturbations"
    "same-object BH4/BH2/GCH1 and NAD(P)H state, NOS-bound BH4 redox/coupling, PAH/TH/TPH/NOS/AGMO flux, TH/TPH/NOS/AGMO abundance/localization, intracellular/extracellular BH4 route, transporter expression/inhibition where relevant, isotope-resolved donor-to-recipient BH4/BH2 transfer, compartment/cell-type/region topology, redox state, mTOR/TSC2 and circuit readouts with calibrated timing"
    "test whether conditional supply-limited competition, pool-restoration failures and route-specific effects are mediated by adaptive synthesis/recycling, NAD(P)H-dependent regeneration, context-specific transporter edges, passive-like movement, enzyme abundance, quantitative transfer, compartment, region, cell type, developmental history or parallel redox state; identify temporal order and mediation rather than scalar-pool correlation"
    "explicitly compare adaptive spatial allocator, downstream marker, parallel redox response and subgroup/state-history models; reject both universal-passive and universal-dedicated-carrier assumptions because transport mechanism is already empirically context-dependent"
    "central edge closes only if new target-relevant same-object intervention plus mediation/temporal evidence extends beyond paid hepatic PAH-iNOS, mouse neural, rat-striatal, NOS-redox, catecholaminergic release/recipient uptake/coculture, epithelial transcellular-rate and ENT/OAT transport constraints and discriminates declared whole-model alternatives with transfer/compartment/route topology resolved"
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

historicalConstraintsCloseCentralEdge : Bool
historicalConstraintsCloseCentralEdge = false
historicalConstraintsCloseCentralEdgeIsFalse : historicalConstraintsCloseCentralEdge ≡ false
historicalConstraintsCloseCentralEdgeIsFalse = refl

remainingExperimentalResidual : String
remainingExperimentalResidual =
  "target-relevant human/neural same-object multi-branch perturbation measuring BH4/BH2, NAD(P)H, NOS-bound BH4 redox/coupling, PAH/TH/TPH/NOS/AGMO flux, enzyme abundance/localization, intracellular versus extracellular route, relevant transporter expression/inhibition and isotope-resolved donor-to-recipient BH4/BH2 rate/direction by compartment/region/cell type/time; general transport existence and one epithelial transcellular rate are paid, but neural donor-to-recipient molecular flux and simultaneous whole-network mediation remain unpaid"

backpropBoundaryConsumed : Backprop.BlockedImplicationBackpropBoundary
backpropBoundaryConsumed = Backprop.canonicalBlockedImplicationBackpropBoundary

experimentalSelectionDoesNotPromoteClaim :
  Backprop.cheapestSelectedExperimentAutomaticallySupportsClaim backpropBoundaryConsumed ≡ false
experimentalSelectionDoesNotPromoteClaim = refl
