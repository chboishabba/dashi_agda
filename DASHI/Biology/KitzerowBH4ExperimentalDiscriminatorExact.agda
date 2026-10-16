module DASHI.Biology.KitzerowBH4ExperimentalDiscriminatorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.KitzerowBH4CascadeExact as Cascade
import DASHI.Biology.KitzerowBH4HepaticCompetitionDiscriminatorExact as Hepatic
import DASHI.Biology.KitzerowBH4NeuralContextDiscriminatorExact as Neural
import DASHI.Biology.KitzerowBH4RedoxSpatialDiscriminatorExact as RedoxSpatial
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
    "live central edge requiring a same-object intervention that distinguishes adaptive BH4 allocation from downstream/parallel stress responses after accounting for supply buffering, redox regeneration, intracellular/extracellular route, spatial pool topology, developmental history, enzyme abundance and region/cell context"

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
    "extend the paid hepatic, neural and redox/spatial precedents: perturb GCH1/BH4 availability or redox-dependent BH4 allocation with temporally controlled intervention while independently manipulating intracellular supply, extracellular exposure and reductive-regeneration context where feasible"
    "matched stress/allostasis condition with BH4 allocation held or rescued independently; preserve hepatic phenylalanine/DAHP/BH4 logic, neural developmental/region stratification, and route-specific intracellular versus extracellular controls with orthogonal downstream/redox perturbations"
    "same-object BH4/BH2/GCH1 and NAD(P)H state, NOS-bound BH4 redox/coupling, PAH/TH/TPH/NOS/AGMO flux, TH/TPH/NOS/AGMO abundance/localization, intracellular/extracellular BH4 route, compartment/cell-type/region topology, redox state, mTOR/TSC2 and circuit readouts with calibrated timing"
    "test whether conditional supply-limited competition, pool-restoration failures and route-specific effects are mediated by adaptive synthesis/recycling, NAD(P)H-dependent regeneration, enzyme abundance, compartment, region, cell type, developmental history or parallel redox state; identify temporal order and mediation rather than scalar-pool correlation"
    "explicitly compare adaptive spatial allocator, downstream marker, parallel redox response and subgroup/state-history models; reject a naive fixed/well-mixed/current-pool-sufficiency model where existing data already show adaptive supply buffering, failed functional rescue, spatial separation and route-specific effects"
    "central edge closes only if new target-relevant same-object intervention plus mediation/temporal evidence extends beyond the paid hepatic PAH-iNOS, mouse neural and rat-striatal/NOS-redox constraints and discriminates the declared whole-model alternatives with compartment/route topology resolved"
    false refl
    false refl

------------------------------------------------------------------------
-- Historical discriminator payments consumed by the forward design.
------------------------------------------------------------------------

historicalSameObjectConstraint : Hepatic.HepaticCompetitionDiscriminator
historicalSameObjectConstraint = Hepatic.canonicalHepaticCompetitionDiscriminator

historicalNeuralContextConstraint : Neural.NeuralContextDiscriminator
historicalNeuralContextConstraint = Neural.canonicalNeuralContextDiscriminator

historicalRedoxSpatialConstraint : RedoxSpatial.RedoxSpatialDiscriminator
historicalRedoxSpatialConstraint = RedoxSpatial.canonicalRedoxSpatialDiscriminator

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

historicalConstraintsCloseCentralEdge : Bool
historicalConstraintsCloseCentralEdge = false

historicalConstraintsCloseCentralEdgeIsFalse : historicalConstraintsCloseCentralEdge ≡ false
historicalConstraintsCloseCentralEdgeIsFalse = refl

remainingExperimentalResidual : String
remainingExperimentalResidual =
  "target-relevant human/neural same-object multi-branch perturbation measuring BH4/BH2, NAD(P)H, NOS-bound BH4 redox/coupling, PAH/TH/TPH/NOS/AGMO flux, enzyme abundance/localization, intracellular versus extracellular route and transfer/supply topology by compartment/region/cell type/time; existing hepatic, mouse-neural, rat-striatal and NOS-bound redox results already rule out naive fixed/well-mixed/current-pool-sufficiency models but do not close the full architecture"

backpropBoundaryConsumed : Backprop.BlockedImplicationBackpropBoundary
backpropBoundaryConsumed = Backprop.canonicalBlockedImplicationBackpropBoundary

experimentalSelectionDoesNotPromoteClaim :
  Backprop.cheapestSelectedExperimentAutomaticallySupportsClaim
    backpropBoundaryConsumed
  ≡ false
experimentalSelectionDoesNotPromoteClaim = refl
