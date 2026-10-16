module DASHI.Biology.KitzerowBH4ExperimentalDiscriminatorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.KitzerowBH4CascadeExact as Cascade
import DASHI.Biology.KitzerowBH4HepaticCompetitionDiscriminatorExact as Hepatic
import DASHI.Biology.KitzerowBH4NeuralContextDiscriminatorExact as Neural
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
    "live central edge requiring a same-object intervention that distinguishes BH4 allocation from downstream or parallel stress responses after accounting for adaptive supply, developmental history, enzyme abundance and region/cell context"

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
    "extend the paid Pastor hepatic and Hyland/Jiang neural precedents: perturb GCH1/BH4 availability or redox-dependent BH4 allocation with temporally controlled intervention while measuring multiple branch-specific fluxes and enzyme-state coordinates"
    "matched stress/allostasis condition with BH4 allocation held or rescued independently; preserve hepatic phenylalanine/DAHP/BH4 logic while stratifying neural region/cell type/developmental history and adding orthogonal redox/downstream controls"
    "same-object BH4/BH2/GCH1 and NAD(P)H state, NOS coupling, PAH/TH/TPH flux, AGMO/ether-lipid flux, TH/TPH/NOS/AGMO abundance/localization, redox state, mTOR/TSC2, compartment/cell-type/region and circuit readouts with calibrated timing"
    "test whether conditional supply-limited competition and pool-restoration failures are mediated by enzyme abundance, region, cell type, developmental history or parallel redox state; identify temporal order and mediation rather than scalar pool correlation"
    "explicitly compare adaptive allocator, downstream marker, parallel redox response and subgroup/context-specific state-history models; reject a naive fixed-pool/current-pool-sufficiency model where existing data already show adaptive supply buffering or failed functional rescue"
    "central edge closes only if new same-object intervention plus mediation/temporal evidence extends beyond the paid hepatic PAH-iNOS and mouse neural constraints and discriminates the declared whole-model alternatives in the target-relevant context"
    false refl
    false refl

------------------------------------------------------------------------
-- Historical discriminator payments consumed by the forward design.
------------------------------------------------------------------------

historicalSameObjectConstraint : Hepatic.HepaticCompetitionDiscriminator
historicalSameObjectConstraint = Hepatic.canonicalHepaticCompetitionDiscriminator

historicalNeuralContextConstraint : Neural.NeuralContextDiscriminator
historicalNeuralContextConstraint = Neural.canonicalNeuralContextDiscriminator

historicalTwoBranchConstraintPaid : Bool
historicalTwoBranchConstraintPaid = true

historicalTwoBranchConstraintPaidIsTrue : historicalTwoBranchConstraintPaid ≡ true
historicalTwoBranchConstraintPaidIsTrue = refl

historicalNeuralContextConstraintPaid : Bool
historicalNeuralContextConstraintPaid = true

historicalNeuralContextConstraintPaidIsTrue : historicalNeuralContextConstraintPaid ≡ true
historicalNeuralContextConstraintPaidIsTrue = refl

historicalConstraintsCloseCentralEdge : Bool
historicalConstraintsCloseCentralEdge = false

historicalConstraintsCloseCentralEdgeIsFalse : historicalConstraintsCloseCentralEdge ≡ false
historicalConstraintsCloseCentralEdgeIsFalse = refl

remainingExperimentalResidual : String
remainingExperimentalResidual =
  "target-relevant human/neural same-object multi-branch perturbation measuring BH4/BH2, NAD(P)H, PAH/TH/TPH/NOS/AGMO flux and enzyme abundance/localization by region/cell type/time; existing rat hepatic and mouse neural results already rule out naive fixed-pool/current-pool-sufficiency models but do not close the full architecture"

backpropBoundaryConsumed : Backprop.BlockedImplicationBackpropBoundary
backpropBoundaryConsumed = Backprop.canonicalBlockedImplicationBackpropBoundary

experimentalSelectionDoesNotPromoteClaim :
  Backprop.cheapestSelectedExperimentAutomaticallySupportsClaim
    backpropBoundaryConsumed
  ≡ false
experimentalSelectionDoesNotPromoteClaim = refl
