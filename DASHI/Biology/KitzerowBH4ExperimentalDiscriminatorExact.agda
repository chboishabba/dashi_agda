module DASHI.Biology.KitzerowBH4ExperimentalDiscriminatorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.KitzerowBH4CascadeExact as Cascade
import DASHI.Biology.KitzerowBH4HepaticCompetitionDiscriminatorExact as Hepatic
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
    "live central edge requiring a same-object intervention that distinguishes BH4 allocation from downstream or parallel stress responses"

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
    "extend the Pastor-et-al hepatic precedent: perturb GCH1/BH4 availability or redox-dependent BH4 allocation with temporally controlled intervention while measuring multiple branch-specific fluxes, not only terminal phenotype"
    "matched stress/allostasis condition with BH4 allocation held or rescued independently; preserve the historical phenylalanine/DAHP/BH4 logic while adding orthogonal redox and downstream controls"
    "same-object BH4/BH2/GCH1 and NAD(P)H state, NOS coupling, PAH/TH/TPH flux, AGMO/ether-lipid flux, redox state, mTOR/TSC2, compartment/cell-type and circuit readouts with calibrated timing"
    "test whether the conditional supply-limited competition seen in rat PAH-iNOS generalizes, disappears, or changes sign across declared human/neural/subgroup contexts; identify mediation and temporal order"
    "explicitly compare adaptive allocator, downstream marker, parallel redox response and subgroup/context-specific models; reject a naive fixed-pool model where adaptive BH4 synthesis buffers demand"
    "central edge closes only if new same-object intervention plus mediation/temporal evidence extends beyond the paid hepatic PAH-iNOS subgraph and discriminates the declared whole-model alternatives"
    false refl
    false refl

------------------------------------------------------------------------
-- Historical discriminator payment consumed by the forward design.
------------------------------------------------------------------------

historicalSameObjectConstraint : Hepatic.HepaticCompetitionDiscriminator
historicalSameObjectConstraint = Hepatic.canonicalHepaticCompetitionDiscriminator

historicalTwoBranchConstraintPaid : Bool
historicalTwoBranchConstraintPaid = true

historicalTwoBranchConstraintPaidIsTrue : historicalTwoBranchConstraintPaid ≡ true
historicalTwoBranchConstraintPaidIsTrue = refl

historicalConstraintClosesCentralEdge : Bool
historicalConstraintClosesCentralEdge = false

historicalConstraintClosesCentralEdgeIsFalse : historicalConstraintClosesCentralEdge ≡ false
historicalConstraintClosesCentralEdgeIsFalse = refl

remainingExperimentalResidual : String
remainingExperimentalResidual =
  "human/neural or otherwise target-relevant same-object multi-branch perturbation measuring BH4/BH2, NAD(P)H and PAH/TH/TPH/NOS/AGMO flux with compartment, timing and subgroup controls; the rat hepatic PAH-iNOS result is a direct constraint, not whole-model closure"

backpropBoundaryConsumed : Backprop.BlockedImplicationBackpropBoundary
backpropBoundaryConsumed = Backprop.canonicalBlockedImplicationBackpropBoundary

experimentalSelectionDoesNotPromoteClaim :
  Backprop.cheapestSelectedExperimentAutomaticallySupportsClaim
    backpropBoundaryConsumed
  ≡ false
experimentalSelectionDoesNotPromoteClaim = refl
