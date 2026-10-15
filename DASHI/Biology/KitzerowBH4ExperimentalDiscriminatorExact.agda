module DASHI.Biology.KitzerowBH4ExperimentalDiscriminatorExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.KitzerowBH4CascadeExact as Cascade
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
    "perturb GCH1/BH4 availability or redox-dependent BH4 allocation with temporally controlled intervention while measuring branch-specific flux rather than only terminal phenotype"
    "matched stress/allostasis condition with BH4 allocation held or rescued independently; include interventions on downstream NOS/mTOR and parallel stress pathways"
    "same-object BH4/BH2/GCH1 state, NOS coupling, AAAH flux, AGMO/ether-lipid flux, redox state, mTOR/TSC2, cell-type and circuit readouts with calibrated timing"
    "identify whether manipulating BH4 allocation changes multiple proposed branches before downstream phenotype and whether rescue follows the predicted mediation path"
    "explicitly compare models in which BH4 is upstream organiser versus downstream marker, parallel compensatory response, or subgroup-specific correlate"
    "central edge closes only if same-object intervention plus mediation/temporal evidence discriminates the BH4-upstream architecture from declared alternatives"
    false refl
    false refl

backpropBoundaryConsumed : Backprop.BlockedImplicationBackpropBoundary
backpropBoundaryConsumed = Backprop.canonicalBlockedImplicationBackpropBoundary

experimentalSelectionDoesNotPromoteClaim :
  Backprop.cheapestSelectedExperimentAutomaticallySupportsClaim
    backpropBoundaryConsumed
  ≡ false
experimentalSelectionDoesNotPromoteClaim = refl
