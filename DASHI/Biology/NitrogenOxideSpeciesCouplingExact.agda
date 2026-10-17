module DASHI.Biology.NitrogenOxideSpeciesCouplingExact where

open import DASHI.Core.Prelude

import DASHI.Biology.ExternalBiologyEvidenceCore as External
import DASHI.Biology.BH4SystemStateExact as BH4
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- NITROGEN-OXIDE SPECIES / NOS COUPLING
--
-- BH4-dependent nitric-oxide synthase chemistry concerns nitric oxide (NO).
-- Nitrous oxide (N2O; recreational "nangs") is a distinct molecular species.
-- This owner makes the distinction structural so a coarse nitrogen-oxide label
-- cannot silently transport evidence between them.
------------------------------------------------------------------------

data NitrogenOxideSpecies : Set where
  nitricOxide : NitrogenOxideSpecies
  nitrousOxide : NitrogenOxideSpecies
  superoxide : NitrogenOxideSpecies
  peroxynitrite : NitrogenOxideSpecies
  namedNitrogenOxideSpecies : String → NitrogenOxideSpecies

nitricOxideNotNitrousOxide : nitricOxide ≡ nitrousOxide → ⊥
nitricOxideNotNitrousOxide ()

data NOSIsoform : Set where
  neuronalNOS : NOSIsoform
  inducibleNOS : NOSIsoform
  endothelialNOS : NOSIsoform
  namedNOSIsoform : String → NOSIsoform

data NOSCouplingState : Set where
  coupled : NOSCouplingState
  partiallyUncoupled : NOSCouplingState
  uncoupled : NOSCouplingState
  couplingUnresolved : NOSCouplingState

record NOSBiochemicalState : Set where
  constructor nosBiochemicalState
  field
    isoform : NOSIsoform
    protein : External.ProteinRef
    compartment : BH4.Compartment
    bh4StateReference : String
    bh4ToBh2Reference : String
    arginineReference : String
    redoxReference : String
    oxygenReference : String
    couplingState : NOSCouplingState
    productSpecies : NitrogenOxideSpecies
    measurementReference : String
    couplingMeasured : Bool

open NOSBiochemicalState public

record NOSCouplingTransitionWitness : Set where
  constructor nos-coupling-transition-witness
  field
    beforeReference : String
    afterReference : String
    sameProteinIsoform : Bool
    sameCompartment : Bool
    bh4OrRedoxPerturbationReference : String
    beforeState : NOSCouplingState
    afterState : NOSCouplingState
    productShiftReference : String
    directOrInterventionalEvidenceReference : String
    transitionPaid : Bool

open NOSCouplingTransitionWitness public

data NOSCouplingResidual : Set where
  missingBH4BH2State : NOSCouplingResidual
  missingSubstrateState : NOSCouplingResidual
  missingRedoxState : NOSCouplingResidual
  missingCompartmentIdentity : NOSCouplingResidual
  missingProductMeasurement : NOSCouplingResidual
  missingTransitionIntervention : NOSCouplingResidual

record NOSCouplingBoundary : Set where
  constructor nos-coupling-boundary
  field
    proteinPresenceEstablishesUncoupling : Bool
    proteinPresenceEstablishesUncouplingIsFalse :
      proteinPresenceEstablishesUncoupling ≡ false
    bh4RequirementAloneEstablishesUncoupling : Bool
    bh4RequirementAloneEstablishesUncouplingIsFalse :
      bh4RequirementAloneEstablishesUncoupling ≡ false
    nitricOxideIsNitrousOxide : Bool
    nitricOxideIsNitrousOxideIsFalse : nitricOxideIsNitrousOxide ≡ false
    nitrousOxideIsCanonicalNOSProduct : Bool
    nitrousOxideIsCanonicalNOSProductIsFalse :
      nitrousOxideIsCanonicalNOSProduct ≡ false
    oneNOSIsoformMeasurementGlobalizesToAllIsoforms : Bool
    oneNOSIsoformMeasurementGlobalizesToAllIsoformsIsFalse :
      oneNOSIsoformMeasurementGlobalizesToAllIsoforms ≡ false

canonicalNOSCouplingBoundary : NOSCouplingBoundary
canonicalNOSCouplingBoundary =
  nos-coupling-boundary false refl false refl false refl false refl false refl

canonicalNitrogenOxideSpeciesCouplingReceipt : Receipt.GenericReceipt
canonicalNitrogenOxideSpeciesCouplingReceipt =
  Receipt.mkNonPromotingReceipt
    "nitrogen-oxide species and NOS coupling"
    "DASHI.Biology.NitrogenOxideSpeciesCouplingExact"
    "NitrogenOxideSpecies / NOSBiochemicalState / NOSCouplingTransitionWitness"
    "separates NO from N2O and requires BH4/BH2, substrate, redox, compartment and product-state payment before NOS coupling transitions are promoted"
    "NOS protein presence or BH4 requirement does not establish uncoupling; N2O is not definitionally NO or the canonical NOS product"
    "agda -i . DASHI/Biology/NitrogenOxideSpeciesCouplingExact.agda"
