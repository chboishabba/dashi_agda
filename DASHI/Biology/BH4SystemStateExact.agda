module DASHI.Biology.BH4SystemStateExact where

open import DASHI.Core.Prelude

import DASHI.Biology.ExternalBiologyEvidenceCore as External
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- SHARED BH4 SYSTEM STATE
--
-- This owner upgrades the coarse atlas node `bh4Availability` into a state
-- carrier that can be shared by synthesis, recycling, oxidation and multiple
-- enzyme consumers.  It is intentionally quantitative only at the interface:
-- database annotations may identify participants/reactions, but they do not
-- manufacture measured compartmental amounts or fluxes.
------------------------------------------------------------------------

data Compartment : Set where
  cytosol : Compartment
  mitochondrion : Compartment
  plasmaMembrane : Compartment
  endoplasmicReticulum : Compartment
  extracellular : Compartment
  neuronal : Compartment
  endothelial : Compartment
  immuneCell : Compartment
  gutPeripheral : Compartment
  namedCompartment : String → Compartment

Amount : Set
Amount = Nat

Flux : Set
Flux = Nat

record BH4PoolState : Set where
  constructor bh4PoolState
  field
    compartment : Compartment
    bh4Amount : Amount
    bh2Amount : Amount
    synthesisFlux : Flux
    regenerationFlux : Flux
    oxidationFlux : Flux
    measurementReference : String
    measured : Bool

open BH4PoolState public

data EnzymeActivityState : Set where
  active : EnzymeActivityState
  reducedActivity : EnzymeActivityState
  inactive : EnzymeActivityState
  activityUnresolved : EnzymeActivityState

record EnzymeDemand : Set where
  constructor enzymeDemand
  field
    protein : External.ProteinRef
    compartment : Compartment
    bh4DemandFlux : Flux
    activityState : EnzymeActivityState
    demandReference : String
    demandMeasured : Bool

open EnzymeDemand public

record BH4SystemState : Set where
  constructor bh4SystemState
  field
    stateId : String
    pools : List BH4PoolState
    demands : List EnzymeDemand
    transportReference : String
    redoxReference : String
    samePhysicalStateReference : String
    compartmentTransportMeasured : Bool
    wholeSystemFluxMeasured : Bool

open BH4SystemState public

------------------------------------------------------------------------
-- Conservation-style payment interface.
--
-- The exact biological model may later refine these totals into concentrations,
-- rates, stoichiometric coefficients and compartment-specific transport.  The
-- current theorem surface only requires that any promoted allocator model pay
-- a shared balance equation rather than juxtaposing isolated reaction nodes.
------------------------------------------------------------------------

record FluxBalanceWitness (state : BH4SystemState) : Set where
  constructor fluxBalanceWitness
  field
    totalSynthesisFlux : Flux
    totalRegenerationFlux : Flux
    totalConsumerDemand : Flux
    totalOxidativeLoss : Flux
    storageIncrease : Flux
    balanceEquation :
      totalSynthesisFlux + totalRegenerationFlux
      ≡ totalConsumerDemand + totalOxidativeLoss + storageIncrease
    sameStateReference : String
    measuredOrDerivedReference : String

open FluxBalanceWitness public

data WholeSystemFluxResidual : Set where
  missingCompartmentAmounts : WholeSystemFluxResidual
  missingConsumerFluxes : WholeSystemFluxResidual
  missingTransportFluxes : WholeSystemFluxResidual
  missingOxidationFlux : WholeSystemFluxResidual
  missingSameStateMeasurement : WholeSystemFluxResidual
  missingBalanceEquationPayment : WholeSystemFluxResidual

record BH4SystemPayment : Set where
  constructor bh4SystemPayment
  field
    state : BH4SystemState
    fluxWitnessReference : String
    participantIdentityPaid : Bool
    reactionIdentityPaid : Bool
    compartmentStatePaid : Bool
    consumerFluxPaid : Bool
    transportPaid : Bool
    causalAllocatorPaid : Bool

open BH4SystemPayment public

------------------------------------------------------------------------
-- Promotion boundaries.
------------------------------------------------------------------------

record BH4SystemBoundary : Set where
  constructor bh4-system-boundary
  field
    proteinIdentityCreatesMeasuredPoolState : Bool
    proteinIdentityCreatesMeasuredPoolStateIsFalse :
      proteinIdentityCreatesMeasuredPoolState ≡ false
    reactionAnnotationPaysWholeFluxBalance : Bool
    reactionAnnotationPaysWholeFluxBalanceIsFalse :
      reactionAnnotationPaysWholeFluxBalance ≡ false
    cofactorRequirementProvesCompetitionBetweenConsumers : Bool
    cofactorRequirementProvesCompetitionBetweenConsumersIsFalse :
      cofactorRequirementProvesCompetitionBetweenConsumers ≡ false
    oneCompartmentMeasurementGlobalizesToAllCompartments : Bool
    oneCompartmentMeasurementGlobalizesToAllCompartmentsIsFalse :
      oneCompartmentMeasurementGlobalizesToAllCompartments ≡ false
    balanceEquationAloneProvesDiseaseMechanism : Bool
    balanceEquationAloneProvesDiseaseMechanismIsFalse :
      balanceEquationAloneProvesDiseaseMechanism ≡ false

canonicalBH4SystemBoundary : BH4SystemBoundary
canonicalBH4SystemBoundary =
  bh4-system-boundary false refl false refl false refl false refl false refl

canonicalBH4SystemReceipt : Receipt.GenericReceipt
canonicalBH4SystemReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 shared system state"
    "DASHI.Biology.BH4SystemStateExact"
    "BH4PoolState / EnzymeDemand / BH4SystemState / FluxBalanceWitness"
    "requires one shared compartment/redox/flux carrier for BH4 synthesis, regeneration, oxidation and simultaneous enzyme demand"
    "protein/reaction annotations do not create measured pools, competition, transport, whole-system balance, allocator causality or disease mechanism"
    "agda -i . DASHI/Biology/BH4SystemStateExact.agda"
