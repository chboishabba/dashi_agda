module DASHI.Biology.Protein.ProteinTemporalObligationProfilesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.Protein.ProteinTemporalObligationChainExact as Chain
import DASHI.Biology.Protein.TRPA1SingleResidueThermalAdaptationExact as TRPA1
import DASHI.Biology.Protein.TRPA1SourceAttributionEnvelopeExact as TRPA1Source
import DASHI.Biology.Protein.AdenylateKinaseSituatedProteinWitnessExact as AdK
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalExact as AdKEmpirical

------------------------------------------------------------------------
-- SOURCE-BOUNDED TEMPORAL PAYMENT PROFILES
--
-- These profiles do not add biological facts.  They record which parts of the
-- generic obligation chain are actually paid by the already-owned source-local
-- witnesses and which remain unpaid.  A local source payment cannot totalise a
-- protein's temporal state and cannot be transferred to another protein lane.
------------------------------------------------------------------------

record ProteinTemporalPaymentProfile : Set where
  constructor protein-temporal-payment-profile
  field
    profileLabel : String
    sourceRole : String

    encodedOrResidueCoordinatePaid : Bool
    translationContextPaid : Bool
    realisedProteinIdentityPaid : Bool
    conformationOrModificationContextPaid : Bool
    localMetabolicFluxPaid : Bool
    actionOrFunctionalReadoutPaid : Bool
    historyResidualPaid : Bool

    paymentReading : String
    attributionReading : String
open ProteinTemporalPaymentProfile public

trpa1TemporalPaymentProfile : ProteinTemporalPaymentProfile
trpa1TemporalPaymentProfile = protein-temporal-payment-profile
  "Feng-TRPA1 temporal payment profile"
  "Feng et al. 2026 owns the bounded pore-residue/thermal-gating and reported downstream pathway/intervention propositions; the temporal profile itself is DASHI synthesis"
  true
  false
  true
  false
  false
  true
  false
  "paid slice: TRPA1 identity + separating pore-residue coordinate + thermal-response/action readout. Not paid here: a generic translation witness, complete folding/modification state, metabolic flux state, or historical reconstruction"
  "DOI/PMID/PMCID/QID and other identifiers retain source identity/provenance only and do not create any missing temporal payment"

adkTemporalPaymentProfile : ProteinTemporalPaymentProfile
adkTemporalPaymentProfile = protein-temporal-payment-profile
  "adenylate-kinase temporal payment profile"
  "4AKE/1AKE and their primary structural literature own the bounded same-sequence/context-separated conformation observation; the generic temporal classification is DASHI synthesis"
  true
  false
  true
  true
  false
  false
  false
  "paid slice: primary-sequence identity + resolved protein identity/context + open/closed conformation separation in the finite empirical fixture. Not paid here: translation, local metabolic flux, complete functional action, or historical reconstruction"
  "PDB DOI/PDB ID/UniProt/QID retain object/source identity only; they do not manufacture conformation mechanism, kinetics, function or temporal history"

------------------------------------------------------------------------
-- Explicit donor surfaces, retained only to make the source ownership visible.
------------------------------------------------------------------------

trpa1ThermalGateDonor : TRPA1.SingleResidueThermalGateReceipt
trpa1ThermalGateDonor = TRPA1.feng2026ThermalGateReceipt

trpa1AttributionDonor = TRPA1Source.canonicalTRPA1SourceAttributionBoundary

adkContextConformationDonor = AdKEmpirical.canonicalAdenylateKinaseEmpiricalBoundary

adkSituatedDonor = AdK.canonicalAdKSituatedBoundary

chainBoundary : Chain.ProteinTemporalObligationBoundary
chainBoundary = Chain.canonicalProteinTemporalObligationBoundary

------------------------------------------------------------------------
-- WrongType / cross-source payment firewalls.
------------------------------------------------------------------------

data TRPA1ProfileCreatesCompleteTemporalChain : Set where
data AdKProfileCreatesCompleteTemporalChain : Set where
data CrossSourcePaymentTransfers : Set where
data ProteinIdentityCreatesTranslationReceipt : Set where
data StructuralIdentityCreatesMetabolicFlux : Set where
data ThermalReadoutCreatesHistory : Set where

trpa1ProfileDoesNotCreateCompleteTemporalChain :
  TRPA1ProfileCreatesCompleteTemporalChain → ⊥
trpa1ProfileDoesNotCreateCompleteTemporalChain ()

adkProfileDoesNotCreateCompleteTemporalChain :
  AdKProfileCreatesCompleteTemporalChain → ⊥
adkProfileDoesNotCreateCompleteTemporalChain ()

crossSourcePaymentDoesNotTransfer : CrossSourcePaymentTransfers → ⊥
crossSourcePaymentDoesNotTransfer ()

proteinIdentityDoesNotCreateTranslationReceipt :
  ProteinIdentityCreatesTranslationReceipt → ⊥
proteinIdentityDoesNotCreateTranslationReceipt ()

structuralIdentityDoesNotCreateMetabolicFlux :
  StructuralIdentityCreatesMetabolicFlux → ⊥
structuralIdentityDoesNotCreateMetabolicFlux ()

thermalReadoutDoesNotCreateHistory : ThermalReadoutCreatesHistory → ⊥
thermalReadoutDoesNotCreateHistory ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ProteinTemporalProfilesBoundary : Set where
  constructor protein-temporal-profiles-boundary
  field
    trpa1RetainsResidueCoordinatePayment : Bool
    trpa1RetainsThermalReadoutPayment : Bool
    trpa1TranslationPaid : Bool
    trpa1MetabolicFluxPaid : Bool
    trpa1HistoryPaid : Bool

    adkRetainsSequenceContextConformationPayment : Bool
    adkTranslationPaid : Bool
    adkMetabolicFluxPaid : Bool
    adkCompleteFunctionPaid : Bool
    adkHistoryPaid : Bool

    localPaymentTotalisesTemporalChain : Bool
    paymentTransfersAcrossProteinLanes : Bool
    identityMetadataPaysMissingTemporalLeg : Bool
open ProteinTemporalProfilesBoundary public

canonicalProteinTemporalProfilesBoundary : ProteinTemporalProfilesBoundary
canonicalProteinTemporalProfilesBoundary = protein-temporal-profiles-boundary
  true true false false false
  true false false false false
  false false false
