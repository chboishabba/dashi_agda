module DASHI.Biology.Levin.EndosymbioticOrganelleAgencyBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.MitochondrialBioenergeticAdapter as Mito
import DASHI.Biology.Levin.MultiscaleIdentityDissociation as Identity
import DASHI.Biology.Levin.SubstrateIndependentAgency as Agency

record EndosymbioticIntegrationWitness : Set where
  field
    bacterialAncestrySupported : Bool
    genomeReductionObserved : Bool
    hostNuclearGeneTransferObserved : Bool
    proteinImportDependencyObserved : Bool
    metabolicReciprocityObserved : Bool
    reproductiveCouplingObserved : Bool
    conflictSuppressionObserved : Bool
    residualOrganelleAutonomyMeasured : Bool

record EndosymbioticOrganelleAgencyBoundary : Set where
  field
    mitochondrialLane : Mito.MitochondrialBioenergeticAdapter
    identityBoundary : Identity.MultiscaleIdentityDissociationBoundary
    agencyBoundary : Agency.SubstrateIndependentAgencyBoundary
    organelleHasEvolutionaryIndividualityHistory : Bool
    presentOrganelleNotFreeLivingAgent : Bool
    localHomeostasisNotIndependentGoalOwnership : Bool
    hostAndOrganelleInterestsMayPartiallyAlign : Bool
    conflictAndCooperationBothAdmissible : Bool
    organismNotMerelyVehicleForOrganelle : Bool
    interpretation : String

canonicalEndosymbioticOrganelleAgencyBoundary : EndosymbioticOrganelleAgencyBoundary
canonicalEndosymbioticOrganelleAgencyBoundary = record
  { mitochondrialLane = Mito.canonicalMitochondrialBioenergeticAdapter
  ; identityBoundary = Identity.canonicalMultiscaleIdentityDissociationBoundary
  ; agencyBoundary = Agency.canonicalSubstrateIndependentAgencyBoundary
  ; organelleHasEvolutionaryIndividualityHistory = true
  ; presentOrganelleNotFreeLivingAgent = true
  ; localHomeostasisNotIndependentGoalOwnership = true
  ; hostAndOrganelleInterestsMayPartiallyAlign = true
  ; conflictAndCooperationBothAdmissible = true
  ; organismNotMerelyVehicleForOrganelle = true
  ; interpretation = "Mitochondria descend from bacterial endosymbionts and retain local regulatory capacities, yet extensive genomic, metabolic and reproductive integration prevents equating evolutionary ancestry with present independent agency or treating the organism as merely an organelle vehicle"
  }
