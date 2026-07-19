module DASHI.Biology.Levin.ElectrochemicalBodyConsortium where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.CellPhysicalOrganisationCore as Cell
import DASHI.Biology.Levin.MitochondrialBioenergeticAdapter as Mito
import DASHI.Biology.Levin.BioelectricChemistryWaveAdapter as Electrochem
import DASHI.Biology.Levin.MultiscaleIdentityDissociation as Identity

record ConsortiumLayer : Set where
  field
    endogenousHostCells : Bool
    endosymbioticOrganelles : Bool
    residentMicrobiota : Bool
    extracellularMatrix : Bool
    circulatingSignals : Bool
    neuralAndNonneuralElectricalNetworks : Bool
    layerBoundaryExplicit : Bool

record ElectrochemicalBodyConsortiumBoundary : Set where
  field
    cellOrganisation : Cell.CellPhysicalOrganisationCore
    mitochondrialLane : Mito.MitochondrialBioenergeticAdapter
    electrochemicalLane : Electrochem.BioelectricChemistryWaveAdapter
    identityBoundaryType : Set
    bodyNotSingleCentralController : Bool
    noSubsystemOwnsWholeOrganismByDefinition : Bool
    organismalIdentityIsScaleIndexed : Bool
    materialMembershipNotEquivalentToSelfhood : Bool
    microbiotaInfluenceNotMicrobialSovereignty : Bool
    interpretation : String

canonicalElectrochemicalBodyConsortiumBoundary : ElectrochemicalBodyConsortiumBoundary
canonicalElectrochemicalBodyConsortiumBoundary = record
  { cellOrganisation = Cell.canonicalCellPhysicalOrganisationCore
  ; mitochondrialLane = Mito.canonicalMitochondrialBioenergeticAdapter
  ; electrochemicalLane = Electrochem.canonicalBioelectricChemistryWaveAdapter
  ; identityBoundaryType = Identity.MultiscaleIdentityDissociationBoundary
  ; bodyNotSingleCentralController = true
  ; noSubsystemOwnsWholeOrganismByDefinition = true
  ; organismalIdentityIsScaleIndexed = true
  ; materialMembershipNotEquivalentToSelfhood = true
  ; microbiotaInfluenceNotMicrobialSovereignty = true
  ; interpretation = "The embodied organism is a nested electrochemical consortium of host cells, endosymbiotic organelles, extracellular structures and resident microorganisms; causal participation and organismal identity remain scale-indexed rather than assigned to one privileged controller"
  }
