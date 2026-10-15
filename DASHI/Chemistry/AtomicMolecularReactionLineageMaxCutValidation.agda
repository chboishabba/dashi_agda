module DASHI.Chemistry.AtomicMolecularReactionLineageMaxCutValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Chemistry.AtomicMolecularReactionLineageHyperfabricExact as Lineage
import DASHI.Chemistry.ElectronBondTransportExact as Electron
import DASHI.Biology.AtomicMolecularBiologicalIncorporationHyperfabricExact as Bio
import DASHI.Biology.LeadCalciumAtomicLineageRegressionExact as PbCa
import DASHI.Biology.KitzerowBH4LineageRegressionExact as BH4
import DASHI.Biology.PrebioticCarbonAtomicLineageRegressionExact as Carbon

lineageSeparatesNuclearAndElectronTransport :
  Lineage.nuclearIdentityTransportIsDistinctFromElectronTransport
    Lineage.canonicalAtomicMolecularReactionLineageBoundary ≡ true
lineageSeparatesNuclearAndElectronTransport = refl

stoichiometryDoesNotDetermineElectronFlow :
  Electron.stoichiometricBalanceDeterminesElectronTransport
    Electron.canonicalElectronBondTransportBoundary ≡ false
stoichiometryDoesNotDetermineElectronFlow = refl

biologyRetainsUpstreamMaterialLineage :
  Bio.upstreamMaterialLineageRetained
    Bio.canonicalAtomicMolecularBiologicalIncorporationBoundary ≡ true
biologyRetainsUpstreamMaterialLineage = refl

pbCaMimicryDoesNotCollapseAtomicIdentity :
  PbCa.leadCalciumAtomicIdentityCollapsed
    PbCa.canonicalLeadCalciumAtomicLineageRegression ≡ false
pbCaMimicryDoesNotCollapseAtomicIdentity = refl

bh4SharedSpeciesDoesNotProveFluxAllocation :
  BH4.sharedBH4SpeciesProvesFluxReallocation
    BH4.canonicalKitzerowBH4LineageRegression ≡ false
bh4SharedSpeciesDoesNotProveFluxAllocation = refl

carbonSuitabilityDoesNotProveLife :
  Carbon.carbonLineageProvesAbiogenesis
    Carbon.canonicalPrebioticCarbonAtomicLineageRegression ≡ false
carbonSuitabilityDoesNotProveLife = refl

coarseObserverDoesNotEraseFineResidual :
  Lineage.coarseObserverEqualityImpliesFineIdentity
    Lineage.canonicalAtomicMolecularReactionLineageBoundary ≡ false
coarseObserverDoesNotEraseFineResidual = refl
