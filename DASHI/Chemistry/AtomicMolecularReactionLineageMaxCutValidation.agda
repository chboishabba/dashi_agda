module DASHI.Chemistry.AtomicMolecularReactionLineageMaxCutValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Chemistry.AtomicMolecularReactionLineageHyperfabricExact as Lineage
import DASHI.Chemistry.ElectronBondTransportExact as Electron
import DASHI.Chemistry.AtomicLineageBidiDiscriminatorExact as Bidi
import DASHI.Biology.AtomicMolecularBiologicalIncorporationHyperfabricExact as Bio
import DASHI.Biology.AtomicLineageTargetRecognitionBridgeExact as Recognition
import DASHI.Biology.LeadCalciumAtomicLineageRegressionExact as PbCa
import DASHI.Biology.KitzerowBH4LineageRegressionExact as BH4
import DASHI.Biology.PrebioticCarbonAtomicLineageRegressionExact as Carbon

nativeHyperformWeldsAreExplicit :
  Lineage.usesNativeCoarseFineHyperfabric
    Lineage.canonicalAtomicMolecularReactionLineageBoundary ≡ true
  × Lineage.usesNativeAdmissibleTransitionHyperfabric
    Lineage.canonicalAtomicMolecularReactionLineageBoundary ≡ true
nativeHyperformWeldsAreExplicit = refl , refl

atomMappingIsTyped369Lineage :
  Lineage.everyAtomicCarrierUses369AtomicIndex
    Lineage.canonicalAtomicMolecularReactionLineageBoundary ≡ true
  × Lineage.reactionAtomMappingIsTypedLineageNotString
    Lineage.canonicalAtomicMolecularReactionLineageBoundary ≡ true
atomMappingIsTyped369Lineage = refl , refl

lineageSeparatesNuclearAndElectronTransport :
  Lineage.nuclearIdentityTransportIsDistinctFromElectronTransport
    Lineage.canonicalAtomicMolecularReactionLineageBoundary ≡ true
lineageSeparatesNuclearAndElectronTransport = refl

fermionIdentityIsNotFabricated :
  Lineage.electronLineageMeansPersistentIndividualFermionIdentity
    Lineage.canonicalAtomicMolecularReactionLineageBoundary ≡ false
  × Lineage.electronEquivalentOrDensityTransportIsTrackable
    Lineage.canonicalAtomicMolecularReactionLineageBoundary ≡ true
fermionIdentityIsNotFabricated = refl , refl

molecularGeometryNeedsIndependentWitness :
  Lineage.molecularFormulaDeterminesBondGeometry
    Lineage.canonicalAtomicMolecularReactionLineageBoundary ≡ false
  × Lineage.geometryRequiresIndependentAssemblyOrMinimizerWitness
    Lineage.canonicalAtomicMolecularReactionLineageBoundary ≡ true
molecularGeometryNeedsIndependentWitness = refl , refl

stoichiometryDoesNotDetermineElectronFlow :
  Electron.stoichiometricBalanceDeterminesElectronTransport
    Electron.canonicalElectronBondTransportBoundary ≡ false
  × Electron.persistentIndividualElectronIdentityTracked
    Electron.canonicalElectronBondTransportBoundary ≡ false
  × Electron.electronEquivalentOrDensityFlowTrackable
    Electron.canonicalElectronBondTransportBoundary ≡ true
stoichiometryDoesNotDetermineElectronFlow = refl , (refl , refl)

biologyRetainsUpstreamMaterialLineage :
  Bio.upstreamMaterialLineageRetained
    Bio.canonicalAtomicMolecularBiologicalIncorporationBoundary ≡ true
biologyRetainsUpstreamMaterialLineage = refl

targetOverlapDoesNotCollapseFineLineage :
  Recognition.targetRelativeOverlapEqualsFineIdentity
    Recognition.canonicalAtomicLineageTargetRecognitionBoundary ≡ false
  × Recognition.newSeparatingCoordinateReopensDownstreamConsumers
    Recognition.canonicalAtomicLineageTargetRecognitionBoundary ≡ true
targetOverlapDoesNotCollapseFineLineage = refl , refl

bidiCandidateDoesNotCreateTruth :
  Bidi.candidatePerturbationCreatesWorldTruth
    Bidi.canonicalAtomicLineageBidiDiscriminatorBoundary ≡ false
  × Bidi.observedFineDifferenceReopensOnlyAffectedConsumers
    Bidi.canonicalAtomicLineageBidiDiscriminatorBoundary ≡ true
  × Bidi.interventionAuthorityIsIndependentObligation
    Bidi.canonicalAtomicLineageBidiDiscriminatorBoundary ≡ true
bidiCandidateDoesNotCreateTruth = refl , (refl , refl)

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
  × Lineage.fineResidualRemainsReopenable
    Lineage.canonicalAtomicMolecularReactionLineageBoundary ≡ true
coarseObserverDoesNotEraseFineResidual = refl , refl
