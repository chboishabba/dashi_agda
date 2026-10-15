#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

required = [
    "DASHI/Chemistry/AtomicMolecularReactionLineageHyperfabricExact.agda",
    "DASHI/Chemistry/ElectronBondTransportExact.agda",
    "DASHI/Biology/AtomicMolecularBiologicalIncorporationHyperfabricExact.agda",
    "DASHI/Biology/AtomicLineageTargetRecognitionBridgeExact.agda",
    "DASHI/Biology/LeadCalciumAtomicLineageRegressionExact.agda",
    "DASHI/Biology/KitzerowBH4LineageRegressionExact.agda",
    "DASHI/Biology/PrebioticCarbonAtomicLineageRegressionExact.agda",
    "DASHI/Chemistry/AtomicMolecularReactionLineageEverything.agda",
    "DASHI/Chemistry/AtomicMolecularReactionLineageMaxCutValidation.agda",
]
for rel in required:
    assert (ROOT / rel).exists(), f"missing {rel}"

core = (ROOT / required[0]).read_text()
for needle in [
    "AtomicPeriodicTable369GenerativeExact",
    "AtomicPeriodicTable369ChemistryHyperfibreBridgeExact",
    "MolecularAssemblyBoundary",
    "MolecularConstrainedMinimizerBridge",
    "TransitionKernel",
    "ConsumerRelativeCoarseGrainingBidiExact",
    "AtomicLineage",
    "ElectronLineage",
    "MolecularLineageState",
    "MolecularGeometryLineageReceipt",
    "ReactionLineageTransport",
    "nuclearIdentityTransportIsDistinctFromElectronTransport",
    "electronLineageMeansPersistentIndividualFermionIdentity",
    "electronEquivalentOrDensityTransportIsTrackable",
    "geometryRequiresIndependentAssemblyOrMinimizerWitness",
    "coarseObserverEqualityImpliesFineIdentity",
]:
    assert needle in core, f"core missing {needle}"

electron = (ROOT / required[1]).read_text()
for needle in [
    "ElectronTransferReceipt",
    "BondChangeReceipt",
    "stoichiometricBalanceDeterminesElectronTransport",
    "chargeBalanceDeterminesBondChange",
    "persistentIndividualElectronIdentityTracked",
    "electronEquivalentOrDensityFlowTrackable",
]:
    assert needle in electron, f"electron/bond owner missing {needle}"

bio = (ROOT / required[2]).read_text()
for needle in [
    "AtomicPeriodicTable369ProteinDNA3DAdapterExact",
    "CellStateAttractor",
    "ProblemSpaceAgency",
    "upstreamMaterialLineageRetained",
    "sameAtomInventoryImpliesSameBiologicalCarrier",
]:
    assert needle in bio, f"biology incorporation missing {needle}"

probe = (ROOT / required[3]).read_text()
for needle in [
    "TargetRelativeRecognitionFibreExact",
    "AtomicSubstitutionProbe",
    "MolecularSubstitutionProbe",
    "targetRelativeOverlapEqualsFineIdentity",
]:
    assert needle in probe, f"recognition bridge missing {needle}"

pbca = (ROOT / required[4]).read_text()
for needle in [
    "IonicMimicryGeometryExact",
    "TargetRelativeRecognitionFibreExact",
    "Atomic369.atomicIndex 20 20 18",
    "Atomic369.atomicIndex 82 126 80",
    "canonicalPbCaAtomicSubstitutionProbe",
    "leadCalciumAtomicIdentityCollapsed",
]:
    assert needle in pbca, f"Pb/Ca regression missing {needle}"

bh4 = (ROOT / required[5]).read_text()
for needle in [
    "KitzerowBH4ReactionChemistryExact",
    "KitzerowBH4SynthesisRegenerationExact",
    "sharedBH4SpeciesProvesFluxReallocation",
    "electronRedoxLineageRetained",
    "sprElectronTransfer",
    "dhprElectronTransfer",
]:
    assert needle in bh4, f"BH4 regression missing {needle}"

carbon = (ROOT / required[6]).read_text()
for needle in [
    "CarbonChemicalSuitabilityLifeBoundaryExact",
    "PrebioticChemistryLifeInevitabilityBidiExact",
    "ProblemSpaceAgency",
    "Atomic369.atomicIndex 6 6 6",
    "carbonLineageProvesAbiogenesis",
    "maintainedNonequilibriumProvesAgency",
]:
    assert needle in carbon, f"carbon regression missing {needle}"

rollup = (ROOT / required[7]).read_text()
for needle in [
    "AtomicMolecularReactionLineageHyperfabricExact",
    "AtomicLineageTargetRecognitionBridgeExact",
    "LeadCalciumAtomicLineageRegressionExact",
    "KitzerowBH4LineageRegressionExact",
    "PrebioticCarbonAtomicLineageRegressionExact",
]:
    assert needle in rollup, f"rollup missing {needle}"

print("atomic-molecular-reaction lineage max-cut static contract: PASS")
