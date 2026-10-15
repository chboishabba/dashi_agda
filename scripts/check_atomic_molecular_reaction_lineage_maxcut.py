#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

required = [
    "DASHI/Chemistry/AtomicMolecularReactionLineageHyperfabricExact.agda",
    "DASHI/Chemistry/ElectronBondTransportExact.agda",
    "DASHI/Biology/AtomicMolecularBiologicalIncorporationHyperfabricExact.agda",
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
    "TransitionKernel",
    "ConsumerRelativeCoarseGrainingBidiExact",
    "AtomicLineage",
    "ElectronLineage",
    "MolecularLineageState",
    "ReactionLineageTransport",
    "nuclearIdentityTransportIsDistinctFromElectronTransport",
    "coarseObserverEqualityImpliesFineIdentity",
]:
    assert needle in core, f"core missing {needle}"

electron = (ROOT / required[1]).read_text()
for needle in [
    "ElectronTransferReceipt",
    "BondChangeReceipt",
    "stoichiometricBalanceDeterminesElectronTransport",
    "chargeBalanceDeterminesBondChange",
]:
    assert needle in electron, f"electron/bond owner missing {needle}"

bio = (ROOT / required[2]).read_text()
for needle in [
    "AtomicPeriodicTable369ProteinDNA3DAdapterExact",
    "CellStateAttractor",
    "ProblemSpaceAgency",
    "upstreamMaterialLineageRetained",
]:
    assert needle in bio, f"biology incorporation missing {needle}"

pbca = (ROOT / required[3]).read_text()
for needle in ["IonicMimicryGeometryExact", "calciumII", "leadII", "leadCalciumAtomicIdentityCollapsed"]:
    assert needle in pbca, f"Pb/Ca regression missing {needle}"

bh4 = (ROOT / required[4]).read_text()
for needle in [
    "KitzerowBH4ReactionChemistryExact",
    "KitzerowBH4SynthesisRegenerationExact",
    "sharedBH4SpeciesProvesFluxReallocation",
    "electronRedoxLineageRetained",
]:
    assert needle in bh4, f"BH4 regression missing {needle}"

carbon = (ROOT / required[5]).read_text()
for needle in [
    "CarbonChemicalSuitabilityLifeBoundaryExact",
    "PrebioticChemistryLifeInevitabilityBidiExact",
    "ProblemSpaceAgency",
    "carbonLineageProvesAbiogenesis",
]:
    assert needle in carbon, f"carbon regression missing {needle}"

print("atomic-molecular-reaction lineage max-cut static contract: PASS")
