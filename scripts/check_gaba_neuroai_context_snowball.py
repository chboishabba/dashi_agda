#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
files = [
    ROOT / "DASHI/Biology/GABANeuroAIContextSnowballExact.agda",
    ROOT / "DASHI/Biology/GABANeuroAIContextSnowballRegression.agda",
    ROOT / "DASHI/Biology/GABANeuroAIContextParetoSnowballExact.agda",
    ROOT / "DASHI/Biology/GABANeuroAIContextParetoSnowballRegression.agda",
]
text = "\n".join(p.read_text(encoding="utf-8") for p in files)
required = [
    "metaTRIBEv2Receipt",
    "metaBrain2QwertyReceipt",
    "scholz2017ViralityReceipt",
    "chan2023SharingReceipt",
    "neuralink2026CalibrationReceipt",
    "canonicalDyadicObserverPluralityBridge",
    "canonicalLevinMultiscaleSignalAnchor",
    "peripheralCentralTransportNotAutomatic",
    "peripheralToCentralExperimentRequirement",
    "canonicalNeuroforecastExperimentRequirement",
    "canonicalAcquisitionFrontier",
    "crossParticipantDecoderTransferAcquisition",
    "companyEvidenceStaysCompanyEvidence",
    "numericScientificRankingInventedIsFalse",
    "10.1073/pnas.1615259114",
    "10.1073/pnas.2313175120",
    "FMRIConnectomeProxyGovernance",
    "AliceBrownThreadInquirySynthesisExact",
    "SIBioelectricNetworkAdapterExact",
    "SnowballPluralLensDiscoveryAdmissionExact",
]
missing = [x for x in required if x not in text]
if missing:
    raise SystemExit("missing required snowball surface: " + ", ".join(missing))
forbidden = [
    "metaViralityIsMetaAuthored :",
    "fMRIProvesMindReading :",
    "serumGABAEqualsBrainGABA :",
    "weeklyCalibrationUniversal :",
    "crossParticipantSuperiorityEstablishedIsTrue",
]
found = [x for x in forbidden if x in text]
if found:
    raise SystemExit("forbidden overclaim declaration found: " + ", ".join(found))
print("GABA neuro-AI context snowball source surface: OK")
