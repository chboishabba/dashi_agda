# Sprint 131 Final Claim Audit

- audit_id: `ym_sprint131_final_claim_audit`
- route_decision: `pass`
- fail_reasons: `0`

## Internal Claim State

| Claim | Internal true | Source sprint | Evidence paths |
| --- | --- | --- | --- |
| CC1 | closed | Sprint128 | DASHI/Physics/Closure/YMSprint128CompactnessAndLogGeneratorClosure.agda, DASHI/Physics/Closure/YMSprint128SymmetryAndGroupClosure.agda, DASHI/Physics/Closure/YMSprint128WilsonCarrierConstruction.agda |
| WC1 | closed | Sprint128 | DASHI/Physics/Closure/YMSprint128CompactnessAndLogGeneratorClosure.agda, DASHI/Physics/Closure/YMSprint128WilsonCarrierConstruction.agda |
| MC1 | closed | Sprint129 | DASHI/Physics/Closure/YMSprint129MoscoLiminfStrongResolventClosure.agda, DASHI/Physics/Closure/YMSprint129MoscoRecoveryNoPollutionClosure.agda, DASHI/Physics/Closure/YMSprint129MoscoSpectralRouteLedger.agda, DASHI/Physics/Closure/YMSprint129SpectralGapTransportClosure.agda |
| MC2 | closed | Sprint129 | DASHI/Physics/Closure/YMSprint129MoscoLiminfStrongResolventClosure.agda, DASHI/Physics/Closure/YMSprint129MoscoRecoveryNoPollutionClosure.agda, DASHI/Physics/Closure/YMSprint129MoscoSpectralRouteLedger.agda, DASHI/Physics/Closure/YMSprint129SpectralGapTransportClosure.agda |
| MC3 | closed | Sprint129 | DASHI/Physics/Closure/YMSprint129MoscoLiminfStrongResolventClosure.agda, DASHI/Physics/Closure/YMSprint129MoscoRecoveryNoPollutionClosure.agda, DASHI/Physics/Closure/YMSprint129MoscoSpectralRouteLedger.agda, DASHI/Physics/Closure/YMSprint129SpectralGapTransportClosure.agda |
| MC4 | closed | Sprint129 | DASHI/Physics/Closure/YMSprint129MoscoLiminfStrongResolventClosure.agda, DASHI/Physics/Closure/YMSprint129MoscoRecoveryNoPollutionClosure.agda, DASHI/Physics/Closure/YMSprint129MoscoSpectralRouteLedger.agda, DASHI/Physics/Closure/YMSprint129SpectralGapTransportClosure.agda |
| SC1 | closed | Sprint128 | DASHI/Physics/Closure/YMSprint128CompactnessAndLogGeneratorClosure.agda, DASHI/Physics/Closure/YMSprint128WilsonCarrierConstruction.agda |
| SC2 | closed | Sprint129 | DASHI/Physics/Closure/YMSprint129MoscoRecoveryNoPollutionClosure.agda, DASHI/Physics/Closure/YMSprint129MoscoSpectralRouteLedger.agda, DASHI/Physics/Closure/YMSprint129SpectralGapTransportClosure.agda |
| SC3 | closed | Sprint128 | DASHI/Physics/Closure/YMSprint128TransferLowerBoundClosure.agda, DASHI/Physics/Closure/YMSprint128WilsonCarrierConstruction.agda |
| SY1 | closed | Sprint128 | DASHI/Physics/Closure/YMSprint128CompactnessAndLogGeneratorClosure.agda, DASHI/Physics/Closure/YMSprint128SymmetryAndGroupClosure.agda, DASHI/Physics/Closure/YMSprint128WilsonCarrierConstruction.agda |
| GG1 | closed | Sprint128 | DASHI/Physics/Closure/YMSprint128CompactnessAndLogGeneratorClosure.agda, DASHI/Physics/Closure/YMSprint128SymmetryAndGroupClosure.agda, DASHI/Physics/Closure/YMSprint128WilsonCarrierConstruction.agda |
| OS1 | closed | Sprint130 | DASHI/Physics/Closure/YMSprint130FinalClayAssemblyLedger.agda, DASHI/Physics/Closure/YMSprint130OSToWightmanDistributionsClosure.agda, DASHI/Physics/Closure/YMSprint130PoincareSpectrumWightmanClosure.agda |
| FIN | closed | Sprint130 | DASHI/Physics/Closure/YMSprint130FinalClayAssemblyLedger.agda, DASHI/Physics/Closure/YMSprint130OSToWightmanDistributionsClosure.agda, DASHI/Physics/Closure/YMSprint130PoincareSpectrumWightmanClosure.agda |

## Boundary State

- external acceptance present: `false`
- external acceptance evidence: `[{"name": "externalAcceptanceTokenPresent", "path": "DASHI/Physics/Closure/YMSprint130FinalClayAssemblyLedger.agda", "value": false}]`
- clayYangMillsPromoted present: `false`
- clayYangMillsPromoted flags: `[{"name": "clayYangMillsPromoted", "path": "DASHI/Physics/Closure/YMSprint128WilsonCarrierConstruction.agda", "sprint": "Sprint128", "value": false}, {"name": "clayYangMillsPromoted", "path": "DASHI/Physics/Closure/YMSprint128CompactnessAndLogGeneratorClosure.agda", "sprint": "Sprint128", "value": false}, {"name": "clayYangMillsPromoted", "path": "DASHI/Physics/Closure/YMSprint128TransferLowerBoundClosure.agda", "sprint": "Sprint128", "value": false}, {"name": "clayYangMillsPromoted", "path": "DASHI/Physics/Closure/YMSprint128SymmetryAndGroupClosure.agda", "sprint": "Sprint128", "value": false}, {"name": "clayYangMillsPromoted", "path": "DASHI/Physics/Closure/YMSprint129MoscoLiminfStrongResolventClosure.agda", "sprint": "Sprint129", "value": false}, {"name": "clayYangMillsPromoted", "path": "DASHI/Physics/Closure/YMSprint129MoscoRecoveryNoPollutionClosure.agda", "sprint": "Sprint129", "value": false}, {"name": "clayYangMillsPromoted", "path": "DASHI/Physics/Closure/YMSprint129SpectralGapTransportClosure.agda", "sprint": "Sprint129", "value": false}, {"name": "clayYangMillsPromoted", "path": "DASHI/Physics/Closure/YMSprint129MoscoSpectralRouteLedger.agda", "sprint": "Sprint129", "value": false}, {"name": "clayYangMillsPromoted", "path": "DASHI/Physics/Closure/YMSprint130FinalClayAssemblyLedger.agda", "sprint": "Sprint130", "value": false}, {"name": "clayYangMillsPromoted", "path": "DASHI/Physics/Closure/YMSprint130OSToWightmanDistributionsClosure.agda", "sprint": "Sprint130", "value": false}, {"name": "clayYangMillsPromoted", "path": "DASHI/Physics/Closure/YMSprint130PoincareSpectrumWightmanClosure.agda", "sprint": "Sprint130", "value": false}]`

## Fail-Closed Scan

- Sprint128: 4 scanned surfaces
  - `DASHI/Physics/Closure/YMSprint128CompactnessAndLogGeneratorClosure.agda`
  - `DASHI/Physics/Closure/YMSprint128SymmetryAndGroupClosure.agda`
  - `DASHI/Physics/Closure/YMSprint128TransferLowerBoundClosure.agda`
  - `DASHI/Physics/Closure/YMSprint128WilsonCarrierConstruction.agda`
- Sprint129: 4 scanned surfaces
  - `DASHI/Physics/Closure/YMSprint129MoscoLiminfStrongResolventClosure.agda`
  - `DASHI/Physics/Closure/YMSprint129MoscoRecoveryNoPollutionClosure.agda`
  - `DASHI/Physics/Closure/YMSprint129MoscoSpectralRouteLedger.agda`
  - `DASHI/Physics/Closure/YMSprint129SpectralGapTransportClosure.agda`
- Sprint130: 3 scanned surfaces
  - `DASHI/Physics/Closure/YMSprint130FinalClayAssemblyLedger.agda`
  - `DASHI/Physics/Closure/YMSprint130OSToWightmanDistributionsClosure.agda`
  - `DASHI/Physics/Closure/YMSprint130PoincareSpectrumWightmanClosure.agda`

## Fail Reasons

- none
