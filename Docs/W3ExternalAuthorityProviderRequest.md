# W3 External Authority Provider Request

Date: `2026-05-13`
Status: `provider request; candidate-pass-no-authority-token; non-promoting`
Owner: `Lane 6`

This packet asks an external W3 authority provider to accept, reject, or mark
insufficient the bounded W3 t43 evidence packet. It does not fabricate the
accepted evidence authority token locally.

## Requested Authority Identity

```text
DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken
```

## Candidate Evidence

| Field | Value |
|---|---|
| Frozen commit | `3205d746639568762c9e97adf4a3672c356bd491` |
| Candidate comparison artifact | `logs/research/w3_frozen_3205d74_t43_comparison_20260513.json` |
| Artifact SHA-256 | `92b61032c06cb4d00d22e00bf9e280b47806f9ebf18f012f5b82a41b0afae238` |
| Status | `candidate-pass-no-authority-token` |
| chi2/dof | `2.1565191176275618` |
| mean pred/data | `0.9941` |
| HEPData submission DOI | `10.17182/hepdata.115656.v1` |
| Ratio table | `t43` |
| Covariance table | `t44` |
| CMS analysis id | `CMS-SMP-20-003` |
| CMS paper DOI | `10.1140/epjc/s10052-023-11631-7` |

Canonical payloads staged for provider review:

| Payload | SHA-256 | Check |
|---|---|---|
| `logs/research/provider_inputs/hepdata_ins2079374/t43_canonical.json` | `5cfefe5a5a99c415f9225a3515383e8ce5e9a874861ff6c5fc08365871bfd340` | semantic match to local CSV: `18/18` |
| `logs/research/provider_inputs/hepdata_ins2079374/t44_canonical.json` | `2dfa2abe120981f1f8379d95c8d6e0362394c6f6c8fed01dd45fc76a3e2b660b` | covariance semantic match: `324/324` |

Source artifacts:

```text
Docs/W3AcceptedEvidenceAuthorityProviderResponse.md
Docs/W3AuthorityProviderResponseChecklist.md
DASHI/Physics/Closure/W3AcceptedAuthorityExternalReceiptRequestPack.agda
DASHI/Physics/Closure/W3AcceptedEmpiricalAuthorityGate.agda
DASHI/Physics/Closure/W3AcceptedEvidenceAuthorityTokenGovernanceObstruction.agda
scripts/data/hepdata/ins2079374_t43_t44.sha256
logs/research/provider_inputs/hepdata_ins2079374/checksums.txt
```

## Exact Receipt Shape Needed

An accepted W3 response must bind:

- provider identity, authority scope, contact or trace id, and timestamp;
- decision: `accepted`, `rejected`, or `insufficient`;
- HEPData table provenance for `t43` and `t44`;
- CMS-SMP-20-003 and paper provenance;
- frozen commit and comparison artifact digest;
- comparison law and covariance source;
- provider-equivalent immutable table checksum binding;
- non-collapse witness;
- exact statement that the response supplies
  `W3AcceptedEvidenceAuthorityToken`.

Rejected or insufficient responses must name the failed or missing field.

## Non-Promotion Boundary

```text
promotesW3 = false
authorityTokenConstructedHere = false
responseContainsAcceptedToken = false
```

The current candidate pass is evidence only. It does not promote W3, W4, W5,
W8, GR/QFT, or the paper.
