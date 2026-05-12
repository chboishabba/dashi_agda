# W3 Authority Provider Response Checklist

Date: 2026-05-13
Owner: Curie-W3
Status: provider-response checklist plus local absence record; candidate-only; non-promoting

This checklist asks an external W3 authority provider for a bounded response on
the W3 t43 evidence packet. The response must not promote any downstream gate
and must not fabricate a local token.

## Required Response

Return exactly one decision:

- `accept`
- `reject`
- `insufficient`

The response must include every checklist item below.

| Item | Required response |
|---|---|
| Authority identity/role | Provider identity, role, authority scope, contact or trace id, and response timestamp |
| Data source accepted | `accept`, `reject`, or `insufficient` for the cited public data source |
| t43 observable accepted | `accept`, `reject`, or `insufficient` for the bounded below-Z `t43` observable |
| Comparison law accepted | `accept`, `reject`, or `insufficient` for the stated t43 comparison law |
| Non-collapse witness accepted | `accept`, `reject`, or `insufficient` for the listed non-collapse witness |
| Provenance packet accepted | `accept`, `reject`, or `insufficient` for the DOI, CMS-SMP-20-003, commit, artifact, and digest provenance packet |
| `tableChecksumBound` | `accept`, `reject`, or `insufficient`; must bind authoritative HEPData `t43` and `t44` table payloads, or provider-equivalent immutable table records, to the cited DOI/table provenance |
| Token status | `accepted external token supplied`, `rejected`, or `insufficient`; no local token may be constructed |
| Rejection reason if any | Required for `reject` or `insufficient`; name the failed field, missing field, or authority rule |

## Candidate Artifact Binding

The candidate comparison now under review is:

| Field | Value |
|---|---|
| Artifact | `logs/research/w3_frozen_3205d74_t43_comparison_20260513.json` |
| Artifact SHA-256 | `92b61032c06cb4d00d22e00bf9e280b47806f9ebf18f012f5b82a41b0afae238` |
| Status | `candidate-pass-no-authority-token` |
| Chi2/dof | `2.1565191176275618` |
| HEPData dataset DOI | `10.17182/hepdata.104472` |
| HEPData submission DOI | `10.17182/hepdata.115656.v1` |
| CMS paper DOI | `10.1140/epjc/s10052-023-11631-7` |
| CMS analysis id | `CMS-SMP-20-003` |
| Ratio table | `t43` |
| Covariance table | `t44` |
| Local t19 CSV SHA-256 | `1a1d280da645f4c55aba73aabf1b398a3fd9614532c363d972018f194b653677` |
| Local t20 CSV SHA-256 | `fa4b694211862d4b07b761d0dab77c8fe1016d2ccd5015dc6f7bc3272c34201a` |
| Local t43 CSV SHA-256 | `0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b` |
| Local t44 CSV SHA-256 | `3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b` |
| Local t43/t44 manifest | `scripts/data/hepdata/ins2079374_t43_t44.sha256` |
| Local checksum receipt | `DASHI/Physics/Closure/HEPDataRatioTableArtifactReceipt.agda` |
| Local header check | t43 and t44 CSVs have first-line table DOI headers matching `10.17182/hepdata.115656.v1/t43` and `10.17182/hepdata.115656.v1/t44` |

The local CSV checksums are candidate-input checks only. They do not discharge
`tableChecksumBound` unless the provider explicitly accepts them as matching
the authoritative HEPData table payloads or supplies an equivalent immutable
table binding.

Local checksum route status:

```text
localHEPDataArtifactReceiptBoundAwaitingProviderCanonicalBinding
providerCanonicalT43ChecksumOrEquivalent = missing
providerCanonicalT44ChecksumOrEquivalent = missing
tableChecksumBound = false
```

## Source And Boundary

The bounded source packet under review is the W3 accepted-evidence authority
handoff for:

```text
DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken
```

The provider response may accept, reject, or mark insufficient only this W3
t43 authority-token boundary. It does not certify W4/W5 calibration, GRQFT
promotion, W8 origin promotion, broad empirical adequacy, or complete physics
unification.

## Forbidden Interpretations

- Do not treat this checklist as promotion.
- Do not infer a token from a partial response.
- Do not fabricate `W3AcceptedEvidenceAuthorityToken` locally.
- Do not treat `insufficient` as acceptance or rejection.
- Do not use a rejection reason unless it names the exact failed field,
  missing field, or authority rule.

## Local Provider Response Inspection

Inspection date: 2026-05-06

Local W3 authority/provider-response files inspected:

- `Docs/W3AcceptedEvidenceAuthorityTokenSubmission.md`
- `Docs/W3AcceptedEvidenceAuthorityProviderResponse.md`
- `DASHI/Physics/Closure/W3AcceptedEvidenceAuthorityTokenReceipt.agda`
- `DASHI/Physics/Closure/W3AcceptedEmpiricalAuthorityGate.agda`
- `DASHI/Physics/Closure/W3AcceptedAuthorityExternalReceiptRequestPack.agda`

Result: no real accepted, rejected, or insufficient W3 authority-provider
response exists locally. The local Markdown provider response is still a
template/status artifact with:

```text
Status: awaiting provider response; non-promoting
authorityTokenConstructedHere = false
responseContainsAcceptedToken = false
exactRemainingGap = W3AcceptedEvidenceAuthorityToken
exactRemainingChecksumGap = tableChecksumBound
```

The typed Agda receipt surface also keeps the authority token constructorless
and requires an external token before any
`W3AcceptedEvidenceAuthorityTokenReceipt` can be inhabited.

Supported token fields from a real provider response: none yet, because no
provider identity, response timestamp, decision, accepted-token attestation,
or rejection/insufficiency reason is present locally.

Exact external blocker:

```text
missing accepted external W3AcceptedEvidenceAuthorityToken, with tableChecksumBound still absent
```

Exact external checksum step:

```text
Return providerCanonicalT43ChecksumOrEquivalent and
providerCanonicalT44ChecksumOrEquivalent, then explicitly set
tableChecksumBound=true for the cited HEPData DOI/table provenance, or mark the
field insufficient/rejected with the exact failed rule.
```
