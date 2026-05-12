# W3 Accepted Evidence Authority Provider Response

Date: `2026-05-13`
Status: `awaiting provider response; candidate-only; non-promoting`
Owner: `Curie-W3`

This packet is the human-facing response form for the final W3 accepted evidence
authority token handoff. It consumes the request-only packet in:

```text
DASHI/Physics/Closure/W3AcceptedEvidenceAuthorityTokenIntakeRequest.agda
```

It does not create or imply a local
`DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken`.
That token remains constructorless in the repo and must come from an accepted
external authority.

## Required Provider Response

The provider response must include every field below.

| Field | Required content |
|---|---|
| Provider identity | Organization/person/system, authority scope, contact or trace id, and response timestamp |
| Evidence authority decision | One of `accepted`, `rejected`, or `insufficient` |
| HEPData DOI | `10.17182/hepdata.104472` plus submission/table refs `10.17182/hepdata.115656.v1`, `t43`, and `t44` |
| CMS paper DOI | `10.1140/epjc/s10052-023-11631-7` |
| CMS analysis id | `CMS-SMP-20-003` |
| Frozen commit | `3205d746639568762c9e97adf4a3672c356bd491` |
| Candidate comparison artifact | `logs/research/w3_frozen_3205d74_t43_comparison_20260513.json`, SHA-256 `92b61032c06cb4d00d22e00bf9e280b47806f9ebf18f012f5b82a41b0afae238`, status `candidate-pass-no-authority-token`, chi2/dof `2.1565191176275618` |
| Local CSV checksums | `t19` `1a1d280da645f4c55aba73aabf1b398a3fd9614532c363d972018f194b653677`; `t20` `fa4b694211862d4b07b761d0dab77c8fe1016d2ccd5015dc6f7bc3272c34201a`; `t43` `0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b`; `t44` `3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b` |
| Local t43/t44 checksum receipt | `DASHI/Physics/Closure/HEPDataRatioTableArtifactReceipt.agda`; manifest `scripts/data/hepdata/ins2079374_t43_t44.sha256`; table DOI headers validated locally |
| Provider canonical checksum fields | `providerCanonicalT43ChecksumOrEquivalent` and `providerCanonicalT44ChecksumOrEquivalent`, both still awaiting external response |
| Comparison law | Bounded below-Z `t43` per-bin comparison under the unnormalized differential cross-section ratio convention |
| Covariance/source | HEPData covariance table `t44`, including source, checksum, or provider equivalent |
| `tableChecksumBound` | Provider must bind authoritative HEPData `t43` and `t44` table payloads, or provider-equivalent immutable table records, to the cited DOI/table provenance |
| Non-collapse witness | Bin `12`, prediction `0.0486590199823977`, data `0.049758`, uncertainty `0.00048197510309143566`, pull `-2.280159308132989` |
| Status | Exact status: `accepted`, `rejected`, or `insufficient` |
| Exact rejection reason | Required for `rejected` and `insufficient`; must name the failed field or authority rule |

## Accepted Response

An `accepted` response must explicitly state that the external authority accepts
the evidence packet as sufficient to supply:

```text
DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken
```

The response must also bind that token to the provider identity, DOI fields,
CMS-SMP-20-003 provenance, frozen commit, comparison artifact digest,
comparison law, covariance source, `tableChecksumBound`, and non-collapse witness above.
The local repo still does not fabricate the token; the accepted response is only
usable after the external token is supplied through the typed receipt surface.

If the provider accepts the local HEP-R28 checksums as canonical, the response
must say so explicitly and bind:

```text
providerCanonicalT43ChecksumOrEquivalent:
  0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b
providerCanonicalT44ChecksumOrEquivalent:
  3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b
tableChecksumBound: true
```

Without that explicit provider statement, these remain local checksums only.

## Rejected Response

A `rejected` response must name the exact rejection reason. Valid rejection
classes include:

```text
provider identity not accepted
HEPData DOI mismatch
CMS paper DOI mismatch
frozen commit mismatch
comparison law rejected or underspecified
covariance/source rejected or underspecified
table checksum binding missing or underspecified
non-collapse witness rejected or not reproduced
authority scope does not permit W3AcceptedEvidenceAuthorityToken issuance
```

## Insufficient Response

An `insufficient` response must name the missing field or missing authority rule.
It is not a rejection of the W3 packet; it is a typed request for additional
evidence before an accepted/rejected decision can be made.

## Current Local State

The canonical local instance is still:

```text
awaitingProviderResponse
authorityTokenConstructedHere = false
responseContainsAcceptedToken = false
exactRemainingGap = W3AcceptedEvidenceAuthorityToken
providerCanonicalTableChecksumBindingPresent = false
exactRemainingChecksumGap = provider canonical t43/t44 checksum binding + tableChecksumBound
```

No downstream W3 consumable anchor, evidence-backed empirical target,
accepted-authority external receipt, B4 empirical promotion, W8 origin promotion,
or broad empirical adequacy claim follows from this response template alone.
