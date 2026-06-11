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
| Canonical t43/t44 JSON intake | User supplied `/home/c/Downloads/hep115656-1316250-1.json` and `/home/c/Downloads/hep115656-1316252-1.json`; staged as `logs/research/provider_inputs/hepdata_ins2079374/t43_canonical.json` and `logs/research/provider_inputs/hepdata_ins2079374/t44_canonical.json`; checksums in `logs/research/provider_inputs/hepdata_ins2079374/checksums.txt` |
| Canonical t43/t44 JSON checks | t43 SHA-256 `5cfefe5a5a99c415f9225a3515383e8ce5e9a874861ff6c5fc08365871bfd340`; t44 SHA-256 `2dfa2abe120981f1f8379d95c8d6e0362394c6f6c8fed01dd45fc76a3e2b660b`; t43 semantic match to local CSV `18/18`; t44 total-covariance semantic match to local CSV `324/324` |
| Canonical t19/t20 JSON intake | User supplied `/home/c/Downloads/hep115656-1316203-1.json` and `/home/c/Downloads/hep115656-1316205-1.json`; staged as `logs/research/provider_inputs/hepdata_ins2079374/t19_canonical.json` and `logs/research/provider_inputs/hepdata_ins2079374/t20_canonical.json`; checksums in `logs/research/provider_inputs/hepdata_ins2079374/checksums.txt` |
| Canonical t19/t20 JSON checks | t19 SHA-256 `c3b5d5cba53e6f0a85cac9b8de077073177d170d13d8e1efdf35db085a45adb7`; t20 SHA-256 `2caae4b6eff3477ac079851afb1c75aa772e1e7bf493b93a830d365828d2d583`; t19 semantic match to local CSV `18/18`; t20 total-covariance semantic match to local CSV `324/324` |
| HEPData metadata route | `https://www.hepdata.net/record/ins2079374?format=json`, SHA-256 `fde88f3acf0b07ccf4be9ddbf311249d5eedf81ca43017a71376dd9a5b1fb36d`; identifies t43 id `1316250` and t44 id `1316252` |
| HEPData payload route | Direct CLI t43/t44 table payload downloads returned HTTP `403`; browser-downloaded canonical JSON payloads are now locally staged and semantically checked |
| t19/t20 source-context intake diagnostic | `logs/research/w3_authority_t19_t20_canonical_json_intake_20260513.json`; metadata and supplied JSON identify t19 id `1316203` and t20 id `1316205`; this binds absolute-source context only, not the active t43/t44 W3 ratio authority payload |
| Provider canonical checksum fields | Canonical JSON payloads now staged as t43 `5cfefe5a5a99c415f9225a3515383e8ce5e9a874861ff6c5fc08365871bfd340` and t44 `2dfa2abe120981f1f8379d95c8d6e0362394c6f6c8fed01dd45fc76a3e2b660b`; accepted authority-token decision still awaiting external response |
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

The canonical t43/t44 JSON payloads are now staged locally. If the provider
accepts the staged canonical JSON payloads as the authoritative payload binding,
the response must say so explicitly and bind:

```text
providerCanonicalT43ChecksumOrEquivalent:
  5cfefe5a5a99c415f9225a3515383e8ce5e9a874861ff6c5fc08365871bfd340
providerCanonicalT44ChecksumOrEquivalent:
  2dfa2abe120981f1f8379d95c8d6e0362394c6f6c8fed01dd45fc76a3e2b660b
tableChecksumBound: true
```

Without that explicit provider statement, these remain local canonical-payload
checksums only; the repo still does not self-issue the accepted authority token.

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

The canonical local instance is now:

```text
awaitingProviderResponse
authorityTokenConstructedHere = false
responseContainsAcceptedToken = false
exactRemainingGap = W3AcceptedEvidenceAuthorityToken
providerCanonicalTableChecksumBindingPresent = candidate-json-payloads-staged
exactRemainingChecksumGap = accepted external authority decision over staged canonical t43/t44 payloads
```

No downstream W3 consumable anchor, evidence-backed empirical target,
accepted-authority external receipt, B4 empirical promotion, W8 origin promotion,
or broad empirical adequacy claim follows from this response template alone.

## t43/t44 Ratio Payload Intake

The 2026-05-13 browser-assisted intake for the active W3 ratio lane is recorded
in:

```text
logs/research/w3_authority_t43_t44_canonical_json_intake_20260513.json
```

The staged payloads are:

```text
logs/research/provider_inputs/hepdata_ins2079374/t43_canonical.json
  sha256 5cfefe5a5a99c415f9225a3515383e8ce5e9a874861ff6c5fc08365871bfd340
  doi 10.17182/hepdata.115656.v1/t43
  name phistar mass 50-76 over mass 76-106

logs/research/provider_inputs/hepdata_ins2079374/t44_canonical.json
  sha256 2dfa2abe120981f1f8379d95c8d6e0362394c6f6c8fed01dd45fc76a3e2b660b
  doi 10.17182/hepdata.115656.v1/t44
  name Covariance matrices for phistar mass 50-76 over mass 76-106
```

Semantic checks against the local ratio CSV cache:

```text
t43: 18/18 rows match for bin center/low/high and ratio value
t44: 324/324 rows match for bin-pair center/low/high and Total uncertainty
```

This closes the local canonical-payload discovery gap for the W3 comparison
surface. The remaining gap is narrower: a real accepted external authority
response must consume these payloads and issue or reject the typed
`W3AcceptedEvidenceAuthorityToken`.

## t19/t20 Source Context Intake

The 2026-05-13 unauthenticated access-route attempt for t19/t20 is recorded in:

```text
logs/research/w3_authority_t19_t20_access_route_discovery_20260513.json
```

The user then supplied the browser-downloaded canonical HEPData JSON exports:

```text
/home/c/Downloads/hep115656-1316203-1.json
/home/c/Downloads/hep115656-1316205-1.json
```

They are staged and hash-bound:

```text
logs/research/provider_inputs/hepdata_ins2079374/t19_canonical.json
  sha256 c3b5d5cba53e6f0a85cac9b8de077073177d170d13d8e1efdf35db085a45adb7
  doi 10.17182/hepdata.115656.v1/t19
  name phistar mass 50-76

logs/research/provider_inputs/hepdata_ins2079374/t20_canonical.json
  sha256 2caae4b6eff3477ac079851afb1c75aa772e1e7bf493b93a830d365828d2d583
  doi 10.17182/hepdata.115656.v1/t20
  name Covariance matrices for phistar mass 50-76
```

Semantic checks against the local CSV cache:

```text
t19: 18/18 rows match for bin center/low/high and measured value
t20: 324/324 rows match for bin-pair center/low/high and Total uncertainty
```

This upgrades the t19/t20 source-context provenance. The active W3 ratio-table
payloads are separately bound in the t43/t44 intake section above.
