# W3 Accepted Evidence Authority Token Submission

Date: 2026-05-13
Owner: Curie-W3
Status: final external-facing submission bundle; candidate-only; non-promoting

This submission asks an external evidence authority to decide whether the W3
t43 evidence packet is sufficient to supply:

```text
DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken
```

The repo does not construct this token locally. The token is constructorless in
`DASHI/Physics/Closure/W3AcceptedEmpiricalAuthorityGate.agda`; this submission
is a request for external acceptance, not self-issuance or promotion.

## Empirical Claim Under Review

The claim is intentionally narrow:

```text
DASHI predicts the CMS below-Z Drell-Yan phi* mass-window ratio
50-76 GeV / 76-106 GeV, table t43, using a frozen no-free-parameter
projection and covariance-aware comparison against t44.
```

Numerical comparison recorded in
`DASHI/Physics/Closure/HEPDataW3ComparisonLawReceipt.agda`:

| Field | Value |
|---|---|
| Observable scope | Below-Z t43 mass-window ratio |
| Observable convention | Unnormalized differential cross-section ratio |
| Ratio table | `ins2079374/t43` |
| Covariance table | `ins2079374/t44` |
| Bins | `18` |
| Chi2 | `38.8173441173` |
| Chi2/dof | `2.1565191176` |
| Acceptance threshold used locally | `4.0` |
| Mean pred/data | `0.9941233097` |
| Mean pred/data acceptance window | `[0.97, 1.03]` |

The 2026-05-13 clean candidate comparison artifact records status
`candidate-pass-no-authority-token`, with chi2/dof `2.1565191176275618` and a
non-collapse witness present. The requested token certifies accepted authority
over this bounded W3 evidence packet only. It does not certify above-Z behavior,
full Standard Model
coverage, W4/W5 calibration, GR recovery, W8 origin promotion, or a broad
unification claim.

## Data And Source Packet

Required public/source fields from
`DASHI/Physics/Closure/W3AcceptedEvidenceAuthorityTokenIntakeRequest.agda`:

| Field | Required value |
|---|---|
| Dataset DOI | `10.17182/hepdata.104472` |
| Submission DOI | `10.17182/hepdata.115656.v1` |
| CMS paper DOI | `10.1140/epjc/s10052-023-11631-7` |
| CMS analysis id | `CMS-SMP-20-003` |
| Ratio table | `10.17182/hepdata.115656.v1/t43` |
| Covariance table | `10.17182/hepdata.115656.v1/t44` |
| Observable convention | `UnnormalizedDifferentialCrossSectionRatio` |
| Bin count | `18` |
| Frozen commit | `3205d746639568762c9e97adf4a3672c356bd491` |
| Per-bin artifact SHA-256 | `3987f82678943bab7679a9948e865f74f2263cdbe38a0e997734dad38939fda0` |
| Per-bin projection digest | `cc6ea1a8ea57ef376ae275c1b49e32b27d6d204d7b70cad5c6308b3f8a897a79` |
| Clean comparison artifact | `logs/research/w3_frozen_3205d74_t43_comparison_20260513.json` |
| Clean comparison artifact SHA-256 | `92b61032c06cb4d00d22e00bf9e280b47806f9ebf18f012f5b82a41b0afae238` |
| Clean comparison status | `candidate-pass-no-authority-token` |
| Clean comparison chi2/dof | `2.1565191176275618` |
| Local t19 CSV SHA-256 | `1a1d280da645f4c55aba73aabf1b398a3fd9614532c363d972018f194b653677` |
| Local t20 CSV SHA-256 | `fa4b694211862d4b07b761d0dab77c8fe1016d2ccd5015dc6f7bc3272c34201a` |
| Local t43 CSV SHA-256 | `0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b` |
| Local t44 CSV SHA-256 | `3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b` |
| Local t43/t44 manifest | `scripts/data/hepdata/ins2079374_t43_t44.sha256` |
| Local checksum receipt | `DASHI/Physics/Closure/HEPDataRatioTableArtifactReceipt.agda` |
| Local header binding | t43 first header `#: table_doi: 10.17182/hepdata.115656.v1/t43`; t44 first header `#: table_doi: 10.17182/hepdata.115656.v1/t44` |
| Canonical HEPData record metadata fetch | `https://www.hepdata.net/record/ins2079374?format=json`, SHA-256 `fde88f3acf0b07ccf4be9ddbf311249d5eedf81ca43017a71376dd9a5b1fb36d` |
| Metadata-discovered t43 table | DOI `10.17182/hepdata.115656.v1/t43`, id `1316250`, name `phistar mass 50-76 over mass 76-106` |
| Metadata-discovered t44 table | DOI `10.17182/hepdata.115656.v1/t44`, id `1316252`, name `Covariance matrices for phistar mass 50-76 over mass 76-106` |
| Canonical table payload attempt | Direct HEPData `csv` table downloads for t43/t44 returned HTTP `403`; no canonical payload checksum was bound |

The authority response must confirm that these public/source and runner-bound
fields are acceptable evidence for the W3 authority-token boundary, or return
the exact field or rule that prevents acceptance.

The local t43/t44 checksum route is now bound to HEP-R28:

```text
local t43 checksum:
  0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b
  = HEPDataRatioTableArtifactReceipt.t43Sha256

local t44 checksum:
  3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b
  = HEPDataRatioTableArtifactReceipt.t44Sha256
```

This is a local HEPData artifact/download-route binding only. It is not an
external provider statement that those local CSV payloads are the canonical
HEPData payloads, and it is not an accepted W3 authority token.

On 2026-05-13, the HEPData record metadata route was reachable and identified
the authoritative t43/t44 table names, DOIs, ids, and download URLs. The direct
table-payload URLs returned HTTP `403`, so the local worker could not compute a
canonical t43/t44 payload checksum from HEPData itself. This failed download
does not reject the W3 packet; it preserves the existing external blocker:
provider-equivalent checksum binding is still required before
`tableChecksumBound` may become `true`.

## Remaining Authority Obligation

The local CSV checksums above bind the candidate comparison and source-table
inputs to checked-in local artifacts. They are not a provider attestation that
HEPData table `t43` and covariance table `t44` are checksum-bound to the cited
HEPData/CMS-SMP-20-003 provenance. The exact remaining external obligation is:

```text
tableChecksumBound:
  provider attests the authoritative HEPData t43 and t44 table payloads,
  or provider-equivalent immutable table records, match the cited DOI/table
  provenance and the candidate comparison inputs.
```

Exact fields still required from the provider:

```text
providerCanonicalT43ChecksumOrEquivalent:
providerCanonicalT44ChecksumOrEquivalent:
tableChecksumBound: true
```

Until `tableChecksumBound` is supplied by an accepted external authority, the
packet remains candidate-only and no `W3AcceptedEvidenceAuthorityToken` is
constructed.

## Non-Collapse Witness Status

`DASHI/Physics/Closure/HEPDataW3NonCollapseWitnessReceipt.agda` records the
runner per-bin witness as extracted, while preserving the authority boundary.

| Field | Value |
|---|---|
| Status | `perBinRunnerWitnessExtracted` |
| Artifact path | `/tmp/t43_clean_freeze_v2.json` |
| Artifact SHA-256 | `3987f82678943bab7679a9948e865f74f2263cdbe38a0e997734dad38939fda0` |
| Projection digest | `cc6ea1a8ea57ef376ae275c1b49e32b27d6d204d7b70cad5c6308b3f8a897a79` |
| Prior artifact SHA-256 | `ffd659e6e2f271d75ec6bf90c5be34cbb9959a8f9d32762c1a2231835fb61eac` |
| Prediction bins stable against prior artifact | `true` |
| Witness bin index | `12` |
| Witness phi* | `0.10250000000000001` |
| Witness phi* low/high | `0.091` / `0.114` |
| Prediction | `0.0486590199823977` |
| Data | `0.049758` |
| Uncertainty | `0.00048197510309143566` |
| Pull | `-2.280159308132989` |
| Pull non-zero | `true` |
| Prediction/data distinct | `true` |

The witness establishes a non-collapse evidence point for the bounded t43
comparison lane. It does not itself construct
`W3AcceptedEvidenceAuthorityToken` or
`W3AcceptedAuthorityExternalReceipt`.

## Exact Certification Request

Please return one of the following decisions.

### Accepted

An accepted response must explicitly state that the provider supplies or
recognizes an accepted external token inhabiting:

```text
DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken
```

The acceptance must bind that token to:

- provider identity, role, scope, contact or trace id, and response timestamp
- HEPData DOI `10.17182/hepdata.104472`
- submission DOI `10.17182/hepdata.115656.v1`
- CMS paper DOI `10.1140/epjc/s10052-023-11631-7`
- CMS analysis id `CMS-SMP-20-003`
- ratio table `t43` and covariance table `t44`
- provider-bound table checksums or provider-equivalent immutable table
  records for `t43` and `t44`
- observable convention `UnnormalizedDifferentialCrossSectionRatio`
- frozen commit `3205d746639568762c9e97adf4a3672c356bd491`
- per-bin artifact SHA-256 and projection digest listed above
- clean comparison artifact SHA-256 listed above
- non-collapse witness bin 12 and its numeric values listed above
- bounded claim scope: below-Z t43 W3 authority token only

### Rejected

A rejected response must name the exact failed field or authority rule. Valid
rejection classes are:

- provider identity not accepted
- HEPData DOI mismatch
- CMS paper DOI mismatch
- frozen commit mismatch
- comparison law rejected or underspecified
- covariance/source rejected or underspecified
- table checksum binding missing or underspecified
- non-collapse witness rejected or not reproduced
- authority scope does not permit W3 token issuance

### Insufficient

An insufficient response is not a rejection. It must name the missing evidence
field, missing provenance field, missing reproducibility field, or missing
authority rule needed before an accepted/rejected decision can be made.

## Expected Authority Response Format

Please return a response with this shape:

```text
provider_identity:
provider_role:
provider_scope:
provider_contact_or_trace_id:
response_timestamp:

decision: accepted | rejected | insufficient

token_type_under_review:
  DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken

evidence_binding:
  dataset_doi: 10.17182/hepdata.104472
  submission_doi: 10.17182/hepdata.115656.v1
  paper_doi: 10.1140/epjc/s10052-023-11631-7
  cms_analysis_id: CMS-SMP-20-003
  ratio_table: t43
  covariance_table: t44
  table_checksum_bound: true | false
  authoritative_t43_table_checksum_or_equivalent:
  authoritative_t44_table_checksum_or_equivalent:
  local_t43_csv_sha256: 0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b
  local_t44_csv_sha256: 3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b
  local_t43_t44_manifest: scripts/data/hepdata/ins2079374_t43_t44.sha256
  observable_convention: UnnormalizedDifferentialCrossSectionRatio
  frozen_commit: 3205d746639568762c9e97adf4a3672c356bd491
  per_bin_artifact_sha256: 3987f82678943bab7679a9948e865f74f2263cdbe38a0e997734dad38939fda0
  per_bin_projection_digest: cc6ea1a8ea57ef376ae275c1b49e32b27d6d204d7b70cad5c6308b3f8a897a79
  clean_comparison_artifact_sha256: 92b61032c06cb4d00d22e00bf9e280b47806f9ebf18f012f5b82a41b0afae238
  witness_bin: 12
  witness_prediction: 0.0486590199823977
  witness_data: 0.049758
  witness_uncertainty: 0.00048197510309143566
  witness_pull: -2.280159308132989

if accepted:
  accepted_token_attestation:
  authority_boundary_acknowledgement:

if rejected:
  rejection_class:
  rejection_reason:

if insufficient:
  missing_fields:
  missing_authority_rules:
```

## Exclusions And Forbidden Interpretations

This submission does not ask the provider to certify any of the following:

- full Standard Model coverage
- W4 Z-peak adequacy or physical calibration
- W5 t45 PDF correction or above-Z closure
- W6 runtime PNF closure
- W8 origin promotion
- B4 empirical promotion beyond the exact W3 token boundary
- GR metric recovery or Einstein equation recovery
- GRQFT closure promotion
- complete physics unification
- self-issuance by the repository owner

An accepted token would make the W3 t43 evidence packet externally consumable
as a bounded empirical anchor. It would not, by itself, promote any downstream
physics gate.

## Local Files Read For This Submission

This packet is conservative over these local sources:

- `Docs/W3AcceptedEvidenceAuthorityProviderResponse.md`
- `DASHI/Physics/Closure/W3AcceptedEvidenceAuthorityTokenReceipt.agda`
- `DASHI/Physics/Closure/W3AcceptedEvidenceAuthorityTokenIntakeRequest.agda`
- `DASHI/Physics/Closure/HEPDataW3ComparisonLawReceipt.agda`
- `DASHI/Physics/Closure/HEPDataW3NonCollapseWitnessReceipt.agda`
- `DASHI/Physics/Closure/W3AcceptedAuthorityExternalReceiptRequestPack.agda`
- `DASHI/Physics/Closure/W3AcceptedEmpiricalAuthorityGate.agda`

## Handling After Response

If the response is accepted, ingest it through:

```text
DASHI/Physics/Closure/W3AcceptedEvidenceAuthorityTokenReceipt.agda
```

and require the typed receipt to carry the external token. Do not treat this
Markdown submission, public DOI availability, or local runner reproducibility
as token construction.

If the response is rejected or insufficient, record the exact failed field or
missing authority rule and keep W3 blocked on:

```text
missing accepted external W3AcceptedEvidenceAuthorityToken
```
