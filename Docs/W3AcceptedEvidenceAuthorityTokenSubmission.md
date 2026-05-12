# W3 Accepted Evidence Authority Token Submission

Date: 2026-05-06
Owner: Curie-W3
Status: final external-facing submission bundle; non-promoting

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

The requested token certifies accepted authority over this bounded W3 evidence
packet only. It does not certify above-Z behavior, full Standard Model
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
| Ratio table | `10.17182/hepdata.115656.v1/t43` |
| Covariance table | `10.17182/hepdata.115656.v1/t44` |
| Observable convention | `UnnormalizedDifferentialCrossSectionRatio` |
| Bin count | `18` |
| Frozen commit | `3205d746639568762c9e97adf4a3672c356bd491` |
| Per-bin artifact SHA-256 | `3987f82678943bab7679a9948e865f74f2263cdbe38a0e997734dad38939fda0` |
| Per-bin projection digest | `cc6ea1a8ea57ef376ae275c1b49e32b27d6d204d7b70cad5c6308b3f8a897a79` |

The authority response must confirm that these public/source and runner-bound
fields are acceptable evidence for the W3 authority-token boundary, or return
the exact field or rule that prevents acceptance.

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
- ratio table `t43` and covariance table `t44`
- observable convention `UnnormalizedDifferentialCrossSectionRatio`
- frozen commit `3205d746639568762c9e97adf4a3672c356bd491`
- per-bin artifact SHA-256 and projection digest listed above
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
  ratio_table: t43
  covariance_table: t44
  observable_convention: UnnormalizedDifferentialCrossSectionRatio
  frozen_commit: 3205d746639568762c9e97adf4a3672c356bd491
  per_bin_artifact_sha256: 3987f82678943bab7679a9948e865f74f2263cdbe38a0e997734dad38939fda0
  per_bin_projection_digest: cc6ea1a8ea57ef376ae275c1b49e32b27d6d204d7b70cad5c6308b3f8a897a79
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
