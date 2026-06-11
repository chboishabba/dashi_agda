# DY Authority Provider Response Checklist

Date: `2026-05-06`
Status: `provider-answerable checklist; non-promoting`
Owner: `Maxwell-Faraday / W4-W5 shared PDF lane`
External request: `AcceptedDYLuminosityConventionAuthority`
Example packet: `scripts/data/authority_packet.example.json`
Shape-only adapter schema:
`scripts/data/authority_packet.accepted_replacement.schema.json`

This checklist turns the external
`AcceptedDYLuminosityConventionAuthority` request into a one-pass provider
answer. It is an intake checklist only. It does not promote W4 or W5, does not
fabricate an authority token, and does not create a new abstract receipt
skeleton.

The current local first missing remains:

```text
missingAcceptedDYLuminosityConventionAuthority
missingSharedAcceptedDYLuminosityConventionAuthority
```

## Provider Action

Return exactly one response class:

1. `accepted`: you accept the submitted or provider-defined Drell-Yan
   luminosity convention and provide every required field below.
2. `rejected`: you reject the request and identify the exact invalid or
   missing assumptions.
3. `insufficient`: you cannot provide authority, or the answer lacks enough
   identity, provenance, convention detail, checksum, citation, attestation, or
   luminosity data to be used.

If the local candidate convention is rejected but you provide a complete
replacement convention, use `accepted` only when the replacement includes every
required authority field and can be independently reproduced. Otherwise use
`rejected` or `insufficient`.

## Required Fields For Accepted

An `accepted` response must include all fields below as nonempty provider
answers.

| Field | Required provider answer |
|---|---|
| `status` | `accepted` |
| `provider_name` | Person, collaboration, service, tool, review body, or governance body supplying the answer |
| `provider_role` | Why the provider can attest the convention |
| `pdf_set_version` | Exact PDF family and release/version |
| `lhapdf_id` | Exact LHAPDF set id or equivalent provider table identifier |
| `member_id` | Exact member id and uncertainty prescription |
| `grid_checksum` | SHA-256 or provider checksum for every `.info`, `.dat`, archive, or equivalent table used |
| `scale_convention` | Factorization and renormalization scale rule, including whether `Q = M` is accepted |
| `rapidity_window` | Boson/lepton rapidity or eta acceptance rule and integration range |
| `mass_bin_rule` | Integration rule for `50-76`, `76-106`, and `106-170 GeV` windows |
| `flavour_weight_rule` | Drell-Yan channel sum, electroweak charge weights, symmetrisation, and heavy-flavour treatment |
| `integration_method` | PDF interpolation and numerical quadrature method |
| `luminosity_values` | Provider-supplied `L43`, `L45`, and W4 per-bin luminosity vector, or accepted reproducible provider route |
| `efficiency_acceptance_model` | Accepted fiducial, detector, and efficiency/acceptance model tying luminosities to CMS-SMP bins |
| `systematic_budget` | PDF, scale, alphaS, EW/QED/FSR, acceptance, efficiency, and numerical integration uncertainty treatment |
| `cms_smp_publication_pointer` | CMS-SMP analysis id, DOI/arXiv/public page, table/bin mapping, and revision |
| `normalization_preservation_law` | Statement or law that provider-to-runner conversion preserves the accepted normalization |
| `conversion_law` | Mapping from provider fields to W4 `ell_i` and W5 `L45/L43` runner inputs |
| `source_citation` | DOI, arXiv id, manual page, collaboration note, publication source, or provider documentation |
| `attestation_no_manual_overfit` | Explicit no-manual-overfit attestation using provider wording |

If provider luminosities are supplied for adapter ingestion, also include:

| Field | Required provider answer |
|---|---|
| `luminosities.L43` | Positive finite luminosity for the `50-76 GeV` / t43 convention surface |
| `luminosities.L45` | Positive finite luminosity for the `106-170 GeV` / t45 convention surface |
| `luminosities.W4_per_bin_luminosities` | Nonempty list of positive finite W4/Z-peak per-bin luminosities, or objects carrying `luminosity`, `L`, or `value` |

## Rejected Response Form

Use this form when the request is invalid or the provider rejects the submitted
candidate.

```json
{
  "status": "rejected",
  "provider_name": "",
  "provider_role": "",
  "rejection_reason": "",
  "invalid_or_missing_fields": [],
  "source_citation": "",
  "attestation_no_manual_overfit": "No convention or luminosity value is accepted or tuned here."
}
```

A rejected response must not be rewritten as partial acceptance. It becomes a
typed obstruction until a later provider supplies a complete accepted
convention.

## Insufficient Response Form

Use this form when the provider cannot answer authoritatively or the response
is incomplete.

```json
{
  "status": "insufficient",
  "provider_name": "",
  "provider_role": "insufficient",
  "missing_fields": [],
  "insufficient_reason": "",
  "source_citation": "",
  "attestation_no_manual_overfit": "No accepted convention or luminosity value is supplied."
}
```

An insufficient response preserves the first missing
`missingAcceptedDYLuminosityConventionAuthority`.

## Accepted Adapter Packet Shape

Only an actual external accepted provider answer may use this executable packet
shape:

```json
{
  "status": "accepted",
  "provider_name": "",
  "provider_role": "",
  "pdf_set_version": "",
  "lhapdf_id": "",
  "member_id": "",
  "grid_checksum": "",
  "scale_convention": "",
  "rapidity_window": "",
  "mass_bin_rule": "",
  "flavour_weight_rule": "",
  "integration_method": "",
  "luminosity_values": "",
  "efficiency_acceptance_model": "",
  "systematic_budget": "",
  "cms_smp_publication_pointer": "",
  "normalization_preservation_law": "",
  "conversion_law": "",
  "source_citation": "",
  "attestation_no_manual_overfit": "",
  "luminosities": {
    "L43": 0.0,
    "L45": 0.0,
    "W4_per_bin_luminosities": []
  }
}
```

The placeholder values above are a shape illustration, not authority. A real
adapter packet must replace every empty string, every zero, and the empty list
with provider-supplied values before it can be consumed.

## Executable Adapter Contract

`scripts/dy_luminosity_from_authority_packet.py` is the narrow bridge from an
external provider answer to W4/W5 runner inputs. It accepts only `status`
values `accepted` or `replacement`; schema conformance alone is not authority
and does not promote W4 or W5.

The canonical packet shape is captured in
`scripts/data/authority_packet.accepted_replacement.schema.json`. For adapter
ingestion, the provider packet must carry these nonempty authority fields:

```text
status
provider_name
provider_role
pdf_set_version
lhapdf_id
member_id
grid_checksum
scale_convention
rapidity_window
mass_bin_rule
flavour_weight_rule
integration_method
source_citation
attestation_no_manual_overfit
```

The canonical schema requires an explicit `luminosities` object. The adapter
also has a top-level fallback for the same aliases when no `luminosities`
object is present. The accepted input aliases are:

| Runner input | Accepted packet field names |
|---|---|
| W5 denominator `L43` | `L43`, `L_M43_Y43`, `L_50_76`, `L_M50_76`, `luminosity_43` |
| W5 numerator `L45` | `L45`, `L_M45_Y45`, `L_106_170`, `L_M106_170`, `luminosity_45` |
| W4 per-bin vector | `W4_per_bin`, `W4_per_bin_luminosities`, `W4_luminosity_bins`, `W4_luminosities`, `L_W4_bins`, `z_peak_per_bin_luminosities` |

`L43` and `L45` must be positive finite numbers. The W4 vector must be a
nonempty list of positive finite numbers, or objects containing one positive
finite `luminosity`, `L`, or `value` field.

When valid, the adapter emits:

- W4 luminosity CSV with columns `index,luminosity`;
- W4 authority JSON with `status`, `pdfSet`, `lhapdfId`, `gridChecksum`,
  `scaleConvention`, `rapidityConvention`, `massBinRule`, `flavourWeights`,
  `interpolationIntegration`, `source`, and `provenance`;
- W5 provider packet with `status`,
  `accepted_dy_luminosity_convention.{pdf_set,lhapdf_id,grid_checksum,factorization_scale,rapidity_window,mass_bin_integration,flavour_weight_rule,source,provenance}`,
  and `luminosities.{L_M45_Y45,L_M43_Y43}`.

`member_id` is required at intake and is retained in the adapter artifact's
authority/provenance fields, even though the current W4/W5 runner JSON maps do
not pass it through as a named runner field.

## No-Manual-Overfit Attestation

The provider must attest that the convention and any luminosities were selected
from the stated Drell-Yan/PDF prescription and reproducible provenance, not by
manual tuning, post-selection, or denominator search against:

```text
W5 target correction factor: 0.8804486068
W4 Z-peak adequacy threshold
DASHI downstream promotion requirements
```

Acceptable wording:

```text
The convention and computed luminosities were selected according to the stated
Drell-Yan/PDF prescription and public provenance, not by manual tuning to the
DASHI W4/W5 target values.
```

Without this attestation, the response is `insufficient`.

## Stop Condition

Stop intake and leave W4/W5 unpromoted when any of these conditions holds:

- `status` is `rejected` or `insufficient`.
- Any required accepted field is missing or empty.
- Provider role is not adequate for convention authority.
- Checksums, source citations, or reproduction provenance are absent.
- Luminosity values, efficiency/acceptance, systematic budget, CMS-SMP pointer,
  normalization preservation, or conversion law is absent.
- The no-manual-overfit attestation is missing or ambiguous.
- Luminosities are absent, non-finite, non-positive, hand-tuned, or computed
  under a convention different from the accepted authority fields.
- The response asks DASHI to infer, repair, tune, or complete authority locally.

Only a complete external `accepted` response may proceed to adapter ingestion,
and adapter output remains `computed-not-promoted` until downstream W4 and W5
receipts pass their own gates.
