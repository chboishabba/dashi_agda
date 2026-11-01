# Accepted DY Luminosity Convention Authority Submission

Date: `2026-05-06`
Status: `provider-facing submission; non-promoting`
Owner: `Maxwell-Faraday / W4-W5 shared PDF lane`

This submission asks an external or repo-governance authority to provide an
accepted Drell-Yan parton-luminosity and bin-integration convention for the
DASHI W4/W5 comparison. It is deliberately narrower than a physics claim: it
does not promote W4, does not promote W5, and does not assert that the current
local CT18NLO probes close either gate.

The requested authority replaces the current first missing item:

```text
missingAcceptedDYLuminosityConventionAuthority
missingSharedAcceptedDYLuminosityConventionAuthority
```

## Observable Compared

The comparison concerns CMS-SMP-20-003 Drell-Yan phi-star mass-window
observables, using a DASHI prediction surface and a PDF-backed Drell-Yan
parton luminosity convention.

The required convention must support these windows:

| Lane | Mass window | Use |
|---|---:|---|
| W3/t43 | `50-76 GeV` relative to `76-106 GeV` | Existing below-Z empirical anchor and reference normalization |
| W4/Z peak | `76-106 GeV` | Z-peak shape adequacy and calibration anchor |
| W5/t45 | `106-170 GeV` relative to `50-76 GeV` or the accepted provider-defined reference | Above-Z neutral-current correction factor |

The target scalar currently recorded for W5 is:

```text
required W5 correction factor: 0.8804486068
```

This target is not by itself an authority. The authority must define the
accepted Drell-Yan luminosity convention that determines what quantity is being
computed and how it is reproduced.

## Why Local Proxies Are Insufficient

The repository has already tested plausible local CT18NLO proxies. They are
recorded as negative diagnostics, not as closure evidence.

| Probe | Result | Target | Disposition |
|---|---:|---:|---|
| Fixed-`x` u-quark `xfxQ` ratio | `1.0506681065158017` | `0.8804486068` | Fails target and is not a bin-integrated DY luminosity |
| Rapidity-window `t45/z_peak` | `0.7514043986785174` | `0.8804486068` | Fails target; Z-peak denominator hypothesis rejected |
| Rapidity-window `t45/t43` | `0.3348750784006896` | `0.8804486068` | Fails target; t43 denominator-fix hypothesis rejected under the tested convention |

These failures sharpen the request. The missing item is not another denominator
tweak. The missing item is an accepted parton-luminosity, mass-bin, rapidity,
scale, flavour-weight, and integration convention with provenance.

## Authority Requested

Please return one of three response classes:

1. `accepted`: accept the submitted convention or a provider-defined equivalent
   and supply every required field below.
2. `rejected`: reject the request and name the exact invalid assumptions or
   missing fields.
3. `insufficient`: state that the provider cannot supply authority, or that the
   response lacks enough provenance to be used.

If the local CT18NLO candidate is rejected but a complete replacement convention
is supplied, mark the response as `accepted` only if the replacement convention
contains all required fields and can be independently reproduced.

## Exact Fields Requested

Return the following fields verbatim.

| Field | Required content |
|---|---|
| `provider_name` | Name of the person, collaboration, service, tool, or governance body supplying the answer |
| `provider_role` | Why this provider can attest the convention, or `insufficient` if they cannot |
| `pdf_set_version` | Exact PDF family and release/version, e.g. `CT18NLO`, `MSHT20`, `NNPDF4.0`, or replacement |
| `lhapdf_id` | Exact LHAPDF set id or equivalent table identifier |
| `member_id` | Exact member id and uncertainty prescription |
| `grid_checksum` | SHA-256 or provider checksum for every `.info`, `.dat`, archive, or equivalent table used |
| `scale_convention` | Factorization and renormalization scale rule, including whether `Q = M` is accepted |
| `rapidity_window` | Boson/lepton rapidity or eta acceptance rule and integration range |
| `mass_bin_rule` | Integration rule for `50-76`, `76-106`, and `106-170 GeV` windows |
| `flavour_weight_rule` | Drell-Yan channel sum, electroweak charge weights, symmetrisation, and heavy-flavour treatment |
| `integration_method` | PDF interpolation and numerical quadrature method |
| `source_citation` | DOI, arXiv id, manual page, collaboration note, or publication source for the convention |
| `attestation_no_manual_overfit` | Explicit statement that the convention/result was not manually tuned to the DASHI W4/W5 target |
| `status` | Exactly one of `accepted`, `rejected`, or `insufficient` |

## Expected Output Format

Preferred response format:

```json
{
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
  "source_citation": "",
  "attestation_no_manual_overfit": "",
  "status": "accepted"
}
```

If the provider supplies computed luminosities in addition to the convention,
include them under a separate `computed_values` object:

```json
{
  "computed_values": {
    "L43": "",
    "L45": "",
    "R45_over_43": "",
    "W4_per_bin_luminosities": [],
    "provenance_hash": ""
  }
}
```

The computed values are optional for the authority itself, but any supplied
values must use the stated convention exactly.

## Receipt Ingestion Contract

The response is ingested by:

```text
DASHI/Physics/Closure/AcceptedDYLuminosityConventionAuthorityReceipt.agda
Docs/AcceptedDYLuminosityConventionAuthorityResponse.md
```

The Agda receipt already defines the canonical payload fields:

```text
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
status accepted/rejected/insufficient
```

An `accepted` response can later inhabit the accepted-convention path only if:

- every required field is present;
- the provider role is adequate for convention authority;
- checksums and source citations are reproducible;
- the no-manual-overfit attestation is explicit;
- the response class is accepted or a complete accepted replacement;
- downstream W4/W5 runners consume the same convention without alteration.

Until then, the canonical local receipt remains:

```text
intakeStatus: awaitingProviderResponse
responseStatus: insufficient
externalProviderAnswerPresent: false
acceptedAuthorityConstructed: false
promotesW4: false
promotesW5: false
```

## Handling Outcomes

### Accepted

If `status = accepted`, the response should be copied into
`Docs/AcceptedDYLuminosityConventionAuthorityResponse.md` and mirrored in the
Agda receipt as an external payload. This enables, but does not itself complete:

```text
AcceptedDYLuminosityConventionAuthority
-> W4ZAdequacyReceipt
-> W5T45CorrectionReceipt
```

W4 and W5 remain unpromoted until their respective numerical receipts are
computed under the accepted convention and pass their own gates.

### Rejected

If `status = rejected`, record the provider's exact invalid assumptions,
missing fields, or convention mismatch. The rejection becomes a typed
obstruction for the current local convention and should not be rewritten as a
partial acceptance.

### Insufficient

If `status = insufficient`, record the missing identity, role, convention,
checksum, citation, attestation, or reproducibility fields. The first missing
remains:

```text
missingAcceptedDYLuminosityConventionAuthority
```

## No-Manual-Overfit Attestation

The authority must explicitly attest that the accepted convention and any
reported luminosity values were not chosen, tuned, or post-selected to match:

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

## Non-Promotion Statement

This submission does not close W4, does not close W5, and does not create an
authority token. It only asks for the external convention/provenance receipt
required before W4 adequacy and W5 correction can be computed honestly.
