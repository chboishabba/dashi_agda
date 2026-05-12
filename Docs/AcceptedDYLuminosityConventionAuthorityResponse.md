# Accepted DY Luminosity Convention Authority Response

Date: `2026-05-06`
Status: `provider-response template; non-promoting`
Owner: `Maxwell-Faraday / W4-W5 shared PDF lane`
Request packet: `Docs/AcceptedDYLuminosityConventionAuthorityProviderPacket.md`

This document is the response template for an external/provider answer to the
accepted Drell-Yan luminosity convention authority request. It is an intake
surface only. It does not fabricate authority, does not accept the local CT18NLO
candidate by itself, and does not close W4 or W5.

The current local state is still:

```text
missingAcceptedDYLuminosityConventionAuthority
missingSharedAcceptedDYLuminosityConventionAuthority
```

## Provider Response Template

Use the following fields verbatim when a provider answer is received.

| Field | Required response |
|---|---|
| `provider_name` | Name of the person, collaboration, service, tool, or governance body supplying the answer |
| `provider_role` | Why this provider can attest the convention, or `insufficient` if they cannot |
| `pdf_set_version` | Exact PDF family and release/version, e.g. CT18NLO, MSHT, NNPDF, or replacement |
| `lhapdf_id` | Exact LHAPDF set id or equivalent provider-table identifier |
| `member_id` | Exact member id and uncertainty prescription |
| `grid_checksum` | SHA-256 or provider checksum for every `.info`, `.dat`, archive, or equivalent table used |
| `scale_convention` | Factorization/renormalization scale rule, including whether `Q = M` is accepted |
| `rapidity_window` | Boson/lepton rapidity or eta acceptance rule and integration range |
| `mass_bin_rule` | Integration rule for CMS-SMP-20-003 windows `50-76`, `76-106`, and `106-170` GeV |
| `flavour_weight_rule` | Drell-Yan channel sum, charge weights, symmetrisation, and heavy-flavour treatment |
| `integration_method` | PDF interpolation and numerical quadrature method |
| `luminosity_values` | Provider-supplied `L43`, `L45`, and W4 per-bin luminosity vector, or accepted reproducible provider route |
| `efficiency_acceptance_model` | Accepted fiducial, detector, and efficiency/acceptance model tying luminosities to CMS-SMP bins |
| `systematic_budget` | PDF, scale, alphaS, EW/QED/FSR, acceptance, efficiency, and numerical integration uncertainty treatment |
| `cms_smp_publication_pointer` | CMS-SMP analysis id, DOI/arXiv/public page, table/bin mapping, and revision |
| `normalization_preservation_law` | Statement or law that provider-to-runner conversion preserves the accepted normalization |
| `conversion_law` | Mapping from provider fields to W4 `ell_i` and W5 `L45/L43` runner inputs |
| `source_citation` | DOI, arXiv id, manual page, collaboration note, or publication source |
| `attestation_no_manual_overfit` | Explicit statement that the answer was not manually tuned to the DASHI W4/W5 target |
| `status` | One of `accepted`, `rejected`, or `insufficient` |

## Response Classes

`accepted` means the provider accepts the named convention and supplies every
required field above.

`replacement` means the provider rejects the local candidate but supplies a
complete replacement convention. The `status` field should still be `accepted`
only if the replacement convention is complete and externally attested.

`rejected` means the provider rejects the request and identifies the invalid or
missing fields.

`insufficient` means the response cannot be used as authority because one or
more required fields, provenance links, checksums, or attestations are missing.

## Current Canonical Local Response

No external/provider answer has been received in this lane. Therefore the
canonical local receipt must remain `insufficient` or awaiting response. It may
record the required payload shape, but it must not construct an accepted
authority receipt.

Current canonical values:

```text
provider_name: missing external provider answer
provider_role: missing
pdf_set_version: missing
lhapdf_id: missing
member_id: missing
grid_checksum: missing
scale_convention: missing
rapidity_window: missing
mass_bin_rule: missing
flavour_weight_rule: missing
integration_method: missing
luminosity_values: missing
efficiency_acceptance_model: missing
systematic_budget: missing
cms_smp_publication_pointer: missing
normalization_preservation_law: missing
conversion_law: missing
source_citation: missing
attestation_no_manual_overfit: missing
status: insufficient
```

## Non-Promotion Rules

- This template does not close W4.
- This template does not close W5.
- Local CT18NLO packet fields remain candidate provenance only.
- Numeric agreement alone is not accepted authority.
- Luminosity values, efficiency/acceptance, systematic budget, CMS-SMP pointer,
  normalization preservation, and conversion law are all required before the
  W4/W5 runners may consume an accepted packet.
- An accepted or replacement response must be ingested as an external payload
  before any downstream W4/W5 receipt can consume it.
- The first missing remains
  `missingAcceptedDYLuminosityConventionAuthority` until an actual provider
  answer supplies all required fields and provenance.
