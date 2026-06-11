# DY Chi2 Pressure Decomposition Architecture

Date: `2026-05-13`
Status: `non-promoting; blocked on accepted DY convention authority`
Owner: `Lane 5 / DY luminosity and pressure-domain localisation`

## Purpose

The pressure decomposition surface separates observed chi2 pressure into four
review domains only as far as current artifacts allow:

| Domain | Local evidence allowed | Current status |
|---|---|---|
| Convention/bin-normalization | Accepted DY authority fields, provider luminosities, conversion law, normalization preservation | blocked |
| PDF | Accepted PDF set/member/checksum and provider uncertainty budget | indeterminate |
| Model | Existing t43/W4 comparison chi2, residuals, pulls | candidate pressure observed |
| Efficiency/acceptance | Provider fiducial, detector, efficiency/acceptance model and budget | missing |

The surface is implemented by:

```text
scripts/chi2_pressure_decomposition.py
```

It consumes existing comparison JSON when available and emits a JSON artifact.
It intentionally exits blocked when required W4 or accepted DY authority fields
are absent. The artifact is a dashboard input, not a promotion receipt.

## Current Local Pressure Facts

The local t43 frozen comparison artifact records:

```text
t43 ratio chi2/dof = 2.1565191176275618
status = candidate-pass-no-authority-token
```

The local W4 dirty Z-peak status document records:

```text
dirty Z-peak chi2/dof = 298.8462841768543
status = inadequate dirty shape-fit diagnostic; not an accepted-DY adequacy receipt
```

Those numbers localize observed pressure but do not assign final cause. Without
an accepted provider convention and W4 `ell_i` luminosity vector, convention,
bin-normalization, PDF, and model pressure remain entangled.

## Provider Fields Required For Convention/Bin Normalization

An accepted or replacement provider packet must provide these authority fields:

| Field | Required content |
|---|---|
| `provider_name` | External or governance provider identity |
| `provider_role` | Authority role for the DY convention decision |
| `pdf_set_version` | Accepted PDF family and version |
| `lhapdf_id` | Exact LHAPDF set identifier or provider table id |
| `member_id` | Exact PDF member used for central values or declared ensemble rule |
| `grid_checksum` | Checksum for every PDF/grid/table artifact used |
| `scale_convention` | Factorization/renormalization scale rule, including whether `Q = M` is accepted |
| `rapidity_window` | Boson/lepton rapidity or eta acceptance and integration range |
| `mass_bin_rule` | Integration rule for `50-76`, `76-106`, and `106-170 GeV` |
| `flavour_weight_rule` | DY channel sum, charge weights, symmetrisation, and heavy-flavour treatment |
| `integration_method` | PDF interpolation and numerical quadrature method |
| `luminosity_values` | Provider `L43`, `L45`, and W4 per-bin luminosity vector or reproducible provider route |
| `efficiency_acceptance_model` | Fiducial, detector, efficiency, and acceptance model tied to CMS-SMP bins |
| `systematic_budget` | PDF, scale, alphaS, EW/QED/FSR, acceptance, efficiency, and integration uncertainties |
| `cms_smp_publication_pointer` | CMS-SMP analysis id, DOI/arXiv/public page, table/bin mapping, and revision |
| `normalization_preservation_law` | Statement that provider-to-runner conversion preserves the accepted normalization |
| `conversion_law` | Mapping from provider fields to W4 `ell_i` and W5 `L45/L43` runner inputs |
| `source_citation` | DOI, arXiv id, manual page, collaboration source, or provider documentation |
| `attestation_no_manual_overfit` | Explicit statement that the convention was not manually tuned to pass DASHI |

The runner-consumable luminosity fields must include:

```text
L43
L45
W4_per_bin_luminosities
```

Placeholders for efficiency or acceptance are not proof. If
`efficiency_acceptance_model` is absent, the pressure surface must record it as
missing rather than attributing the residual pressure to model or PDF.

## Closed-Fail Rule

The decomposition can report candidate pressure from existing comparison JSON,
but it must remain blocked when any of these are absent:

```text
missingAcceptedDYLuminosityConventionAuthority
missing L43/L45/W4_per_bin_luminosities
missing normalization_preservation_law
missing conversion_law
missing W4 comparison fields when W4 is required
```

The JSON artifact must keep:

```text
no W4 promotion
no W5 promotion
no DY convention receipt constructed
no Candidate256 physical calibration promotion
no placeholder efficiency/acceptance treated as proof
```

## Provider Intake Diagnostics

The tool now emits a grouped authority gate rather than a flat missing-field
list. The provider packet is inspected in these groups:

| Group | Fields |
|---|---|
| `provider_identity` | `provider_name`, `provider_role`, `source_citation`, `attestation_no_manual_overfit` |
| `pdf_authority` | `pdf_set_version`, `lhapdf_id`, `member_id`, `grid_checksum` |
| `dy_convention` | `scale_convention`, `rapidity_window`, `mass_bin_rule`, `flavour_weight_rule`, `integration_method` |
| `luminosity_runner_inputs` | `luminosity_values`, `L43`, `L45`, `W4_per_bin_luminosities` |
| `normalization_conversion` | `normalization_preservation_law`, `conversion_law` |
| `efficiency_acceptance` | `efficiency_acceptance_model`, `systematic_budget`, `cms_smp_publication_pointer` |

Each blocked artifact includes:

```text
inputs.authority.missingByGroup
inputs.authority.runnerLuminosityDiagnostics
inputs.authority.authorityGate.acceptedFalseReasons
firstMissing.field
firstMissing.group
```

This makes the fail-closed state directly actionable for a provider. For
example, an `insufficient` example packet now records the first missing field as
`provider_role` in group `provider_identity`, while also showing that `L43`,
`L45`, and `W4_per_bin_luminosities` are not positive finite runner inputs.

The tool also treats negative authority wording inside required fields as a
gate failure. A packet cannot become accepted by placing text such as "not
accepted" or "no accepted convention" in an attestation while setting
`status = accepted`.

## Interpretation

Current pressure attribution is:

```text
t43: candidate ratio pressure observed, not authority-promoted
W4: dirty Z-peak pressure observed in status docs, not accepted-DY adequacy
convention/bin-normalization: blocked by missing accepted provider fields
PDF: indeterminate because local CT18 material is candidate provenance only
efficiency/acceptance: missing; not proof for any pressure domain
final: no promotable attribution
```
