# Accepted DY Luminosity Convention Authority Provider Packet

Date: `2026-05-06`
Status: `provider-facing request; non-promoting`
Owner: `Maxwell-Faraday / W4-W5 shared PDF lane`

This packet asks an external or repo-governance authority to either accept,
replace, or reject the Drell-Yan parton-luminosity convention needed by the W4
Z-peak adequacy lane and the W5 t45 PDF-correction lane.

The packet does not close W4 or W5. It only defines the exact receipt needed to
replace:

```text
missingAcceptedDYLuminosityConventionAuthority
missingSharedAcceptedDYLuminosityConventionAuthority
```

## Request

Please provide an `AcceptedDYLuminosityConventionAuthority` receipt with the
following fields:

| Field | Required content |
|---|---|
| PDF set | Accepted family and version, e.g. CT18, MSHT, NNPDF, or equivalent |
| LHAPDF id | Exact LHAPDF set id/member, or equivalent table identifier |
| Grid checksum | SHA-256 or provider checksum for every `.info`/`.dat` or table artifact used |
| Scale convention | Factorization/renormalization scale rule, including whether `Q = M` is accepted |
| Rapidity convention | Boson/lepton rapidity or eta acceptance rule and integration range |
| Mass-bin rule | Integration rule for CMS-SMP-20-003 windows `50-76`, `76-106`, and `106-170` GeV |
| Flavour weights | Drell-Yan channel sum, charge weights, symmetrisation, and heavy-flavour treatment |
| Interpolation/integration | PDF interpolation and numerical quadrature method |
| Luminosity values | Provider-supplied `L43`, `L45`, and W4 per-bin luminosity vector, or a provider route that computes them reproducibly |
| Efficiency/acceptance | Accepted fiducial, detector, and efficiency/acceptance model tying luminosities to the CMS-SMP bins |
| Systematic budget | PDF, scale, alphaS, EW/QED/FSR, acceptance, efficiency, and numerical integration uncertainty treatment |
| CMS-SMP publication pointer | CMS-SMP analysis id, DOI/arXiv/public page, table/bin mapping, and revision used for the convention |
| Normalization preservation | Statement or law that provider-to-runner conversion preserves the accepted normalization |
| Conversion law | Mapping from provider fields to W4 `ell_i` and W5 `L45/L43` runner inputs |
| Source | DOI, arXiv id, manual page, or collaboration/publication source for the convention |
| Provenance | Provider identity, command/API, input paths, checksums, timestamp, and no-manual-overfit attestation |

## Candidate Local Packet

The repo-local candidate is recorded in:

```text
scripts/data/pdf/ct18_dashi_pdf_packet.json
scripts/extract_ct18_pdf_packet.py
```

Current candidate identifiers:

```text
PDF set: CT18NLO
LHAPDF set id: 14400
member: 0 central value
archive SHA-256: c9127231e77e97cbec79cb5839203ab00f8db77237a061b61f9420f2b7b9c213
central grid SHA-256: 375db856d2f8c7087a626c92ebf228d3f080e5de83175519778ffaf6e72e5410
info SHA-256: be60232d8e6c49982c82f5fa990fd5b0fd1050719944f31602bf27cdb16548b0
```

These fields are candidate provenance only. They are not an accepted authority
receipt.

## Negative Local Probes

The following local probes are explicitly rejected as W4/W5 closure evidence:

| Probe | Result | Target | Disposition |
|---|---:|---:|---|
| Fixed-`x` u-quark `xfxQ` ratio | `1.0506681065158017` | `0.8804486068` | Fails target |
| Rapidity-window `t45/z_peak` | `0.7514043986785174` | `0.8804486068` | Fails target |
| Rapidity-window `t45/t43` | `0.3348750784006896` | `0.8804486068` | Denominator-fix hypothesis falsified |

These results sharpen the blocker. The missing item is not another denominator
tweak; it is an accepted Drell-Yan luminosity and bin-integration convention
with provenance.

## Expected Provider Answer Classes

An acceptable response is one of:

1. `accepted`: the provider accepts a convention and supplies all required
   fields above.
2. `replacement`: the provider rejects the local candidate and supplies a
   replacement convention with the same required fields.
3. `rejected`: the provider rejects the request and names the exact missing or
   invalid fields.

Only `accepted` or `replacement` can unblock W4/W5. Numeric agreement alone is
insufficient without provenance and convention authority.

## Runner-Consumable Fields

The accepted packet must be directly consumable by the W4/W5 runners. It must
therefore bind the following fields without requiring a local denominator tweak
or numeric inference:

```text
luminosity_values: L43, L45, and W4_per_bin_luminosities, or an accepted reproducible provider computation route
efficiency_acceptance_model: fiducial, detector, and efficiency/acceptance model for the CMS-SMP bins
systematic_budget: PDF, scale, alphaS, EW/QED/FSR, acceptance, efficiency, and integration uncertainties
cms_smp_publication_pointer: CMS-SMP analysis id, DOI/arXiv/public page, table/bin mapping, and revision
normalization_preservation_law: provider-to-runner conversion preserves the accepted normalization
conversion_law: provider fields map to W4 ell_i and W5 L45/L43 inputs
```

If any of these fields is absent, the typed first missing remains
`missingAcceptedDYLuminosityConventionAuthority`.

## Downstream Receipt Contract

After an accepted convention exists, the next receipts are:

```text
AcceptedDYLuminosityConventionAuthority
-> W4ZAdequacyReceipt
-> W5T45CorrectionReceipt
-> Candidate256PhysicalCalibrationExternalReceipt
-> W4MatterStressEnergyInterfaceReceipt
-> DiscreteEinsteinLawReceipt
-> GRQFTClosurePromotionReceipt
```

No downstream receipt may be promoted from this packet alone.

## Validation Surfaces

The typed repo surfaces mirroring this request are:

```text
DASHI/Physics/Closure/W4W5AcceptedDYLuminosityConventionDiagnostic.agda
DASHI/Physics/Closure/W4W5PDFSharedDependencyDiagnostic.agda
DASHI/Physics/Closure/W5PDFCarrierExternalIntakeRequest.agda
DASHI/Physics/Closure/W5CT18ExternalIntakeReceipt.agda
```
