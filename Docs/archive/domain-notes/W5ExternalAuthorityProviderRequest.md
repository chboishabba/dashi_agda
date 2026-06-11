# W5 External Authority Provider Request

Date: `2026-05-13`
Status: `provider request; blocked; non-promoting`
Owner: `Lane 6`

This packet asks for the external W5 bridge needed to interpret public
CMS-SMP-20-003 phi-star ratios against the W5 correction surface. It does not
promote W5.

## Requested Authority Identity

Primary W5 bridge request:

```text
accepted A(M, phi*) bridge or accepted observable-conversion law
```

If W5 remains on the older PDF-correction surface, the response must also bind
the accepted Drell-Yan/PDF luminosity convention and state how the bridge maps
to the W5 mass-integrated cross-section/PDF correction target.

## Public Ratio Diagnostics

The public HEPData `DSIG/DPHISTAR` ratio-table diagnostic is:

| Diagnostic | Value |
|---|---:|
| `t43/Z` | `0.048798342138242475` |
| `t45/Z` | `0.025440376842598356` |
| `t45/t43` | `0.5213369087525034` |

Provenance:

| Field | Bound value |
|---|---|
| Runner | `scripts/run_w4w5_hepdata_public_ratio_integral.py` |
| Output artifact | `scripts/data/outputs/w4w5_hepdata_public_ratio_integral.json` |
| Z denominator table | `10.17182/hepdata.115656.v1/t21` |
| Below-Z ratio table | `10.17182/hepdata.115656.v1/t43` |
| Above-Z ratio table | `10.17182/hepdata.115656.v1/t45` |
| Formula | `sum Ratio_i * (dsigma_Z/dphistar)_i * dphistar_i / sum (dsigma_Z/dphistar)_i * dphistar_i` |
| Public record | `https://www.hepdata.net/record/ins2079374` |
| CMS public page | `https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/` |
| CMS submission YAML | `https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/submission.yaml` |

Boundary: `0.5213369087525034` is not the older W5 PDF-carrier target
`0.8804486068`, not a `d sigma / dM` mass-window ratio, and not a PDF
correction target without an accepted conversion law.

## Evidence And Source Artifacts

```text
Docs/W4W5AcceptanceBridgeProviderRequest.md
Docs/W4W5DYConventionCurrentBlocker.md
Docs/AcceptedDYLuminosityConventionAuthorityProviderPacket.md
DASHI/Physics/Closure/W4W5PublicHEPDataRatioDiagnostic.agda
DASHI/Physics/Closure/W4W5PhiStarToMassAcceptanceBridgeRequest.agda
DASHI/Physics/Closure/W5CT18ExternalIntakeReceipt.agda
```

## Exact Receipt Shape Needed

Return exactly one top-level decision:

```text
accepted
rejected
insufficient
```

An accepted W5 response must provide one of:

1. A central-value acceptance/efficiency surface `A(M, phi*)` for the
   CMS-SMP-20-003 mass windows `50-76`, `76-106`, and `106-170 GeV`, including
   the at-least-one-jet selection used by `t43` and `t45`.
2. An accepted observable-conversion law from public `DSIG/DPHISTAR`
   ratio-table integrals to mass-integrated cross-section/PDF correction
   ratios.
3. An accepted retarget law stating that W5 should consume the public phi-star
   ratio surface directly, with the exact replacement target and downstream
   normalization law.
4. A provider statement that no such conversion or retarget is valid.

Any accepted bridge must bind lepton-channel treatment, jet requirement,
fiducial phase space, normalization, bin-width convention, covariance and
systematic propagation, DOI/public URL/source citation, immutable provenance,
provider role, and no-manual-overfit attestation.

## Non-Promotion Boundary

```text
promotesW5 = false
bridgeComputableFromPublicArtifacts = false
```

The public phi-star ratios are diagnostic only until an accepted bridge or
retarget law is supplied.
