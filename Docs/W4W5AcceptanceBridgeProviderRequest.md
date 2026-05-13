# W4/W5 Acceptance Bridge Provider Request

Date: `2026-05-13`
Status: `provider request; non-promoting; awaiting accepted bridge`
Owner: `Lane 6`

This request asks an external provider to supply the missing W4/W5 bridge
artifact for CMS-SMP-20-003 / HEPData `ins2079374`. It records the public
ratio-table diagnostics already available locally and the exact reason they do
not close W4/W5 by themselves.

Typed request surface:

```text
DASHI.Physics.Closure.W4W5PhiStarToMassAcceptanceBridgeRequest
```

## Public Ratio Diagnostics

The local diagnostic runner computes only the public
`DSIG/DPHISTAR / DSIG/DPHISTAR` ratio-table surface:

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

The public CMS/HEPData materials audited locally include measured
`DSIG/DPHISTAR` tables, ratio tables, covariance matrices, uncertainty
components, detector response matrices, and submission metadata. They do not
publish a central-value acceptance/efficiency surface `A(M, phi*)`, and they
do not publish an accepted conversion law from the phi-star ratio integrals to
the W4/W5 mass-integrated cross-section/PDF correction surface.

## Exact Missing Artifact

Please provide one of the following:

1. A central-value acceptance/efficiency surface `A(M, phi*)` for the
   CMS-SMP-20-003 mass windows `50-76`, `76-106`, and `106-170 GeV`, including
   the at-least-one-jet selection used by `t43` and `t45`.
2. An accepted observable-conversion law from CMS-SMP-20-003 `DSIG/DPHISTAR`
   ratio-table integrals to mass-integrated cross-section/PDF correction
   ratios.
3. A provider statement that no such conversion is valid for this use.

Any accepted bridge should bind:

- lepton-channel treatment;
- jet requirement and fiducial phase space;
- mass-window, phi-star-bin, normalization, and bin-width conventions;
- covariance/systematic propagation for the conversion;
- DOI, public URL, immutable package identity, checksum, or equivalent
  provenance;
- provider role and scope of authority.

## Non-Overclaiming Boundary

The current local result is diagnostic only:

```text
promotesW4 = false
promotesW5 = false
bridgeComputableFromPublicArtifacts = false
```

The ratio `0.5213369087525034` is the public `t45/t43` ratio-table result. It
is not the older W5 PDF-carrier target `0.8804486068`, does not establish a
`d sigma / dM` mass-window ratio, and does not construct a DY/PDF luminosity
convention.

W4/W5 remain blocked until an accepted `A(M, phi*)` bridge or an accepted
observable-conversion law is supplied and bound to the cited provenance.

## Public pT Absolute-Table Diagnostic

The pT absolute tables are reachable from the CMS public YAML mirror even when
direct HEPData table downloads return a CLI Cloudflare 403. The current runner:

```text
scripts/run_w4w5_hepdata_pt_integral.py
scripts/data/outputs/w4w5_hepdata_pt_integral.json
```

integrates `d sigma / d pT(ll)` over pT bins for the public mass-window tables
and records SHA-256 digests for every consumed source payload.

Direct HEPData URLs attempted from CLI:

```text
https://www.hepdata.net/download/table/ins2079374/t1/csv
https://www.hepdata.net/download/table/ins2079374/t3/csv
https://www.hepdata.net/download/table/ins2079374/t21/csv
https://www.hepdata.net/download/table/ins2079374/t22/csv
https://www.hepdata.net/download/table/ins2079374/Table%201/1/csv
https://www.hepdata.net/download/table/ins2079374/Table%203/1/csv
```

All six returned `HTTP 403` / Cloudflare from CLI in the 2026-05-13 run. The
script therefore used these CMS public YAML URLs:

```text
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/pt_ll_mass_50-76.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/pt_ll_mass_76-106.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/pt_ll_mass_106-170.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/pt_ll_mass_50-76_jet.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/pt_ll_mass_76-106_jet.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/pt_ll_mass_106-170_jet.yaml
```

Current integrated pT results:

| Diagnostic | Value | Gap to `0.8804486068` |
|---|---:|---:|
| inclusive `50-76 / 76-106` | `0.04898655685575138` | `0.8314620499442487` |
| inclusive `106-170 / 76-106` | `0.025425613872080487` | `0.8550229929279195` |
| inclusive `106-170 / 50-76` | `0.5190324755207884` | `0.3614161312792117` |
| at-least-one-jet `50-76 / 76-106` | `0.041114594269958955` | `0.839334012530041` |
| at-least-one-jet `106-170 / 76-106` | `0.031199447609565292` | `0.8492491591904348` |
| at-least-one-jet `106-170 / 50-76` | `0.7588411892066674` | `0.1216074175933326` |

This falsifies the narrow hypothesis that simply integrating public absolute
pT tables yields the older `0.8804486068` W5 correction. It does not falsify
the broader possibility of an accepted PDF/luminosity or observable-conversion
law; it just means that law is not the direct public pT-table integral.
