# W4/W5 DY Convention Current Blocker

Date: `2026-05-13`
Status: `blocked; provider-facing; non-promoting`
Owner: `Maxwell / W4-W5 empirical blocker status`

## Current State

W4/W5 remain blocked on the same upstream authority item:

```text
missingAcceptedDYLuminosityConventionAuthority
missingSharedAcceptedDYLuminosityConventionAuthority
```

The local CT18NLO material is present and provenance-ready as a candidate
diagnostic, but it is not an accepted Drell-Yan luminosity convention authority.
No W4 promotion, W5 promotion, external PDF carrier, or downstream physical
calibration receipt follows from the current local artifacts.

Lane 5 now has a non-promoting pressure-domain localisation surface:

```text
scripts/chi2_pressure_decomposition.py
Docs/DYPressureDecompositionArchitecture.md
```

This surface can record candidate t43/W4 chi2 pressure, but it does not assign
final cause while the accepted DY convention/bin-normalization authority is
missing.

The current diagnostic artifact shape is grouped by provider obligation. A
blocked run records:

```text
firstMissing.field
firstMissing.group
inputs.authority.missingByGroup
inputs.authority.runnerLuminosityDiagnostics
inputs.authority.authorityGate.acceptedFalseReasons
```

This is intentionally sharper than the older flat blocker. It distinguishes
provider identity, PDF authority, DY convention, runner luminosities,
normalization/conversion, and efficiency/acceptance gaps, while preserving the
same first missing:

```text
missingAcceptedDYLuminosityConventionAuthority
```

## CT18 Local Grid Status

Local CT18NLO grid artifacts are recorded under:

```text
scripts/data/pdf/ct18_dashi_pdf_packet.json
scripts/data/pdf/CT18NLO.tar.gz
scripts/data/pdf/CT18NLO/CT18NLO_0000.dat
scripts/data/pdf/CT18NLO/CT18NLO.info
```

Locally evidenced identifiers:

| Item | Local value |
|---|---|
| PDF set | `CT18NLO` |
| LHAPDF set id | `14400` |
| member | `0` central value |
| format | `lhagrid1` |
| archive SHA-256 | `c9127231e77e97cbec79cb5839203ab00f8db77237a061b61f9420f2b7b9c213` |
| central grid SHA-256 | `375db856d2f8c7087a626c92ebf228d3f080e5de83175519778ffaf6e72e5410` |
| info SHA-256 | `be60232d8e6c49982c82f5fa990fd5b0fd1050719944f31602bf27cdb16548b0` |

The packet status is locally recorded as:

```text
accepted_dy_luminosity_convention_status:
candidate_local_ct18nlo_convention_not_accepted
```

Euler's 2026-05-13 preflight reran the CT18 equivalent-table candidate and
recorded the current tool/provider obstruction:

| Artifact | SHA-256 |
|---|---|
| `logs/research/w4w5_pdf_ct18_candidate_run_20260513.json` | `7b4e5e815c3e65619cd9591734eb00e7c80be0402c6d06c3c8d33d1c8da6609f` |
| `logs/research/w4w5_pdf_lhapdf_intake_obstruction_20260513.json` | `082448674db69767aff1897f7fb66054a6dbc3a70b86f31813185a6a2c10fd41` |

The obstruction artifact records:

```text
lhapdf executable: /usr/bin/lhapdf, version 6.5.5
lhapdf-config: /usr/bin/lhapdf-config, version 6.5.5
Python lhapdf module: available under system `python3`; absent under the repo
`.venv/bin/python` environment
MSHT20 local grid candidates: none found
CT18NLO member grids: 59 present
LHAPDF_DATA_PATH for repo CT18NLO:
  /usr/share/lhapdf/LHAPDF:$PWD/scripts/data/pdf
real_lhapdf_run_possible: true
```

Therefore the local tooling obstruction is resolved for CT18NLO. The lane still
does not promote, because the accepted Drell-Yan/PDF convention authority and
provider provenance remain absent. The CT18 run remains an equivalent-table
candidate parse until those authority fields are supplied.

The local grid is parsed. The parsed packet records a candidate Drell-Yan
parton-luminosity/bin-integration convention:

| Field | Local candidate value |
|---|---|
| kind | rapidity-window Drell-Yan light-quark luminosity |
| formula | `dlog(x1)` integral of charge-weighted `q qbar + qbar q` |
| mass windows | `50-76`, `76-106`, and `106-170 GeV` |
| scale | `Q = dilepton mass` at each integration point |
| collider energy | `sqrt_s = 13000 GeV` |
| rapidity/eta cut | `eta_cut = 2.4` |
| quadrature | `n_x = 200`, `n_m = 80`, trapezoid in `log(x1)` then mass |
| flavours | `u,d,s` with charge weights `4/9,1/9,1/9` |
| table convention | LHAPDF `lhagrid1` stores `x*f(x,Q)`; extractor divides by `x` |

This candidate convention is bound to local DASHI projection artifacts only as
provenance:

```text
scripts/data/outputs/t43_projection_v4.json
scripts/data/outputs/t45_projection_v4.json
```

Both projection JSON files are local diagnostic artifacts with `18` bins. This
binding does not make the CT18 convention accepted, does not supply a
provider-to-runner conversion law, and does not promote W4 or W5.

## Negative Local Probes

The local CT18NLO probes are negative diagnostics only:

| Probe | Local result | W5 target | Status |
|---|---:|---:|---|
| fixed-`x = 0.01` u-quark `xfxQ` ratio | `1.0506681065158017` | `0.8804486068` | fails target |
| rapidity-window `t45/z_peak` | `0.7514043986785174` | `0.8804486068` | fails target |
| rapidity-window `t45/t43` denominator hypothesis | `0.3348750784006896` | `0.8804486068` | denominator-fix hypothesis rejected |
| corrected full-`x` `dL/dtau` mass-window `t45/z_peak` | `0.9931829614316737` | `0.8804486068` | fails target |

The locally recorded `t45/t43` absolute gap is
`0.5455735283993104`; the locally recorded `t45/z_peak` absolute gap is
`0.12904420812148265`.

W4/W5-convention reran the corrected full-`x` DY luminosity diagnostic with
system LHAPDF and:

```text
LHAPDF_DATA_PATH=/usr/share/lhapdf/LHAPDF:$PWD/scripts/data/pdf
```

The diagnostic script is:

```text
scripts/run_w4w5_ct18_corrected_dy_luminosity.py
```

The artifact is
`logs/research/w4w5_ct18_corrected_dy_luminosity_20260513.json`, SHA-256
`34d4a317d29b23a39e6d0b865028ba8640059123371dddfdf443e4b0e8ec43a8`.
It computes the convention
`dL/dtau = integral_tau^1 dx/x sum_q e_q^2 [fq(x,M) f_qbar(tau/x,M) + reverse]`
with `sqrt_s = 13000 GeV`, `Q = M`, and `u,d,s` charge weights. The natural
`dtau` mass-window correction factor `L(106-170)/L(76-106)` is
`0.9931829614316737`, with absolute gap `0.1127343546316737` from target
`0.8804486068`; the diagnostic-only `dM` window ratio is
`0.6738009474587482`, and the center-point `dL/dtau(134.24)/dL/dtau(91.2)`
ratio is `0.3259929663173275`.

These results do not authorize another denominator tweak. They sharpen the
missing provider item: an accepted parton-luminosity and mass-bin integration
convention with provenance.

## W4 Z-Peak Adequacy Status

The local dirty Z-peak path is present and negative:

| Field | Local value |
|---|---|
| measurement | `scripts/data/hepdata/ins2079374_phistar_mass_76-106_t21.csv` |
| covariance | `scripts/data/hepdata/ins2079374_Covariance_phistar_mass_76-106_t22.csv` |
| measurement bins | `18` |
| covariance shape | `18 x 18` |
| shape callable | `DASHI.Physics.Prediction.sigma_dashi:predict_dirty_z_peak_shape` |
| fitted scale | `230534508.31238452` |
| chi2/dof | `298.8462841768543` |
| projection digest | `7fa002539fef1dc9bd51b22c1d512b4ed7be85417a3afb6f1e9992bbdc3dbdc1` |
| run artifact | `logs/research/w4_z_peak_anchor_dirty_run_20260513.json` |
| run artifact SHA-256 | `c8db3b690edcd1b4a792cd772651c5d018d04275d2163007fec7bee6a50a0ada` |
| public intake log | `logs/research/w4_z_peak_t21_t22_public_intake_20260513.json` |

This is an inadequate dirty shape-fit diagnostic. It does not construct a
W4 Z-peak adequacy receipt and does not decide or promote W4 under the newer
accepted-DY authority harness.

The 2026-05-13 public-route audit resolved DOI JSON-LD for:

- `10.17182/hepdata.115656.v1/t21` -> `https://www.hepdata.net/record/129900`;
- `10.17182/hepdata.115656.v1/t22` -> `https://www.hepdata.net/record/129901`.

From this environment, the title and numeric HEPData JSON/CSV download routes
returned HTTP 403. The runner therefore used the existing local t21/t22 CSV
payloads, checksum-bound in the intake log and provider-input manifest.

The current W4 adequacy harness blocks before calculation without an accepted
DY authority packet and accepted per-bin luminosity vector. Its recorded gate is:

```text
missingAcceptedDYLuminosityConventionAuthority
missing accepted luminosity vector ell_i per bin from a real accepted provider packet
```

No local `logs/research/w4_z_peak_adequacy_decision*.json` artifact is
evidenced in the inspected status document.

## Exact First-Missing Provider Authority

The first missing provider authority is not just a PDF file or a numeric ratio.
An accepted or replacement provider response must bind all of the following:

| Required field | Required authority content |
|---|---|
| PDF set | accepted family and version, such as CT18/MSHT/NNPDF or equivalent |
| LHAPDF id | exact set/member id or equivalent provider table identifier |
| grid checksum | checksum for every grid/table artifact used |
| scale convention | factorization/renormalization rule, including whether `Q = M` is accepted |
| rapidity convention | boson/lepton rapidity or eta acceptance and integration range |
| mass-bin rule | integration rule for `50-76`, `76-106`, and `106-170 GeV` |
| flavour weights | Drell-Yan channel sum, charge weights, symmetrisation, heavy-flavour treatment |
| interpolation/integration | PDF interpolation and numerical quadrature method |
| source | DOI, arXiv id, manual page, collaboration/publication source, or provider documentation |
| provenance | provider identity, command/API, input paths, checksums, timestamp, and no-manual-overfit attestation |

For downstream adapter ingestion, provider luminosities must also include
positive finite `L43`, `L45`, and W4 per-bin luminosities aligned to the
Z-peak bins, or a complete accepted replacement shape carrying the same
authority fields.

## LHAPDF-6 External Intake Contract

The W5 PDF intake surface now names the LHAPDF-6 / equivalent-table contract:

- LHAPDF-6 runtime route or equivalent table reader with version recorded;
- CT18NLO candidate set `14400`, or an accepted replacement;
- MSHT20 exact LHAPDF set id/version/member, if used instead;
- central member and uncertainty/error-set prescription;
- `.info` and every consumed member-grid checksum;
- `xfxQ` / `xfxQ2` convention and whether the table stores `x*f(x,Q)`;
- interpolation and extrapolation policy over `x` and `Q`;
- alphaS, perturbative order, and flavour-scheme convention;
- Drell-Yan parton-luminosity formula and normalization;
- mass-window integration for `50-76`, `76-106`, and `106-170 GeV`;
- rapidity or eta acceptance convention;
- charge weights, symmetrisation, and heavy-flavour policy;
- conversion law to W4 `ell_i` and W5 `L43/L45` runner inputs;
- provider provenance and no-manual-overfit attestation.

Without that payload, the local CT18NLO parse remains a candidate diagnostic
and cannot become a PDF authority or W5 correction receipt.

The pressure tool now reports these runner inputs separately under:

```text
inputs.authority.runnerLuminosityDiagnostics.L43.positiveFinite
inputs.authority.runnerLuminosityDiagnostics.L45.positiveFinite
inputs.authority.runnerLuminosityDiagnostics.W4_per_bin_luminosities.allPositiveFinite
```

All three must be true before convention/bin-normalization pressure can be
separated from PDF/model pressure.

## Not Locally Evidenced

- A real external/provider `accepted` or `replacement` DY authority packet is
  not locally evidenced.
- A W4 Z-peak adequacy pass under an accepted DY luminosity convention is not
  locally evidenced.
- A CSS momentum-space/qT dirty Z-peak artifact at chi2/dof approximately `65`
  is not locally evidenced; the local diagnostic binds the dirty Z-peak
  chi2/dof to `298.8462841768543`.
- A W5 correction pass at `0.8804486068` under accepted convention authority is
  not locally evidenced.

## Sources Inspected

- `TODO.md`
- `Docs/AcceptedDYLuminosityConventionAuthorityProviderPacket.md`
- `Docs/AcceptedDYLuminosityConventionAuthorityResponse.md`
- `Docs/DYAuthorityProviderResponseChecklist.md`
- `Docs/DYAuthorityProviderResponseStatus.md`
- `Docs/W4ZAdequacyDecisionStatus.md`
- `DASHI/Physics/Closure/W4W5AcceptedDYLuminosityConventionDiagnostic.agda`
- `DASHI/Physics/Closure/W4W5PDFSharedDependencyDiagnostic.agda`
- `DASHI/Physics/Closure/W5CT18ExternalIntakeReceipt.agda`
- `DASHI/Physics/Closure/W4ZAdequacyReceipt.agda`
- `DASHI/Physics/Closure/W4ZPeakCalibrationAnchorReceipt.agda`
- `scripts/data/pdf/ct18_dashi_pdf_packet.json`
- `logs/research/dy_authority_adapter_smoke.json`
- `logs/research/accepted_dy_authority_adapter_blocked.json`
