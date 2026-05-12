# W4/W5 DY Convention Current Blocker

Date: `2026-05-12`
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

## Negative Local Probes

The local CT18NLO probes are negative diagnostics only:

| Probe | Local result | W5 target | Status |
|---|---:|---:|---|
| fixed-`x = 0.01` u-quark `xfxQ` ratio | `1.0506681065158017` | `0.8804486068` | fails target |
| rapidity-window `t45/z_peak` | `0.7514043986785174` | `0.8804486068` | fails target |
| rapidity-window `t45/t43` denominator hypothesis | `0.3348750784006896` | `0.8804486068` | denominator-fix hypothesis rejected |

The locally recorded `t45/t43` absolute gap is
`0.5455735283993104`; the locally recorded `t45/z_peak` absolute gap is
`0.12904420812148265`.

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
| projection digest | `36191efc92cb3c9b1641c9206171a307c4796369a4acd1485bf87d1051662b8b` |

This is an inadequate dirty shape-fit diagnostic. It does not construct a
W4 Z-peak adequacy receipt and does not decide or promote W4 under the newer
accepted-DY authority harness.

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
