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

## W5 Observable Clarification

Typed clarification surface:

```text
DASHI.Physics.Closure.W5ObservableClarificationNote
```

The W5 carrier target `0.8804486068` is the older carrier
mass-integrated cross-section/PDF correction ratio. The CT18 and public
CMS-SMP-20-003 diagnostics currently available locally are different
observables: CT18 Drell-Yan luminosity probes, public `DSIG/DPHISTAR` ratio
integrals, public pT table integrals, and response-matrix-derived candidates.

Those diagnostics characterize the mismatch. They do not provide a proof
closure and must not be substituted for the W5 carrier observable unless an
accepted bridge supplies the missing conversion. W5a is parked pending the W4
acceptance/conversion correction; W5b is parked pending an accepted DY
luminosity convention. The exact remaining blocker is an accepted W4
phi-star-to-mass acceptance/conversion bridge or accepted DY luminosity
convention binding the CT18/public-CMS diagnostic observable to the older W5
carrier ratio.

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

## Public Phi-Star Response-Matrix Diagnostic

The CMS public YAML mirror also exposes the phi-star response-matrix tables
corresponding to submission documents `t68` through `t77`. The current runner:

```text
scripts/run_w4w5_hepdata_response_matrix_diagnostic.py
scripts/data/outputs/w4w5_hepdata_response_matrix_diagnostic.json
scripts/data/hepdata/ins2079374_response_phistar_t68_t77.sha256
```

records URL status, caches every consumed YAML payload, and binds all cached
payloads by SHA-256.

Direct HEPData YAML URLs attempted from CLI:

```text
https://www.hepdata.net/download/table/ins2079374/t68/yaml
...
https://www.hepdata.net/download/table/ins2079374/t77/yaml
https://www.hepdata.net/download/table/ins2079374/Table%2068/1/yaml
...
https://www.hepdata.net/download/table/ins2079374/Table%2077/1/yaml
```

All `20` direct HEPData YAML attempts returned `HTTP 403` / Cloudflare from
CLI in the 2026-05-13 run. The runner therefore used the CMS public YAML
mirror:

```text
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/submission.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/electron_response_phistar_mass_50-76.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/muon_response_phistar_mass_50-76.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/electron_response_phistar_mass_76-106.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/muon_response_phistar_mass_76-106.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/electron_response_phistar_mass_106-170.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/muon_response_phistar_mass_106-170.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/electron_response_phistar_mass_170-350.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/muon_response_phistar_mass_170-350.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/electron_response_phistar_mass_350-1000.yaml
https://cms-results.web.cern.ch/cms-results/public-results/publications/SMP-20-003/SMP-20-003_hepdata/muon_response_phistar_mass_350-1000.yaml
```

Current schema and extraction result:

| Diagnostic | Value |
|---|---:|
| Response YAMLs fetched from CMS mirror | `10 / 10` |
| Relevant W4/W5 windows (`50-76`, `76-106`, `106-170`) | `6` matrices |
| Matrix shape | `18 x 18` for every response table |
| Dependent variable | `P` |
| Independent variables | two phi-star bin axes |
| Direct HEPData CLI YAML success | `false` |
| CMS public mirror success | `true` |
| Looks like response/unfolding migration data | `true` |
| Direct central-value `A(M, phi*)` surface present | `false` |
| Column-sum candidate `A_col[j] = sum_i P[i][j]` computed | `true` |
| Column-sum candidate bounded in `[0,1]` with `1e-5` roundoff | `true` |
| Diagonal candidate `A_diag[j] = P[j][j]` computed | `true` |
| Diagonal candidate exactly bounded in `[0,1]` | `true` |
| Usable as W4/W5 bridge without typed receipt/gate consumer | `false` |

Candidate extraction summary:

| Channel | Mass | Column min | Column max | Column mean | Diagonal min | Diagonal max | Diagonal mean |
|---|---:|---:|---:|---:|---:|---:|---:|
| electron | 50-76 | `0.999994497000` | `1.000004934000` | `1.000000972222` | `0.82790` | `0.99849` | `0.921637777778` |
| muon | 50-76 | `0.999995100000` | `1.000004850000` | `0.999999599778` | `0.96268` | `0.99967` | `0.983527222222` |
| electron | 76-106 | `0.999995217870` | `1.000003388290` | `0.999998967347` | `0.85072` | `0.99824` | `0.927732222222` |
| muon | 76-106 | `0.999995356520` | `1.000004880000` | `1.000000840810` | `0.97034` | `0.99957` | `0.985763333333` |
| electron | 106-170 | `0.999995423000` | `1.000005425000` | `1.000001023086` | `0.86503` | `0.99836` | `0.934486111111` |
| muon | 106-170 | `0.999994320400` | `1.000004460000` | `0.999999917550` | `0.97522` | `1.00000` | `0.988531666667` |
| electron | 170-350 | `0.999996900000` | `1.000004278000` | `1.000000560894` | `0.88369` | `0.99788` | `0.945410555556` |
| muon | 170-350 | `0.999995297000` | `1.000004800000` | `1.000000026859` | `0.97653` | `0.99977` | `0.989388888889` |
| electron | 350-1000 | `0.999995641000` | `1.000004631000` | `1.000000156517` | `0.90681` | `0.99756` | `0.958693333333` |
| muon | 350-1000 | `0.999980898000` | `1.000003926000` | `0.999999022444` | `0.97844` | `1.00000` | `0.991503888889` |

Interpretation:

- `A_col[j] = sum_i P[i][j]` is now locally computed and checksum-bound for
  every cached `t68-t77` matrix.
- The column sums are numerically one within roundoff. That is consistent with
  a truth-bin-normalized migration matrix, so the column-sum extraction does
  not reveal an independent central acceptance-loss vector.
- `A_diag[j] = P[j][j]` is also locally computed and lies in `[0,1]`. It is a
  same-bin retention/purity candidate, not a full acceptance correction unless
  a W4 receipt or gate consumer explicitly accepts that convention.

Representative checksum-bound files:

| File | SHA-256 |
|---|---|
| `scripts/data/hepdata/ins2079374_submission.yaml` | `917a23b6c873c2acc623758cd6938c47f010da956a4d4fd9cbcda258632ed74c` |
| `scripts/data/hepdata/ins2079374_electron_response_phistar_mass_50-76.yaml` | `1dff609f908e3b3a8a6d9406bfc78795947d35aaba266de724dc52cb86399b41` |
| `scripts/data/hepdata/ins2079374_muon_response_phistar_mass_50-76.yaml` | `1c032b4c99bf961cebbae1a08772f0d6755575e65af2de0b715aef3dd6b8b6ea` |
| `scripts/data/hepdata/ins2079374_electron_response_phistar_mass_76-106.yaml` | `c8d769ec9996093d9bbe54f04552543977e9040b3dafb044f5ec9a2785fc352a` |
| `scripts/data/hepdata/ins2079374_muon_response_phistar_mass_76-106.yaml` | `52e1a96bfb4b514075956e6310e4dfff15102750fc0934c0121ced61956803b5` |
| `scripts/data/hepdata/ins2079374_electron_response_phistar_mass_106-170.yaml` | `8d6a510b651eb2a0b37595f902da4e95c11f474ec1f2fe2684df085acb13a009` |
| `scripts/data/hepdata/ins2079374_muon_response_phistar_mass_106-170.yaml` | `18dd807e13815ac08c1c756966a5a87a355367f263b2eef4128970529d1da8d5` |
| `scripts/data/outputs/w4w5_hepdata_response_matrix_diagnostic.json` | `366fe83fe4dae1d14ccb9ef3bd7a0858fa8baf9998fc8c96250c16bc4a748fdb` |

This confirms the public response matrices are fetchable through the CMS
mirror and are genuine square phi-star bin-migration/unfolding matrices. It
does **not** close W4/W5: the YAMLs expose `P` migration matrices, and the
two natural local extractions are now recorded, but no current typed gate
consumer accepts either extraction as the W4 `A(M, phi*)` bridge.

## W4 Diagonal Consumer Request

The current typed consumer request is:

```text
DASHI.Physics.Closure.W4DiagonalConventionGateConsumer
```

It accepts the diagonal extraction as the W4 convention-layer target without
promoting W4:

```text
accepted convention layer:
  A_diag[j] = P[j][j]
```

Explicit admissibility bounds are now bound from
`scripts/data/outputs/w4w5_hepdata_response_matrix_diagnostic.json`:

| Scope | Value |
|---|---:|
| W4-selected diagonal global min | `0.8279` |
| W4-selected diagonal global max | `1.0` |
| W4-selected diagonal global mean | `0.9569463888888888` |
| Selected windows | `50-76`, `76-106`, `106-170 GeV` |
| Diagnostic output SHA-256 | `366fe83fe4dae1d14ccb9ef3bd7a0858fa8baf9998fc8c96250c16bc4a748fdb` |

The accepted convention-layer electron/muon channel-combination law is the
geometric mean:

```text
A_geom[j] = sqrt(A_e,j * A_mu,j)
```

The accepted convention-layer covariance propagation law is the linearized
Jacobian rule for corrected observables:

```text
y_j = sigma_j / A_j
V_y = J V_x J^T
dy/dsigma = 1/A_j
dy/dA = -sigma_j/A_j^2
```

These are accepted only at the convention layer. The typed request still
records:

```text
diagonalAsAcceptanceConventionAccepted = true
diagonalAdmissibilityBoundsAccepted = true
electronMuonCombinationLawAccepted = true
covariancePropagationLawAccepted = true
internalAdequacyComputedPass = true
constructsW4ZAdequacy = false
constructsW4GateReceipt = false
```

The internal adequacy evidence added for this lane is deliberately
non-promoting:

| Field | Value |
|---|---:|
| Mass window | `76-106 GeV` |
| Channel combination | geometric mean diagonal convention |
| Combined diagonal efficiency | `0.9566` |
| Adequacy bound | `0.90` |
| Scaled decimal comparison | `9566 > 9000` |
| Boolean/string-layer pass | `true` |
| Constructs W4ZAdequacy | `false` |
| Constructs W4 gate receipt | `false` |

The exact remaining local blocker is the missing Agda numeric primitive:

```text
scaled-decimal strict inequality witness for 9566 > 9000
```

Until that primitive, a real `W4ZAdequacyReceipt`, and gate authority exist,
the internal pass is only computed evidence.

The exact remaining receipt condition is:

```text
W4ResponseMatrixAcceptanceReceipt =
  { sourceMatrices : SHA256-bound t68-t77 matrix set
  ; acceptedCandidate : Diagonal
  ; channelCombinationLaw : geometric mean electron/muon combination
  ; covariancePropagationLaw : linearized corrected-ratio Jacobian propagation
  ; internalAdequacyEvidence : non-promoting computed evidence for 0.9566 > 0.90
  ; provesGateBridge : candidate supplies the W4 A(M, phi*) bridge
  ; w4AdequacyConsumer : consumes the corrected observable and covariance
  }
```

## W4 Diagonal Convention Candidate Receipt

The typed local candidate receipt is:

```text
DASHI.Physics.Closure.W4ResponseMatrixAcceptanceCandidateReceipt
```

It binds the response-matrix diagnostic output checksum, the two candidate
formulae, and the W4-relevant diagonal mean values. It now accepts the
diagonal convention layer while remaining fail-closed at the W4 gate:

```text
selectedCandidateForGate = diagonalCandidate
channelCombinationRule   = geometricMeanElectronMuonCombination
constructsW4GateReceipt  = false
firstMissing             = missingW4ZAdequacyConsumer
internalAdequacyFirstMissing = missingScaledDecimalStrictGreaterThanPrimitive
```

The W4-relevant diagonal mean candidates are:

| Mass window | Electron diagonal mean | Muon diagonal mean |
|---|---:|---:|
| `50-76` | `0.9216377777777777` | `0.9835272222222221` |
| `76-106` | `0.9277322222222223` | `0.9857633333333333` |
| `106-170` | `0.9344861111111111` | `0.9885316666666666` |

These values are accepted as the same-bin retention convention layer. They do
not become a W4 promotion until a gate consumer accepts the resulting
corrected observable and covariance:

- W4ZAdequacy consumer over the corrected observable;
- pass/fail tolerance;
- promotion boundary connecting the convention layer to the W4 gate.

Until that receipt is consumed by the W4 gate, the result remains
`diagnostic_only = true`.
