# W4 Z-Peak Adequacy Receipt Template

Date: `2026-05-06`
Status: `template only; blocked; non-promoting`
Owner: `Laplace / W4 Z-peak adequacy lane`

This template prepares the W4 Z-peak adequacy path without deciding adequacy.
It is gated on an accepted Drell-Yan luminosity convention authority and real
per-bin inputs.

## Gate

Required order:

```text
AcceptedDYLuminosityConventionAuthority
-> scripts/run_w4_z_peak_adequacy.py
-> W4ZAdequacyReceipt
```

The current blocker is exact:

```text
missingAcceptedDYLuminosityConventionAuthority
missing accepted luminosity vector ell_i per bin
```

The existing dirty Z-peak shape diagnostic remains a baseline only:

```text
chi2/dof = 298.8462841768543
```

## Calculation

The runner implements:

```text
chi2(alpha) = sum_i ((m_i - alpha d_i ell_i)^2 / sigma_i^2)
alpha* = sum_i (m_i d_i ell_i / sigma_i^2) / sum_i ((d_i ell_i)^2 / sigma_i^2)
```

where:

| Symbol | Meaning |
|---|---|
| `m_i` | measured Z-peak bin value |
| `d_i` | dirty Dashi Z-peak shape prediction |
| `ell_i` | accepted Drell-Yan luminosity convention value for the bin |
| `sigma_i` | accepted per-bin uncertainty for the adequacy calculation |

## Runner Contract

Required command shape:

```text
python scripts/run_w4_z_peak_adequacy.py \
  --accepted-dy-authority accepted_dy_authority.json \
  --measurement-csv measurement.csv \
  --measurement-column m \
  --prediction-csv prediction.csv \
  --prediction-column d \
  --luminosity-csv luminosity.csv \
  --luminosity-column ell \
  --sigma-csv sigma.csv \
  --sigma-column sigma \
  --output w4_z_peak_adequacy.json
```

The authority JSON must contain:

```text
status
pdfSet
lhapdfId
gridChecksum
scaleConvention
rapidityConvention
massBinRule
flavourWeights
interpolationIntegration
source
provenance
```

`status` must be `accepted` or `replacement`.

## Fail-Closed Rules

The script exits before calculation when:

| Missing/invalid surface | Disposition |
|---|---|
| accepted DY authority JSON | blocked |
| required authority field | blocked |
| non-accepted authority status | blocked |
| measurement, prediction, luminosity, or sigma CSV | blocked |
| requested CSV column | blocked |
| non-finite value or non-positive sigma | blocked |

No fake adequacy artifact is emitted for missing inputs.

## Typed Surface

Agda mirror:

```text
DASHI/Physics/Closure/W4ZAdequacyReceipt.agda
```

The module defines `AcceptedDYLuminosityConventionAuthority` as constructorless
in this lane. `W4ZAdequacyReceipt` requires that authority field, so no promoted
receipt can be constructed here.

## Non-Promotion Boundary

This lane does not:

```text
accept the W4/W5 shared luminosity convention
claim the dirty Z-peak baseline is adequate
construct Candidate256PhysicalCalibrationAuthorityToken
construct Candidate256PhysicalCalibrationExternalReceipt
promote W4
```
