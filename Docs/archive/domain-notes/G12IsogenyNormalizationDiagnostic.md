# G12 Isogeny Normalization Diagnostic

Date: `2026-05-29`
Status: sector normalization derived; Cabibbo/CKM promotion still false

The raw isogeny-degree factor remains explicit:

```text
g12_raw = sqrt(3)/2 = 0.866025403784
```

The sector-angle normalization is the X0(4) modular volume:

```text
vol(X0(4)) = (pi/3)*psi(4) = (pi/3)*6 = 2*pi
g12_full = 2*pi*(sqrt(3)/2) = pi*sqrt(3) = 5.441398092703
```

The active numerical computation is

```text
alpha1 = sqrt(2.16/1270) = 0.041240603797
pi*sqrt(3)*sqrt(2.16/1270) = 0.224406542845
PDG |V_us| comparison value = 0.224500000000
absolute error = 0.000093457155
relative error = 0.041629 percent
```

`U1CMOrbitIntegralReceipt` now derives the p2-p3 sector-angle
normalization from vol(X0(4)).  This still does not promote the
Cabibbo angle: physical CKM diagonalisation and accepted PDG
authority binding remain open.

Governance flags remain:

```text
sectorAngleNormalizationDerived = true
angularNormalizedDiagnosticPromoted = true
cabibboAngleDerived = false
matchesPDG = false
cabibboPromotion = false
```

JSON payload:

```json
{
  "active_computation": "pi*sqrt(3)*sqrt(2.16/1270)",
  "cabibbo_angle_derived": false,
  "cabibbo_promotion": false,
  "candidate_normalized_g12": 5.441398092702653,
  "candidate_sector_angle_factor": 6.283185307179586,
  "candidate_sector_angle_normalization": "vol(X0(4)) = 2*pi",
  "diagnostic_absolute_error": 9.345715487699136e-05,
  "diagnostic_relative_error": 0.0004162902221692265,
  "diagnostic_vus": 0.224406542845123,
  "matches_pdg_promoted": false,
  "normalization_derived": true,
  "numerical_diagnostic": true,
  "open_formal_step": "physical CKM diagonalisation and PDG authority binding",
  "orbit_integral_denominator": 1270.0,
  "orbit_integral_numerator": 2.16,
  "orbit_integral_scale": 0.041240603797408244,
  "pdg_vus_target": 0.2245,
  "raw_isogeny_g12": 0.8660254037844386
}
```
