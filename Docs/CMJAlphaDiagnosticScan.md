# CM j Alpha Diagnostic Scan

Date: `2026-05-29`
Status: numerical diagnostic; non-promoting; no receipt flag changes.

This note records the first local numerical check requested after the Paper 8
freeze pass.  The calculation is intentionally weaker than a derivation.  It
verifies the classical anchors already recorded in
`DASHI.Physics.Moonshine.ModularJInvariantAlphaReceipt` and scans small
imaginary-quadratic CM points for naive normalized `j`-value separations near
the carrier diagnostics `alpha1 = 0.041240` and `alpha2 = 0.085720`.

The script is:

```text
scripts/cm_j_alpha_scan.py
```

The frozen output is:

```text
scripts/data/cm_j_alpha_scan_2026-05-29.json
```

## Result

The anchor check passed numerically:

| Anchor | Computed value |
|---|---:|
| `j(i)` | `1728.0 + 0.0i` |
| `|j(rho)|` | `3.0116454574113063e-44` |

The scan found nearby values under deliberately naive normalizations:

| Target | Nearest log-ratio CM discriminants | Value | Nearest pair-ratio CM discriminants | Value |
|---|---|---:|---|---:|
| `alpha1 = 0.041240` | `D=-155`, `D=-164` | `0.04123703959733996` | `D=-99`, `D=-143` | `0.04410567761228215` |
| `alpha2 = 0.085720` | `D=-68`, `D=-183` | `0.08572428867595441` | `D=-80`, `D=-168` | `0.08740490159196981` |

These numerical coincidences are not a carrier derivation.  They depend on the
choice of normalization and on a search over many CM pairs.  The required next
mathematical object is still a canonical map from modular or supersingular
geometry into the DASHI carrier alpha diagnostics.

## Governance

The following flags remain false:

```text
alphaDerivedFromModularGeometry = false
alphaOneDerivedFromModularGeometry = false
alphaTwoDerivedFromModularGeometry = false
alphaValuesPromoted = false
```

Allowed wording:

> A reproducible CM `j`-value scan found nearby values under simple
> normalizations, but the repository has not constructed a canonical
> `j`-to-alpha normalization map.

Prohibited wording:

> DASHI derives alpha from modular geometry.

> The CM scan proves the carrier alpha values.

> The modular-j bridge derives the Cabibbo angle.
