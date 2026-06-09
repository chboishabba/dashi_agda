# Clay Sprint 53 YM Diameter-1/2 KP Activity

Sprint 53 advances the Yang-Mills lane by adding an executable p=7
diameter-1/2 activity diagnostic before the all-diameter KP/Balaban gate.

Producer:

```bash
python scripts/ym_diameter_kp_activity_estimator.py \
  --out-dir Docs/Images/clay-analytic-sprint/sprint53_ym_diameter_kp_activity \
  --betas 6.0 7.69 10.13 13.64 16.7
```

Outputs:

```text
ym_diameter_kp_activity_table.csv
ym_diameter_kp_activity_checks.json
ym_diameter_kp_activity_manifest.json
```

## Activity Semantics

The harness emits two activity columns side by side:

```text
literal Wilson-defect diagnostic:
  z_literal(d) = |exp(-beta * c_min * d) - 1|

contour/action KP envelope:
  z_contour(d) = exp(a*d - beta*c_min*d)
```

This distinction matters. The literal Wilson-defect diagnostic tends to one at
large beta and is not a suppressive KP activity. The existing local YM receipts
use the contour/action envelope as the proof-facing suppression object.

For the unit single-plaquette convention `S_Wilson(square)=1`, the same issue
is sharper:

```text
|exp(-16.7)-1| ~= 0.999999944116686
8*|exp(-16.7)-1| ~= 7.999999552933488

exp(-16.7) ~= 5.588331392518267e-8
8*exp(-16.7) ~= 4.470665114014614e-7
```

So the carrier-scale KP pass belongs to the suppressive weight/envelope, not
to the literal `|exp(-beta*S)-1|` quantity.

## Measured Run

Constants:

```text
p = 7
BT branching factor = p + 1 = 8
c_min = 0.242
a = 0.5
```

Selected rows:

| beta | literal 8*z1 | contour 8*z1 | contour 7*z1 | status |
|---:|---:|---:|---:|---|
| 6.0 | 6.127187 | 3.087747 | 2.701778 | fails |
| 7.69 | 6.755839 | 2.051275 | 1.794866 | fails |
| 10.13 | 7.310658 | 1.136532 | 0.994466 | same-prime p clears, p+1 fails |
| 13.64 | 7.705194 | 0.486053 | 0.425296 | finite-prefix contour clears |
| 16.7 | 7.859417 | 0.231782 | 0.202809 | finite-prefix contour clears |

At the unit-plaquette literal convention, beta `16.7` also fails as a literal
Wilson defect:

```text
unit-plaquette literal 8*z1 at beta 16.7 = 7.999999552933488
unit-plaquette suppressive 8*exp(-beta) at beta 16.7 = 4.470665114014614e-7
```

Thresholds from this convention:

```text
same-prime p=7 threshold = 10.107066731633527
p+1=8 branch threshold  = 10.658849345784446
```

## Interpretation

The Sprint 53 run gives a conditional YM gain:

```text
beta = 16.7 clears the diameter-1/2 finite-prefix contour branch check.
```

It does not close the YM route because:

```text
literal Wilson-defect activity fails as a suppressive KP object;
unit-plaquette literal Wilson-defect activity also fails at carrier beta;
all-diameter KP is not certified;
actual KP incompatibility neighborhoods are not supplied;
Balaban RG scale transfer is not proved;
continuum YM, OS/Wightman, mass gap, and Clay promotion remain false.
```

The current best reading is:

```text
If Balaban RG legitimately transports the carrier to beta ~= 16.7, then
the diameter-1/2 contour/action prefix, and the unit-plaquette suppressive
weight, are safely subcritical. The load-bearing remaining gate is still
AllDiameterKPActivityBound plus Balaban transfer.
```
