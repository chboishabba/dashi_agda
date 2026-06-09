# Clay Sprint Sixty Seven NS CKN Lemma/Test Ladder

Sprint 67 records the next honest NS route after the source-budget/action-
budget lane was exhausted: CKN/local critical concentration is the live norm,
and the proof route is now a lemma/test ladder.

## Route State

The route has three established diagnostic inputs:

```text
Sprint 64: source-budget route exhausted; CKN route opened.
Sprint 65: periodic zero-mean pressure reconstruction made CKN pressure usable.
Sprint 66: sampled pressure-inclusive hot spots decay under r-sweep zoom.
```

Sprint 66's favorable diagnostic is not a CKN theorem.  It says that the
sampled hot spots look like bulk turbulence under zoom, not like concentrating
singular candidates.

## CKN Quantity

The live quantity is the scale-normalized local concentration:

```text
C(r,x0,t0) =
  r^-2 integral_{t0-r^2}^{t0} integral_{B_r(x0)}
    (|u|^3 + |p|^(3/2)) dx dt
```

Raw enstrophy, raw positive vortex stretch, and packet action budgets are not
the promotion norm for this route.

## Lemma Ladder

| Lemma | Diagnostic/Test Contract | Current Status |
| --- | --- | --- |
| 0. Pressure reconstruction | Check Poisson residual, zero-mean gauge, finite pressure. | Diagnostically passed; keep as regression. |
| 1. Correct CKN quantity | Use `r^-2 integral (|u|^3 + |p|^(3/2))`. | Defined in Sprint 65/66 receipts. |
| 2. Decay under zoom | Compute CKN r-sweeps around candidate hot spots. | Favorable: 60/60 six-run, 10/10 N128, 10/10 dense N64 decay. |
| 3. Persistent ascension absent | Audit threshold exceedance across nearby radii, times, and resolutions. | Open. |
| 4. Candidate coverage | Audit raw-action, vorticity, velocity, pressure, large-C, and random classes. | Open. |
| 5. Riesz pressure control | Track pressure ratio and prove pressure is controlled by velocity up to localization terms. | Open and newly explicit. |
| 6. Suitable weak solution bridge | Measure local energy inequality residual and bridge to CKN suitable weak solutions. | Open and newly explicit. |
| 7. Uniform CKN epsilon bridge | Establish theorem-authorized epsilon bound, not a diagnostic threshold. | Open. |
| 8. Continuum/refinement stability | Compare dense cadence and N-ladder behavior. | Open. |
| 9. Conditional no-blowup | Conclude only if uniform CKN and suitable weak solution hypotheses are discharged. | Conditional only. |

## Sprint 67 Test Surface

Sprint 67A should expand candidate coverage:

```text
candidate_source
candidate_count
decaying_count
flat_count
concentrating_count
max_C_total
median_C_total
pressure_ratio_max
route_decision
```

Sprint 67B should add local energy residuals:

```text
cylinder_id
r
t
local_energy_residual
positive_residual_mass
max_positive_residual
route_label
```

Sprint 67C should replay compact summaries into this repo, not row-level CSVs.

## Route Labels

```text
CKN_UNIFORM_SAFE_ON_TESTED_GRID
CKN_DECAYS_BUT_EPSILON_UNCALIBRATED
CKN_PRESSURE_RATIO_BLOCKED
CKN_LOCAL_ENERGY_RESIDUAL_BLOCKED
CKN_CONCENTRATION_CANDIDATE_FOUND
```

## Governance

Sprint 67 is a proof-obligation ladder.  It preserves the Sprint 66 favorable
r-sweep evidence, but it does not prove CKN epsilon regularity, Riesz pressure
control, a local energy inequality bridge, suitable weak solution status,
continuum uniformity, no finite-time blowup, or Clay/NS promotion.
