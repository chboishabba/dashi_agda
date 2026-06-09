# Clay Sprint Sixty Six NS CKN r-sweep Calibration

Sprint 66 calibrates the pressure-inclusive Sprint 64/65 CKN diagnostic by
sampling candidate hot spots over multiple radii.

## Diagnostic Quantity

```text
C(r, x0, t0) = r^-2 integral_Q(r,x0,t0) (|u|^3 + |p|^(3/2)) dx dt
```

The important observable is the r-sweep trend.  If `C(r)` decreases as the
audit zooms inward, the sampled point behaves like bulk turbulence rather than
a concentration candidate.  If `C(r)` grows under zoom, the sampled point is a
candidate concentration site.

## dashiCFD Results

Six-run N32/N64:

```text
route_decision = CKN_R_SWEEP_DECAYS_UNDER_ZOOM
hotspot_count = 60
ascended_fraction = 0.43666666666666665
decaying_hotspot_count = 60
concentrating_hotspot_count = 0
```

N128 seed0:

```text
route_decision = CKN_R_SWEEP_DECAYS_UNDER_ZOOM
ascended_fraction = 0.116
decaying_hotspot_count = 10
concentrating_hotspot_count = 0
```

Dense N64 seed0:

```text
route_decision = CKN_R_SWEEP_DECAYS_UNDER_ZOOM
ascended_fraction = 0.125
decaying_hotspot_count = 10
concentrating_hotspot_count = 0
```

## Governance

Sprint 66 is favorable diagnostic evidence: the tested pressure-inclusive hot
spots decay under zoom and do not behave like concentration candidates.

It is not a CKN epsilon-regularity theorem.  It does not prove a suitable weak
solution bridge, continuum-uniform bounds, no finite-time blowup, or Clay/NS
promotion.
