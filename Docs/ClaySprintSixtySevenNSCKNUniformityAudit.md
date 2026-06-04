# Clay Sprint Sixty Seven NS CKN Uniformity Audit

Sprint 67B turns the Sprint 66 r-sweep result into a proof-facing uniformity
question.

Sprint 66 showed that sampled hot spots decay under zoom:

```text
six-run N32/N64: 60/60 decayed
N128 seed0:      10/10 decayed
dense N64 seed0: 10/10 decayed
pooled:          80/80 decayed
```

With zero observed concentrating failures in 80 sampled hot spots, the rough
95 percent Wilson upper bound on the true sampled failure rate is:

```text
failure_rate <= 0.0458
```

This is favorable diagnostic evidence, not theorem-zero.

## Calibration Signal

The fixed-block ascended fraction drops sharply under refinement:

```text
six-run N32/N64: 0.43666666666666665
N128 seed0:      0.116
absolute drop:   0.32066666666666666
relative drop:   0.7343511450381679
```

That supports the current interpretation: many coarse fixed-block ascensions
were calibration or bulk-turbulence effects, not persistent local CKN
concentration.

## Uniformity Audit

Sprint 67B audits candidate ascended cylinders, not just top hot spots.  The
output surface is:

```text
ns_sprint67_ckn_uniformity_by_cylinder.csv
ns_sprint67_ckn_uniformity_by_cluster.csv
ns_sprint67_ckn_uniformity_summary.json
```

Core fields:

```text
run
N
seed
time
x0,y0,z0
r
C_total
C_velocity
C_pressure
C_slope_vs_log_r
route_label
cluster_id
cluster_volume
cluster_persistence
pressure_fraction
velocity_fraction
```

Route decisions:

```text
CKN_UNIFORM_DECAY_SUPPORTED
CKN_LOCALIZED_PERSISTENT_PLATEAU
CKN_CONCENTRATION_CANDIDATE_FOUND
CKN_PRESSURE_DOMINATED_ARTIFACT
CKN_INCONCLUSIVE_NEEDS_HIGHER_N
```

Observed bounded six-run replay:

```text
route_decision = CKN_UNIFORM_DECAY_SUPPORTED
cylinder_count = 1536
cluster_count = 120
decaying_count = 1536
flat_count = 0
concentrating_count = 0
persistent_cluster_count = 0
pressure_fraction_max = 0.13074814940071125
max_C_total_N32 = 0.6157542190448191
max_C_total_N64 = 0.2939492011581624
max_ckn_grows_with_N = false
```

## Pass/Fail Shape

Pass shape:

```text
C(r) decreases under zoom for all or nearly all ascended clusters
cluster persistence is short
max_CKN does not grow with N
pressure fraction is bounded
```

Fail shape:

```text
one or more clusters persist across time
C(r) flat/growing as r decreases
max_CKN grows with N
pressure term dominates pathologically
```

## Governance

Sprint 67B does not prove CKN epsilon regularity.  It records favorable
bounded all-candidate replay evidence after favorable sampled r-sweeps.
Unbounded candidate coverage, theorem-level pressure control, N-ladder
stability beyond the tested artifacts, suitable weak solution bridge,
no-blowup, and Clay/NS promotion remain open.
