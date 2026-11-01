# NS shell/angle residence-time audit

The sparse physical carrier experiment showed that hundreds of thousands of leading transfer atoms still capture only a minority of gross packet activity.  This audit therefore works directly with the full shell/angle aggregate receipts rather than reconstructing another selected-mode carrier.

## Quantity evaluated

For each saved `raw_hat` checkpoint and target shell `K`, the script recomputes the full dealiased packet dissipation and evaluates

```text
Gamma_K(t) = max(full_packet_signed_rate, 0)
             / (2 * nu * full_packet_dissipation).
```

The signed rate comes from the exact Leray-projected aggregate exporter.  The dissipation is recomputed from the saved complex Fourier state using the same normalization and dyadic packet.

The shell/angle census also defines an explicit coarse tightness condition:

```text
sum gross_mass(p_offset,q_offset,angle)
    over |p_offset| <= radius and |q_offset| <= radius
    >= minimum_tightness.
```

Only checkpoints satisfying this declared tightness condition are eligible for the residence statistics.

## Run

First produce the full aggregate receipt:

```bash
python scripts/ns_triad_gamma_gap_raw_hat_export.py \
  --aggregate-only \
  --selection transfer \
  --state path/to/segment1_state.npz \
  --state path/to/segment2_state.npz \
  --target-shell 2 \
  --output-json /tmp/ns-full-aggregate.json
```

Then run the residence audit:

```bash
python scripts/ns_shell_angle_residence_audit.py \
  --input-json /tmp/ns-full-aggregate.json \
  --output-json /tmp/ns-shell-angle-residence.json \
  --gamma-thresholds 0.5,0.9,1.0 \
  --tightness-radius 1 \
  --minimum-tightness 0.8 \
  --pretty
```

For each trajectory and threshold the output reports:

- eligible and dangerous checkpoint counts;
- duration-weighted dangerous-set fraction;
- total and longest contiguous dangerous residence;
- the same residence in parabolic units;
- eligible-time average Gamma;
- integrated positive excess above the threshold.

Each checkpoint also reports shell/angle entropy, effective group count, largest-group mass, local-shell tightness, dissipation, and signed-to-gross cancellation.

## Interpretation

This implements the correct empirical abstraction after sparse carrier failure:

```text
full physical packet transfer
  -> shell/angle aggregation
  -> explicit packet tightness
  -> Gamma threshold set
  -> duration-weighted residence and persistence
```

It does **not** prove residence control between saved checkpoints, compactness of critical profiles, a cutoff-uniform Gamma gap, BKM continuation, or global regularity.  Every authority and promotion field remains false.
