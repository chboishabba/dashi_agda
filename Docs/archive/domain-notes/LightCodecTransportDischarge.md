# Light / Codec Transport Discharge

This note records the analogy boundary between the light-transport surface and
the triadic video codec surface.

The corresponding Agda module is:

```text
DASHI.Interop.LightCodecTransportDischarge
```

## Shared Pattern

Both lanes share:

```text
baseline or chart
  -> latent transform
  -> residual / defect
  -> admissibility gates
  -> deterministic reuse or replay
```

For video, the chart is a predictor and the residual is a signed balanced
ternary plane stack.  For rendering, the chart is a local physical transport
closure and the residual is a light-transport defect.

## Boundary

The discharge is analogy-only.  It does not claim:

- codec compression is light physics;
- light closure is a codec benchmark;
- reuse is valid without a receipt;
- residuals can be hidden;
- side information is free.

This gives the implementation target without over-promoting the analogy.

## Validation

Focused check:

```text
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Interop/LightCodecTransportDischarge.agda
```

