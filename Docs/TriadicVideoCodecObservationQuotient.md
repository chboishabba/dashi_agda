# Triadic Video Codec Observation Quotient

This note records the DASHI-side formal surface for the sibling video codec
work in `../dashitest`.

The corresponding Agda module is:

```text
DASHI.Combinatorics.TriadicVideoCodecObservationQuotient
```

## Pipeline

The codec is represented as:

```text
frame stream
  -> predictor/chart
  -> signed residual
  -> balanced ternary planes
  -> magnitude/sign quotient
  -> block reuse orbit
  -> entropy payload
  -> deterministic decode
```

This matches the observed dashitest direction:

- signed frame residuals;
- balanced ternary digit planes;
- per-plane magnitude/sign quotienting;
- block reuse actions;
- side-information accounting;
- entropy payloads.

## Admissibility Rule

Compression alone is not enough.  A reuse or quotient is promotable only if:

- signed residuals are carried;
- balanced ternary expansion is exact;
- quotient masks are deterministic;
- reuse has equality or correction evidence;
- side information is counted;
- entropy model/header information is serialized;
- the decoder reconstructs deterministically;
- any residual defect remains explicit.

This imports the codec lesson into light transport: cached closure and reuse
are admissible only when the receipt and residual are part of the artifact.

## Validation

Focused check:

```text
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Combinatorics/TriadicVideoCodecObservationQuotient.agda
```

