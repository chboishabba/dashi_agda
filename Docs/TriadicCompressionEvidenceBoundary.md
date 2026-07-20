# Triadic compression: formal and empirical boundary

## Purpose

This note records what the existing compression benchmark does and does not establish, and connects that result to the canonical ternary carrier already formalised in `DASHI.Foundations.SSPTritCarrier`.

The checked companion module is:

- `DASHI.Compression.TriadicCodecBoundary`

## Existing formal spine reused

The compression boundary does not introduce a competing trit representation. It reuses `SSPTrit = {-1, 0, +1}` from `DASHI.Foundations.SSPTritCarrier`, which already has total round trips to:

- `DASHI.Algebra.Trit.Trit`; and
- `Base369.TriTruth`.

The new module proves the exact ternary support/sign factorisation:

- `0` is represented by `zeroFactor`;
- `-1` is represented by an active support carrying `negativeSign`;
- `+1` is represented by an active support carrying `positiveSign`.

Both factorisation round trips reduce by computation. This is the precise form of the earlier statement that ternary admits an exact support/sign factorisation. It is not a claim that two independent binary bits are required or that base conversion alone compresses data.

## What the 600-frame benchmark established

The reported benchmark decoded 600 grayscale frames at `1280 x 720`, for `552,960,000` pixels. The relevant zlib-backed figures were:

| stream | rate |
|---|---:|
| raw grayscale bytes | 1.418 bits/pixel |
| temporal byte residual | 0.032 bits/pixel |

Thus the residual-plus-zlib stream was about `1.418 / 0.032 = 44.3` times smaller than zlib on the raw frame bytes.

That is strong evidence that the sample has very high temporal predictability and that residualisation exposes it effectively. It is not evidence that a ternary context coder caused the gain, because:

1. the source symbols were grayscale bytes, not `SSPTrit` values;
2. the transform was a byte-valued temporal residual;
3. `compression/rans.py` was a zlib wrapper rather than a real rANS implementation; and
4. no ternary action/context probability model was exercised.

The Agda witness `sixHundredFrameIsTemporalModelEvidence` therefore classifies the run as `temporalModelEvidence`.

## What counts as triadic evidence

The formal boundary distinguishes four levels:

1. `genericCompressionEvidence`: a generic backend compresses a generic source;
2. `temporalModelEvidence`: a temporal or canonical residual improves a non-ternary stream;
3. `triadicRepresentationEvidence`: the source is ternary, but the backend/context path does not yet establish a genuine ternary context codec;
4. `triadicContextCodecEvidence`: a ternary source is encoded with an explicit non-empty trit context and a real range/rANS backend.

This prevents a representation change, a useful predictor, and an entropy coder from being credited to one another.

## Minimum valid triadic benchmark

A benchmark may be described as testing the triadic codec only when it includes all of the following:

- source: action or cell-delta symbols in `{-1, 0, +1}`;
- exact reversible mapping to the canonical `SSPTrit` carrier;
- context model, beginning with previous trit and optionally adding `p_bad` and run-length buckets with backoff;
- a real range coder or rANS implementation rather than the zlib shim;
- encode/decode round-trip tests;
- bits per trit measured on the same logical stream against packed zlib and lzma baselines;
- model/header costs included in the reported byte count.

The checked `canonicalTriadicCodecValidationContract` records these requirements.

## Interpretation

The current honest conclusion is:

> The temporal modelling result is excellent: it improved the zlib result by about 44 times on the measured sample. The triadic codec itself remains unmeasured until the source, contexts, and entropy backend are genuinely ternary-aware.

This preserves the broader DASHI principle: useful compression comes from selecting a structured causal description and quotienting predictable redundancy, not from changing numeral base alone.
