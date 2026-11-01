# Triadic mask/sign rANS formalism

## Status boundary

This tranche separates three kinds of claim:

- **proved finite structure:** exact reversible decompositions of `Trit³`;
- **typed implementation contract:** normalized finite rANS frequency/CDF tables;
- **empirical claims:** achieved bitrate, context-model gains, compute cost, codec comparisons, and patent status.

Only the first two are represented as checked Agda surfaces. Performance and legal claims remain external measurements or analysis.

## 1. Carrier

Let

```text
T = {-1, 0, +1}.
```

A three-trit word is an ordered element of `T³`, hence has 27 possible states.

## 2. Exact support/sign factorisation

Each trit factors as:

```text
trit = inactive
     | active negative
     | active positive.
```

For an ordered triple `u = (u₁,u₂,u₃)`, define the support mask

```text
mᵢ = 1 when uᵢ != 0, otherwise 0.
```

The mask belongs to `{0,1}³`, giving eight masks. A sign is present only at active coordinates. If `K` is mask Hamming weight, exactly `K` signs are carried.

The state count is therefore

```text
sum_{K=0..3} choose(3,K) * 2^K = 1 + 6 + 12 + 8 = 27.
```

`DASHI.Codec.TriadicMaskSign` implements this as a dependent payload and proves decoding after encoding for all 27 ordered states.

This is a change of coordinates, not compression by itself. It exposes support sparsity and sign bias to an entropy model.

## 3. Eight-mask histogram

For a uniform source over the 27 triples, each mask of weight `K` has `2^K` compatible sign patterns. Thus the exact structural counts are:

| mask | states |
|---|---:|
| `000` | 1 |
| each one-hot mask | 2 |
| each two-hot mask | 4 |
| `111` | 8 |

Grouped by weight, the histogram is `1, 6, 12, 8`.

For an empirical source, the production encoder should count the eight masks directly per plane/context rather than infer them from marginal trit entropies.

## 4. Global inversion fold

Global inversion acts by

```text
u -> -u.
```

The zero word is fixed and every nonzero word belongs to a two-element orbit. Therefore there are

```text
1 + (27 - 1)/2 = 14
```

orbits. `DASHI.Codec.TriadicGlobalInversionFold` explicitly defines the 14 canonical representatives, uses a gated polarity payload, and proves reconstruction for all 27 states.

This `14 + polarity` representation and the mask/sign representation are both bijective parameterisations. Neither can beat source entropy without a statistical model. Their practical difference is which dependencies they expose cheaply to the entropy coder.

## 5. Entropy identities

Let `U` be the triple, `M` its support mask, and `S` its gated sign payload. Since the mapping is bijective,

```text
H(U) = H(M,S) = H(M) + H(S | M).
```

If signs are conditionally independent and unbiased, then

```text
H(S | M) = E[K].
```

For a uniform 27-state source this recovers exactly

```text
H(U) = log2(27) = 3 log2(3).
```

There is no Shannon violation. Gains arise only when the actual source is non-uniform or context-predictable.

## 6. rANS model boundary

`DASHI.Codec.RANSMaskSignModel` provides a small production-facing model contract:

- 8-symbol support-mask alphabet;
- 2-symbol sign alphabet, emitted only for active slots;
- `ScaleBits = 12`;
- `TotalFrequency = 4096`;
- normalized frequency-table witnesses;
- a sparse cold-start mask table;
- a balanced cold-start sign table.

The cold-start mask symbol order is

```text
000, 001, 010, 100, 011, 101, 110, 111
```

with frequencies

```text
2610, 431, 431, 431, 61, 61, 61, 10
```

and CDF

```text
0, 2610, 3041, 3472, 3903, 3964, 4025, 4086, 4096.
```

These constants are a valid normalized initial model, not a claim that they are optimal for every channel, plane, clip, or context. Production tables should be trained from exact per-context counts and normalized deterministically.

## 7. Rate comparison rule

On the same empirical source, ideal entropy coding gives the same joint lower bound for:

- flat 27-symbol coding;
- 14-orbit plus gated polarity coding;
- 8-mask plus gated per-active signs.

Any measured rate difference comes from model class, context selection, finite-frequency quantization, stream framing, and implementation overhead. Mask/sign is expected to be attractive when support is sparse and local because it gives small alphabets and directly gated sign emission. Flat-27 may equal or beat it when a sufficiently strong 27-way context model captures all joint dependencies cheaply.

Accordingly, the repository does **not** promote a theorem that mask/sign is universally rate-optimal or universally faster.

## 8. Compute boundary

Fixed radix packing such as five trits in one byte costs `1.6` bits per emitted trit and has very low compute overhead, but it cannot exploit source bias.

rANS adds frequency lookup, state update, renormalisation, and context-selection work. The finite mask/sign alphabets are intended to keep this overhead small, but wall-clock performance is an empirical backend property. Python benchmark timings must not be read as production C/Rust/SIMD timings.

## 9. Modules

- `DASHI.Codec.TriadicMaskSign`
- `DASHI.Codec.TriadicGlobalInversionFold`
- `DASHI.Codec.RANSMaskSignModel`
- `DASHI.Codec.TriadicMaskSignRegression`
