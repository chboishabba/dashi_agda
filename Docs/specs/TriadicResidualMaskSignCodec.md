# Triadic residual codec: exact mask/sign factorisation

## Status

This document records a proved algebraic core and a separate implementation contract.

- **Proved in Agda:** the canonical DASHI trit `neg | zer | pos` is exactly equivalent to `inactive | active sign`; the equivalence lifts componentwise to 3-trit symbols; the projected support mask has eight forms; and the support-size state count is `1 + 6 + 12 + 8 = 27`.
- **Specified, not yet proved:** Shannon entropy identities over a canonical probability/real-number library, finite-precision rANS normalization and roundtrip correctness, and empirical rate claims.

The formal modules are:

- `DASHI.Codec.TriadicMaskSignFactorization`
- `DASHI.Codec.TriadicMaskSignEntropyContract`
- `DASHI.Codec.TriadicMaskSignSSPBridge`
- `DASHI.Codec.TriadicMaskSignRegression`

## 1. Source carrier

The codec reuses `DASHI.Algebra.Trit`:

\[
T = \{-1,0,+1\}.
\]

A residual sample may be represented across balanced-ternary planes as

\[
R = \sum_{k=0}^{K-1} S_k 3^k, \qquad S_k \in T.
\]

The present Agda tranche formalises each trit plane's symbol factorisation. It does not yet formalise integer reconstruction, uniqueness of a chosen finite balanced-ternary expansion, predictor semantics, or image/video continuity.

## 2. Exact support/sign factorisation

For one trit, define

\[
M = \mathbf 1_{S \ne 0},
\]

and, only on the active branch,

\[
\Sigma \in \{-1,+1\}.
\]

The Agda carrier is therefore

```text
inactive | active negative | active positive
```

with total encode/decode functions and both roundtrip laws. The inactive branch carries no dummy sign. This is the precise lossless factorisation; calling it “minimal sufficient” additionally requires a stated statistical model and is not promoted here as a theorem.

## 3. Three-trit symbols

For `u : T^3`, componentwise factorisation produces a support mask in

```text
000 001 010 011 100 101 110 111
```

and one sign for each active position. Grouping by active count gives

\[
\binom 3 0 2^0 + \binom 3 1 2^1 + \binom 3 2 2^2 + \binom 3 3 2^3
= 1 + 6 + 12 + 8 = 27.
\]

This establishes an exact 27-state decomposition. It does **not** identify `T^3` with an ordinary Cartesian product `Mask_8 × Sign^K` for one fixed `K`; the sign payload is mask-indexed/gated.

## 4. Entropy identity

For a single trit random variable, the correct chain-rule statement is

\[
H(S) = H(M) + \Pr(M=1) H(\Sigma \mid M=1).
\]

For a 3-trit symbol `U`, the corresponding exact statement is

\[
H(U) = H(\operatorname{mask}(U))
     + H(\operatorname{signPayload}(U) \mid \operatorname{mask}(U)).
\]

The conditional sign term need not split into independent sign bits unless the source model says so. Likewise, per-plane rates may be summed only under the coder's actual conditioning/model assumptions. `TriadicMaskSignEntropyContract` exposes these quantities as obligations rather than importing an unproved probability theory.

## 5. rANS production contract

The intended backend uses:

- an 8-symbol mask alphabet;
- a 2-symbol sign alphabet;
- sign emission only for active mask positions;
- per-plane tables, optionally split by one cheap context bit;
- `TOTFREQ = 4096`.

The current module records table shapes and claim boundaries. A later executable tranche should provide byte/state representations, normalized frequency proofs, encoder/decoder transition functions, stream-order conventions, and roundtrip tests against a reference implementation.

## 6. Comparison boundary

Mask/gated-sign coding can outperform fixed trit packing when the learned source distribution is sparse and the model cost is amortized. It is not automatically superior to every flat 27-symbol model: a fully adapted 27-symbol entropy model can represent the same joint distribution, while factorisation may win in table economy, generalisation, context sharing, and implementation cost. Empirical figures such as `4.8 -> 2.7 bits` require a digest-bound dataset and benchmark receipt before becoming repository claims.

## 7. Existing DASHI integration

`TriadicMaskSignSSPBridge` composes the factorisation with `DASHI.Foundations.SSPTritCarrier`, which already bridges the canonical `Trit` carrier to `TriTruth`/Base369. No parallel ternary alphabet is introduced. The codec reading remains an engineering/formal-algebra lane and does not promote SSP, p-adic, physical, biological, or perceptual semantics.
