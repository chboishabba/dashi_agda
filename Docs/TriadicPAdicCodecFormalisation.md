# Triadic p-adic codec formalisation

## Status

This document is the prose companion to:

- `DASHI.Codec.TriadicPAdicCodec`
- `DASHI.Codec.TriadicPAdicCodecRegression`

The implementation is intentionally split along the repository's existing
proved/bridge boundary. Finite trit-carrier, inversion, sheet-lift, and
support/sign facts are constructive. Lossless codec, entropy-coder, p-adic
cylinder, MDL-selection, packing-decoder, asymptotic-rate, and hardware claims
are represented by typed contracts unless the required witness is already
present in the repository.

The module explicitly reuses these existing surfaces rather than introducing a
parallel formalism:

- `DASHI.Algebra.Trit`
- `DASHI.Foundations.SurrealCompactificationBalancedTernaryEmbedding`
- `DASHI.MDL.MDLLyapunov`
- `DASHI.Physics.Closure.W9MDLTerminationSeamRoute`

## 1. Carrier and sheet algebra

The canonical alphabet is the existing carrier:

\[
T = \{-1,0,+1\}.
\]

A kernel of order `d` is represented by a length-indexed vector:

\[
\mathcal K_d = T^d.
\]

A sheet is `T²`, and the nine-lift prefixes one sheet to a kernel:

\[
\operatorname{lift}_9 : T^2 \times T^d \to T^{d+2}.
\]

The Agda implementation proves the lift shape definitionally and proves that
componentwise inversion commutes with the lift. It also proves that kernel
inversion is involutive by reusing `DASHI.Algebra.Trit.inv-invol`.

The cardinality readings `|T^d| = 3^d` and `|T^{d+2}| = 9|T^d|` remain prose
interpretations until connected to a finite-cardinality library surface.

## 2. Support/sign factorisation

The per-trit fold is implemented as the exact finite isomorphism:

\[
-1 \leftrightarrow \operatorname{signed}(-),\qquad
0 \leftrightarrow \operatorname{zeroFold},\qquad
+1 \leftrightarrow \operatorname{signed}(+).
\]

Both round trips are proved:

\[
\operatorname{unfold}(\operatorname{fold}(t)) = t,
\qquad
\operatorname{fold}(\operatorname{unfold}(f)) = f.
\]

This is the exact formal content behind the mask/sign representation:

- a Boolean support mask,
- a sign symbol only on support,
- zero as the fixed point of inversion.

The higher-kernel global inversion quotient is represented by the proved
involutive action. Orbit counting (`9 -> 5`, `27 -> 14`) is not silently claimed
as a theorem in this tranche because a finite quotient/cardinality carrier has
not yet been attached.

## 3. Five-trit packing

The module defines the base-three encoder

\[
\operatorname{encode}_5(t_0,\ldots,t_4)
= c(t_0)+3(c(t_1)+3(c(t_2)+3(c(t_3)+3c(t_4))))),
\]

where `c(-1)=0`, `c(0)=1`, and `c(+1)=2`.

This yields values in the intended `0..242` range, corresponding to
`3^5 = 243 <= 256`. The current module deliberately exposes the executable
decoder and bounded-byte proof as `Pack5Contract`; it does not identify an
unbounded Agda `Nat` with a byte.

## 4. Ambient p-adic space and cylinders

The mathematical ambient space is:

\[
\mathcal X = (\mathbb Z_3)^{\Omega\times\mathcal T}.
\]

Residual refinement is represented by `CylinderSystem`, containing:

- a residual carrier,
- a depth-indexed cylinder carrier,
- projection to depth `k`,
- a refinement map from depth `k+1` to `k`,
- the compatibility law
  \[
  \operatorname{refine}_k(\pi_{k+1}(r)) = \pi_k(r).
  \]

The repository already contains a checked finite balanced-trit embedding in
`SurrealCompactificationBalancedTernaryEmbedding`. The codec module imports and
cross-references that surface, but keeps integer residual expansion abstract
because the existing embedding targets its own bounded rational/tower carrier.
A later adapter should connect the codec residual integer carrier to that
existing finite tower instead of duplicating it.

## 5. Causal predictor family

A video carrier supplies pixel, sample, and frame types. A chart at time `t`
contains:

- a past-information carrier,
- an explicit obligation that it contains only earlier frames,
- a block partition,
- per-block lag,
- warp family and parameter,
- a deterministic predictor.

This is the typed counterpart of the filtration condition

\[
\theta_t \text{ is } \mathcal F_{t-1}\text{-measurable}.
\]

The module does not claim that every record inhabitant is causal merely because
it is named `CausalChart`; causality is carried by the
`pastContainsOnlyEarlierFrames` obligation and must be discharged by a concrete
implementation.

## 6. Residual planes and losslessness

`ResidualCodec` requires:

1. subtraction and residual addition,
2. the roundtrip
   \[
   p + (x-p) = x,
   \]
3. a depth-indexed plane decomposition,
4. an assembly operation,
5. the exact plane/assembly roundtrip.

`MatchedEntropyCoder` separately requires the encode/decode roundtrip for a
symbol list under shared deterministic contexts.

`LosslessCodecReceipt` then packages the final theorem shape:

\[
\operatorname{decode}(\operatorname{encode}(x)) = x.
\]

This separates structural losslessness from any claim about compression ratio.

## 7. MDL collapse

The ambient function tower over the nine-object is an interpretation of the
unstructured hypothesis space:

\[
F_0=T^2,\qquad F_{n+1}=F_n^{F_n}.
\]

The implementation does not enumerate this tower. `MDLChartSelection` instead
requires:

- a structured chart carrier,
- a description-length carrier,
- an ordering relation,
- a selected chart,
- a proof that the selected chart is no longer than every candidate.

This is compatible with `DASHI.MDL.MDLLyapunov`, which is imported as the
existing MDL functional spine, and with the accepted W9 termination seam route.
The codec bridge does not reinterpret the W9 theorem as a video-codec
optimality theorem.

## 8. Physical representation

`PhysicalCodecLayout` exposes the implementation-facing streams:

- support-mask words,
- sign words on support,
- packed-trit fallback words,
- side-information words,
- a deterministic decode order.

This reflects an efficient CPU/GPU/ASIC layout without claiming a measured
speedup. A concrete backend should provide:

- bounded machine-word carriers,
- vectorized mask extraction,
- prefix/popcount addressing for conditional signs,
- deterministic warp sampling,
- matched rANS/arithmetic coding,
- cache and bandwidth measurements.

## 9. Rate model and empirical boundary

The useful engineering approximation remains

\[
r \approx r_{\mathrm{side}} + \log_2(3)\sum_k \rho_k,
\]

where `rho_k` is measured active-trit density at plane `k`.

This equation is not currently a theorem of the Agda module. Exact realized
entropy length depends on contexts, model mismatch, headers, finite coder state,
and sign distribution. `EmpiricalRateReceipt` therefore requires the measured
sequence, per-plane density, side rate, achieved rate, comparison target,
measurement protocol, and lossless/lossy mode.

The canonical boundary explicitly leaves these false:

- executable `pack5` decoder proved here,
- asymptotic side-information collapse proved here,
- entropy optimality proved here,
- AV1 superiority proved here,
- physical silicon speedup proved here.

## 10. Next closure steps

The most productive follow-ons are:

1. connect `FiveTrits` to the repository's bounded byte/`Fin 256` carrier and
   prove `encode5 < 243`, injectivity, and decoder roundtrip;
2. define a finite balanced residual tower adapter reusing
   `SurrealCompactificationBalancedTernaryEmbedding`;
3. instantiate `ResidualCodec` for bounded integer samples;
4. instantiate `MatchedEntropyCoder` for an executable reference coder;
5. prove a full causal frame encode/decode receipt;
6. ingest measured plane-density and side-bit receipts from codec experiments;
7. only then compare achieved bpppf, throughput, energy, and quality against a
   specified AV1 mode and implementation.
