# Triadic p-adic codec cross-pollination

## Status

This note accompanies:

- `DASHI.Codec.TriadicPAdicCodec369Bridge`
- `DASHI.Codec.TriadicPAdicCodec369BridgeRegression`

It records the narrow integrations that are constructive now and separates them
from analytic, empirical, and hardware claims that still require receipts.

## 1. Codec kernels and the existing 369 address geometry

The codec carrier uses the existing trit alphabet. A depth-`d` codec kernel is
therefore mapped into the existing `SSP369Ultrametric.Address d` carrier by

\[
-1 \mapsto 3,\qquad 0 \mapsto 6,\qquad +1 \mapsto 9.
\]

This is not a claim that codec digits are SSP primes or physical prime lanes. It
is a carrier-level adapter that reuses the repository's checked prefix geometry.
The codec's nested residual-plane interpretation and the existing address
ultrametric share the same finite-depth idea: longer common prefixes mean finer
agreement.

The bridge proves that every codec kernel has:

- a depth-preserving `369` address;
- a reflexive full-prefix witness;
- zero self-distance under `SSP369Ultrametric.distance`.

The analytic `3`-adic norm remains outside this bridge. The imported geometry is
a finite prefix ultrametric, exactly as its source module states.

## 2. Inversion becomes the existing 369 polarity action

Trit inversion

\[
-1 \leftrightarrow +1,\qquad 0\mapsto0
\]

is transported to

\[
3 \leftrightarrow 9,\qquad 6\mapsto6.
\]

The module proves that mapping a kernel after inversion is equal to applying this
`369` polarity action to the mapped address. This connects the codec's global
inversion quotient to the repo's existing polarity/stage language without
promoting an orbit-count theorem or a physical symmetry claim.

## 3. Nine-lift as two-digit prefix refinement

The codec sheet is `T²`. Prefixing one sheet to a depth-`d` kernel produces a
depth-`d+2` kernel. Under the `369` adapter, this is definitionally the same as
prefixing two `369` digits to the existing address.

Thus the phrase "triads within 9s" gains a checked geometric reading:

- one trit contributes one address digit;
- one nine-sheet contributes two address digits;
- repeated sheet lifts refine the prefix cylinder by two levels at a time.

This is the cleanest current connection between the codec's sheet algebra and
the repository's finite p-adic/ultrametric carrier stack.

## 4. MDL reuse rather than parallel MDL

`codecMDLFunctional` constructs the existing
`DASHI.MDL.MDLLyapunov.MDLFunctional` directly from:

- model/side bits;
- residual bits;
- total description length as their sum.

`NatMDLSelectionAdapter` then exposes the same data through the codec's abstract
`MDLChartSelection` interface. The adapter does not claim that the search
algorithm finds the global minimizer; it states exactly which minimality witness
a concrete search must supply.

The W9 termination seam remains a separate theorem about its own normalization
state. It motivates reuse of the MDL spine but is not reinterpreted as a codec
rate-optimality theorem.

## 5. Cross-pollinated implementation interpretation

The combined carrier picture is now:

1. predictor choice defines a causal chart;
2. residuals are decomposed into trit kernels/planes;
3. support/sign folding exposes sparse physical streams;
4. each finite kernel also has a `369` prefix address;
5. common-prefix geometry can classify reuse, dictionary candidates, or context
   neighborhoods;
6. MDL compares the side cost of those structures against residual savings.

This suggests a concrete implementation strategy: use the existing prefix
ultrametric as a deterministic candidate index, not as an exhaustive search.
Nearby addresses can propose shared contexts, dictionary entries, or warp/tree
reuse, while the actual acceptance rule remains measured description length.

## 6. Claims deliberately left closed

The canonical cross-pollination boundary records `false` for:

- an analytic `3`-adic norm theorem;
- an entropy-rate theorem;
- an AV1 comparison theorem;
- a physical throughput or energy speedup.

Those require, respectively, a suitable analytic carrier, a concrete probability
model/coder, reproducible benchmark receipts, and a specified hardware/backend
measurement protocol.

## 7. Next high-value integrations

The next narrow steps are:

1. use `kernel→369` as an index for context/dictionary candidate generation;
2. define a cylinder-refinement adapter whose projection depth is the shared
   prefix depth;
3. connect finite residual digit towers to the existing balanced-ternary
   embedding without conflating integer and bounded-rational carriers;
4. provide a bounded-byte `pack5` implementation and proof;
5. instantiate model/residual bit counts from an executable reference codec;
6. ingest empirical receipts for active-trit density, side cost, throughput, and
   energy before any comparison promotion.
