# Triadic exploded-transform cross-pollination

This note records how the atomic/exploded-transform layer is integrated with existing DASHI formal surfaces rather than maintained as an isolated codec vocabulary.

## 1. Canonical ternary carrier

`DASHI.Foundations.SSPTritCarrier` is the repository's canonical typed `-1/0/+1` carrier. `DASHI.Geometry.TriadicExplodedTransformCrossPollination` supplies total maps between that carrier and the transform tower's executable trit type, proves both round trips, and proves that the maps commute with sign inversion.

This avoids a second ternary ontology: the local transform implementation may remain small, while all downstream semantic, Base369, odd-lane, polarity, and neutrality consumers can pass through the existing SSP carrier.

## 2. 369 prefix ultrametric

`DASHI.Geometry.SSP369Ultrametric` already proves an ultrametric on finite `3/6/9` addresses using common-prefix depth. The cross-pollination layer introduces two consumer receipts:

- `PrefixRefinementReceipt`: an address warp preserves common-prefix agreement depth;
- `AddressIsometryReceipt`: an address warp preserves the checked 369 distance.

It proves that prefix-depth preservation implies distance preservation. Thus an atomic or exploded transform may be called a symmetry of the existing 369 geometry only after supplying an explicit address action and the relevant preservation proof.

This is the precise bridge between:

- tree refinement / exploded local geometry;
- p-adic-style shared-prefix cylinders;
- and ultrametric invariance.

It does not identify image coordinates with SSP prime-lane addresses automatically. A domain adapter remains required.

## 3. Existing tree automorphisms

`DASHI.Geometry.SSP369TreeAutomorphism` proves that the existing prime-lane unit action commutes with prefix and preserves depth. The new layer keeps that theorem as a live dependency and treats it as the model shape for future exploded-transform address actions.

The two address carriers are intentionally not conflated. A later bridge may prove an embedding or quotient between a codec partition address and `Lane369Address`; until then, only the shared law shape is claimed.

## 4. Renormalisation tower

The exploded-transform tower packages scale systems and scale maps with two independent obligations:

1. coarse-graining commutes with ternary involution;
2. coarse-graining commutes with dynamics and transformed controls.

The cross-pollinated chart requires an actual `ScaleMap`. Metric preservation alone is not treated as sufficient to derive renormalisation compatibility.

## 5. MDL seam

`DASHI.Physics.Closure.W9MDLTerminationSeamRoute` is reused as the repository's accepted MDL/Lyapunov provenance surface. It proves a particular one-step canonicalisation route and remains explicitly non-pressure and non-Qcore.

The cross-pollinated chart records that route's current status but does not claim that every geometric or exploded-transform update decreases the same functional. Such a claim requires a chart-specific residual functional and a descent proof.

## 6. Resulting synthesis

The combined interpretation is:

> A DASHI geometric chart is a causal, finite exploded transform over a canonical ternary state field. Its local atoms commute with sign inversion; its scale maps must commute with dynamics and involution; and any claim that the chart preserves the p-adic/369 geometry must be discharged by a prefix or ultrametric receipt. MDL then selects among receipt-bearing charts by side cost plus residual cost, without turning approximation, physical adequacy, or bitrate superiority into axioms.

## 7. Deliberately open bridges

The following remain explicit future obligations:

- a typed codec-partition-address to SSP369-address adapter;
- affine parameter composition and inverse lemmas;
- conditions under which atomic supports are disjoint and order-independent;
- a piecewise-affine approximation theorem for a stated domain, metric, and regularity class;
- a chart-specific MDL descent theorem;
- empirical residual-density and bitrate receipts.

These are the correct places to deepen the formalism without broadening existing theorem claims.