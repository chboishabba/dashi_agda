# Round Five junction and visualisation tranche

This tranche integrates the supplied sections 524–670 as finite exact Agda source.

## Connected three-to-two junction

`TriToBiSingularJunctionExact.agda` distinguishes a connected five-boundary event from a disconnected pair-of-pants plus cylinder. The finite topology table records:

```text
connected genus-zero 3 -> 2 presentation: three saddle channels, Euler -3
one ordinary saddle presentation: disconnected pants plus cylinder, Euler -1
```

The canonical ternary kernel has type `T x T x T -> T x T`, commutes with global sign involution, and includes explicit dependence witnesses showing that changing any input can change either output. The finite carrier is not promoted to a smooth singularity classification.

`TriToBiTransportExact.agda` separates joint-product mass from additive flux, gives two state-dependent conservative routing tables, and records storage, loss, and residual channels explicitly.

`TriToBiPhaseDialecticExact.agda` adds a three-point circle-phase analogue with common-rotation equivariance, a destructive-interference locus mapped to the ternary neutral state, and a joint dialectical balance `3 = 2 + 1`. Its phase carrier is explicitly not the full complex circle and its labels are not derived from topology alone.

## Affine slices and five-class display

`AffinePlaneSliceExact.agda` represents a finite affine slice by an origin and two directions in four coordinates. It checks axis-aligned and angled samples, origin-shift equivalence, basis-swap reparameterisation, four orientation degrees for `Gr(2,4)`, and two normal-offset degrees. The finite examples do not claim complete continuous Grassmannian coverage.

`FiveClassSimplexColourExact.agda` separates activity, validity, simplex composition, and display colour. It checks a denominator-ten five-class mixture, exhibits an explicit five-class-to-RGB collision, and distinguishes local PCA, global PCA, fixed palettes, and raw-channel panels. Common multiplicative attenuation leaves the declared normalised composition unchanged; class-specific attenuation can change it.

`SliceObjectiveExact.agda` implements distinct activity, entropy, class-coverage, active-area, spatial-variation, boundary, mixture-volume, and region-balance components. In the canonical table, activity alone selects the compact island while the combined objective selects the broad angled plane. The module also records shared atlas normalisation and the independent restriction, normalisation, and colour-projection losses.

`ColourProjectionDiagnosticsExact.agda` checks the intrinsic dimension mismatch `4 -> 3`, an explicit mixture collision, PCA sign and local-basis instability, global-basis stability, and reconstruction residuals hidden by identical RGB output.

## Renderer parity and search

`RendererParityExact.agda` gives separate reference, modular-vanilla, and optimised renderers, exact CMYK conversion, a fixed-slice quadratic-precomputation witness, streaming top-two parity, alpha modes, and evidence levels P0–P4. Visual similarity is not called float-buffer parity or a runtime benchmark.

`RendererReceiptExact.agda` records every renderer stage, semantic configuration, feature flags, buffer-level errors, property tests, timing protocol, performance summary, commit/configuration hashes, benchmark-executed state, and CI state. Its canonical source receipt deliberately has `benchmarkExecuted = false` and `ciKernelCheckSucceeded = false`.

`CoarseSliceSearchExact.agda` contains a concrete ranking counterexample in which a low-precision objective selects a compact island instead of the float winner. Adding active coverage repairs the finite example. The accepted architecture is int8 proposal, top-m retention, int32 accumulation, and float reranking.

`QuantisedSearchBoundsExact.agda` distinguishes preactivation and postactivation quantisation, exhibits clipping collisions, shows that per-plane calibration can reverse rankings, records near-tie instability and stable-margin preservation, rejects opposite-corner pseudo-bounds, supplies an integer-scaled Lipschitz cell bound, and retains the float winner in a top-three proposal.

## Graph and series adapters

`GraphSeriesSemanticExact.agda` uses semantic equivariance rather than pixelwise invariance for bars and graph relabellings, preserves line-series order, and blocks unsupported claims about local layout uniqueness or universal edge-distance monotonicity.

`MeasureFieldAdapterExact.agda` implements:

```text
source object -> finite measure -> smoothed field -> slice -> coarse image
```

The scaled convolution preserves source mass up to the declared kernel scale, is equivariant under a finite latent-location swap, and contains an explicit information-loss witness where distinct sources produce the same coarse image.

`AdapterCommutationExact.agda` checks exact bar relabelling and aggregation squares before rasterisation, distinguishes exact, lax, and undefined adapter laws, converts event and network values into finite measures, checks network-field mass, and demonstrates that equal-mass non-rigid embeddings can generate different fields.

## Provenance and authority

`AttachedVisualisationSourceAtlas.agda` records author, title, venue, year, DOI or explicit arXiv/no-DOI marker, imported role, and excluded promotion for eight source records covering Morse/cobordism theory, Stiefel/Grassmann geometry, PCA, GELU, integer quantisation, graph drawing, and UMAP.

The complete boundary is imported by `Round5CompleteBoundary.agda`, `DASHI/Physics/Foundations/Everything.agda`, and `DASHI/Unified/Everything.agda`. The source checker scans every new module and targets the visualisation regression and aggregate root. Kernel-checked or reproducible status is claimed only after the pinned Agda workflow succeeds.
