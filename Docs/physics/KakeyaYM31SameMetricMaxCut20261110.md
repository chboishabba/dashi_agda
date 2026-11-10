# Kakeya × Yang–Mills / TSVF–KK (3,1): same-object maximum cut
Date: 2026-11-10

## Actual existing owner discovered

PR #1460 (`research/lorentz31-directional-kk-ym-20261103`, inspected head `ed4cd2edf5f9692f015dca7cf1e5439b5eb87ebb`) is **stacked on** the 2026 Voyager Yang–Mills PR #1444. It contains significantly more than the older selected flat integer signature receipt:

- `Lorentz31DirectionalProbeExact`: four observed principal directions + one arrow + source calibration imply three spatial and one temporal sign. Not an independently inhabited physical source.
- `YMClayLorentz31DirectionalKKHodgeExact`: signed two-form Hodge `*²=-1` for selected Lorentzian basis, contrasting the existing Euclidean `*²=+1`. Its `SameSourceKKYMContinuation` is physical input, not an implemented 5D solution.
- `TSFVKKSameArrowQuadraticMetricWeldExact`: actual selected axis equality between original observed TSFV probe and the KK direction given `SameMetricTSFVKK`.
- `TSFVKKActualSelectedMetricHorizontalWeldExact`: exact 5D horizontal bilinear = original selected measured observer 4D bilinear, **conditional** on the physical five-metric/Kaluza–Klein form and actual observed/four-metric equality.

This stacked branch is not merged on `master`. Accordingly, the present Kakeya/YM child branch is based directly on #1460 and does not invent a duplicate source. Separate Kakeya PR #1485 remains on its own branch; do not merge unrelated dirty trees or pretend its modules are in this branch.

## New precise weld

`DASHI.Physics.Foundations.KakeyaYMSelectedSpatialMetricWeldExact` uses the actual #1460 theorem

`Actual.selectedKK5HorizontalIsActualObservedBilinear`

and the original same-arrow theorem

`TimeAxis.samePhysicalObserverAndKKTimeAxis`

to provide:

- `sameKKHorizontalSpatialGram`: for selected *spatial* tangents, the horizontal bilinear of the SAME physically selected KK 5D metric equals a supplied selected Euclidean-spatial Gram after coordinates, if the observed bilinear is proved to equal it.
- `sameKKSpatialGramAndOriginalArrow`: the same spatial Gram equality together with the exact original observer/KK time axis equality.

The `isSpatial` predicate prevents incorrectly demanding an indefinite Lorentzian form be positive Euclidean on *all* four dimensions. There is no synthetic witness of observer-selected geometry, no independent 31-coded input, and no actual Euclidean metric identification constructed here. The theorem is a source-level conditional composition whose input corresponds to an original physical geometric question.

## Mathematical and formal attribution

- Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions* (2025), https://arxiv.org/abs/2502.17655.
- Larry Guth, Hong Wang and Joshua Zahl, *A streamlined proof of the Kakeya set conjecture in R3* (2026), https://arxiv.org/abs/2601.14411.
- Project Numina and Nankai/ByteDance Seed separately own the external unconditional Lean Kakeya proof; local `dashi_lean4` PR #106 provides a stand-alone source-pinned verification launcher, not another proof.
- Lorentz, Minkowski, Kaluza/Klein, Hodge, Wilson, Osterwalder–Schrader, Bałaban and DASHI's earlier source owners retain their separate mathematical and code attribution.

## Highest-alpha remaining ORIGINAL-object gates

| Gate | Exact mathematical proof payment | Status |
| --- | --- | --- |
| YK0 | Type-check this newly composed Agda source at exact head in Agda --safe | Not run; local Agda unavailable |
| YK1 | Physically instantiate `SameMetricTSFVKK`, `selectedFiveMetricIsActualKKForm`, `selectedObserverBilinearIsSameFourMetric` | Open |
| YK2 | Derive the genuine spatial tangent subbundle from the same observed arrow and prove orthogonal positive-definite restricted metric (not sign counts alone) | Open |
| YK3 | Construct original spatial coordinate chart/isometry with `EuclideanSpace ℝ (Fin 3)`, including appropriate real completion, scale and topology | Open |
| YK4 | Prove Lebesgue/Borel measure preservation or precise Jacobian bounds and tube/line-direction preservation | Open |
| YK5 | Verify pinned external unconditional Kakeya theorem locally via the independent source checkout; only transport the theorem to the physically selected geometry once YK1–YK4 hold | Open locally |
| YK6 | Keep 4D Euclidean YM Wilson/OS reconstruction, Hodge Wick continuation and Lorentzian physical metric source independent from Kakeya dimension | Open |

There is a natural conditional transport via a **distance-preserving bijection**, which preserves all Euclidean segment geometry and Hausdorff dimension. A mere `(3,1)` signature, arbitrary chart, or local metric equality on unspecified axes is insufficient. Arbitrary curved 3-dimensional spatial manifolds do not automatically inherit the global Euclidean Kakeya theorem without a separate chart/distortion/localisation argument.

## Verification and merge rules

Use local Nix/Agda 2.9; **no CI needed**. This was source-written and read against the inspected #1460 exact head; no Agda binary was available, hence this is **not** a kernel receipt. Prefer a stacked review and merge the original YM/TSFV donor branch before treating this file as a standalone master candidate.
