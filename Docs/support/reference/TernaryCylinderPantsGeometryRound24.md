# Ternary Cylinder / Pants Geometry — Round 24

## Purpose

This tranche reconnects a concrete geometry that existed experimentally in the legacy `chboishabba/dashifine` repository with theorem-bearing structures that now exist in `dashi_agda`.

The legacy anchors are:

- `43_viz_ultrametric_tree.py`: ternary states, longest-common-prefix depth, induced ultrametric distance, and Euclidean visualization;
- `45_viz_tree_density.py`: explicit prefix-tree density from ternary lens addresses;
- the README gallery artifacts named `pants_example_fixed`, `generalized_pants_nw1_nl2`, `n_pants_with_seams`, and `nwaists_nlegs_pants`.

The theorem-bearing inputs are `SSP369Ultrametric`, `PadicCylinderLODReasoningField`, `RelationalBranchCobordismGeometry`, and the representation-geometry boundary in `FutureGeometryEmbeddingExact`.

## Intrinsic ternary tree

For `a : Address n` and `d : Digit369`, Round 24 defines `appendDigit a d : Address (n+1)`. For any two children of the same parent it proves

`PrefixMatch n (appendDigit a d1) (appendDigit a d2)`.

Thus the three child cylinders share the complete depth-`n` parent prefix independently of any Euclidean visualization.

## Exact pants indexing

The existing branch-cobordism carrier composes two `1 -> 2` junctions into an exact `1 -> 3` junction. Round 24 introduces `slot3`, `slot6`, `slot9` and exact two-way round trips

`Digit369 <-> BranchSlot`.

Those slots enumerate the three outputs of `composedOneToThree` in exact list order. The same finite three-element carrier therefore indexes both the child cylinders and the canonical pants outputs.

`CylinderPantsBridge parent` records the refined child, branch slot, and existing output channel for each digit. At depth one it directly reuses

`prefixTwoToOne (refineOne parent digit) = parent`.

## Discrete 3D observation

The existing `embedDepthThree : Address 3 -> Voxel3` is reused on the explicit depth-two parent `[3,6]`:

- `[3,6,3] -> voxel3 0 1 0`;
- `[3,6,6] -> voxel3 0 1 1`;
- `[3,6,9] -> voxel3 0 1 2`.

All three are proved to share the same depth-two ultrametric cylinder.

This is an extrinsic observation only. The formal boundary records that the voxel map is not claimed to be an ultrametric isometry, the p-adic fibre is not identified with a connected pants surface, and a smooth embedded thickening has not yet been constructed.

## Source boundary

Michael F. Atiyah, *Topological quantum field theory*, Publications Mathematiques de l'IHES 68 (1988), 175-186. DOI `10.1007/BF02698547`.

Atiyah supplies boundary/gluing/cobordism vocabulary only; no physical TQFT claim is imported.

## Next producer

The next high-alpha layer is genuinely geometric rather than another correspondence record:

1. recursively construct the finite ternary branch complex at arbitrary depth;
2. prove its depth-`n` frontier is indexed exactly by `Address n`;
3. construct a collision-free embedded graph in `R^3` preserving prefix ancestry;
4. thicken each trivalent junction to an oriented pants/tube patch;
5. prove gluing compatibility;
6. only then establish quantitative distortion bounds between intrinsic ultrametric and extrinsic graph/Euclidean metrics.
