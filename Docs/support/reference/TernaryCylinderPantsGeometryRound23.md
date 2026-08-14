# Ternary Cylinder / Pants Geometry — Round 23

## Purpose

This tranche reconnects a concrete geometry that existed experimentally in the legacy `chboishabba/dashifine` repository with theorem-bearing structures that now exist in `dashi_agda`.

The legacy anchors are:

- `43_viz_ultrametric_tree.py`: ternary states, longest-common-prefix depth, induced ultrametric distance, and Euclidean visualization;
- `45_viz_tree_density.py`: explicit prefix-tree density from ternary lens addresses;
- the README gallery artifacts named `pants_example_fixed`, `generalized_pants_nw1_nl2`, `n_pants_with_seams`, and `nwaists_nlegs_pants`.

The new theorem-bearing inputs are:

- `DASHI.Geometry.SSP369Ultrametric`;
- `DASHI.Biology.PadicCylinderLODReasoningField`;
- `DASHI.Reasoning.RelationalBranchCobordismGeometry`;
- `DASHI.Cognition.PNF.FutureGeometryEmbeddingExact`.

## 1. Intrinsic ternary cylinder tree

For an address

`a : Address n`

and a digit

`d : Digit369 = {3,6,9}`,

Round 23 defines arbitrary-depth refinement by appending one digit:

`appendDigit a d : Address (n+1)`.

For any two children of the same parent it proves

`PrefixMatch n (appendDigit a d1) (appendDigit a d2)`.

Therefore the three refined cylinders share the complete depth-`n` parent prefix. This is the intrinsic tree/cylinder fact. No Euclidean embedding is needed.

## 2. Exact three-way pants indexing

The existing `RelationalBranchCobordismGeometry` already composes two `1 -> 2` pants junctions into an exact `1 -> 3` junction.

Round 23 introduces three branch slots

`slot3`, `slot6`, `slot9`

and proves exact two-way round trips

`Digit369 <-> BranchSlot`.

The slots enumerate the existing three outputs of `composedOneToThree` in exact list order. Thus the same finite three-element carrier indexes both:

- the three child cylinders of one ternary prefix; and
- the three output channels of the canonical pants junction.

This is the first exact bridge between the old ternary tree and the pants construction.

## 3. Cylinder/pants commuting interface

`CylinderPantsBridge parent` records, for every ternary digit:

- the refined child cylinder;
- the corresponding branch slot;
- the corresponding existing pants output channel.

At depth one, the bridge directly reuses the existing theorem

`prefixTwoToOne (refineOne parent digit) = parent`.

So choosing one of the three output slots corresponds to choosing one refined cylinder, while forgetting the fine choice returns the original parent cylinder.

The structural square is therefore:

```text
parent cylinder
      |
      | choose digit 3/6/9
      v
refined cylinder  --------->  pants output slot
      |                              |
      | forget fine digit            | forget branch choice
      v                              v
parent cylinder  <---------  canonical 1->3 junction
```

The right-hand forgetful arrow is conceptual at this tranche: the canonical junction is the shared parent branching event, while each slot carries one child choice.

## 4. Discrete 3D observation

`PadicCylinderLODReasoningField` already provides

`embedDepthThree : Address 3 -> Voxel3`.

For the explicit depth-two parent `[3,6]`, Round 23 proves that its three children map to

- `[3,6,3] -> voxel3 0 1 0`;
- `[3,6,6] -> voxel3 0 1 1`;
- `[3,6,9] -> voxel3 0 1 2`.

All three are separately proved to share the same depth-two ultrametric cylinder.

This is a discrete extrinsic observation of one ternary branch in three-dimensional coordinates.

## 5. Important non-identifications

The formal boundary records all of the following explicitly:

- the ternary cylinder tree is formalized;
- the cylinder-to-pants slot correspondence is formalized;
- a voxel observation exists;
- the voxel map is **not** claimed to be an ultrametric isometry;
- the p-adic fibre is **not** claimed to be the connected pants surface;
- a smooth embedded pants thickening has **not** yet been constructed.

The intended architecture is therefore

```text
intrinsic totally-disconnected carrier
    ternary addresses
        -> cylinders
        -> ultrametric prefix tree

extrinsic connected realization
    branch slots
        -> 1->3 pants junction
        -> discrete 3D observation
        -> future smooth tube/pants thickening
```

The connected object is a realization/thickening of finite branching structure, not the identity of the p-adic fibre.

## 6. Source boundary

The pants/cobordism vocabulary continues to use:

Michael F. Atiyah, *Topological quantum field theory*, Publications Mathematiques de l'IHES 68 (1988), 175-186. DOI `10.1007/BF02698547`.

This source supports boundary/gluing/cobordism vocabulary only. Round 23 does not promote the finite relational carrier to a physical TQFT.

## 7. Next mathematical producer

The next high-alpha theorem is no longer another correspondence record. It is the geometric realization layer:

1. recursively construct the finite ternary branch complex at arbitrary depth;
2. prove its depth-`n` frontier is indexed exactly by `Address n`;
3. construct a collision-free embedded graph in `R^3` whose vertices preserve prefix ancestry;
4. thicken each trivalent graph junction to an oriented pants/tube patch;
5. prove gluing compatibility of adjacent patches;
6. only then ask for quantitative distortion bounds between intrinsic ultrametric distance and an extrinsic graph/Euclidean metric.

This separates topology, embedding, thickening, and metric distortion rather than silently identifying them.
