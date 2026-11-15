# Conway / C3 / Karp max-cut: same-object strengthening

## Corrected K04

`DASHI.Core.TriadicClosureTower` defines

    TriadicCube = Trit -> Trit
    ThreeSuperThree = ThreeTowerCarrier 1
    ThreeTowerCarrier 1 = Trit -> Trit

Hence these two selected carriers are *definitionally equal*. The
new `ConwayC3SameObjectCodecExact.agda` proves this with `refl`.

The separate actual `C3CubeFourier27Exact.Cube3` is a triple of
`DepthWheelPhase`. It is not definitionally equal to `Trit -> Trit`
but is connected by explicit mutually inverse table maps:

- `cubeToTower : Cube3 -> ThreeSuperThree`;
- `towerToCube : ThreeSuperThree -> Cube3`;
- `cubeRoundTrip : towerToCube (cubeToTower c) == c`;
- `towerRoundTripPointwise : cubeToTower (towerToCube f) t == f t`.

This uses no function extensionality postulate. The selected C3 additive
action is transported onto the trit-value function carrier, with an
explicit pointwise preservation theorem. The actual six-bit triple
encoder `VerifiedFiniteTritCoder.encodeTriple` is reused.

This is stronger than a matching cardinality; it does not imply that
a path-cube graph adjacency, a C3^3 Cayley graph, a spectrum, and a
tetrational successor operation are all identical.

## Remaining acceptance cut

K01: full positive arbitrary-list Conway evaluation and termination
K02: length-costed flat bits codec for arbitrary symbolic chains and
     prime-exponent vectors (the native fixed six-bit 27-cell codec
     is already reused)
K03: source/target language choice and real polynomial-time map
K04: selected cube/tower definitional equality and actual C3 cube
     reversible table codec SOURCE-WRITTEN; kernel acceptance pending
K05: polynomiality transport into the existing Cook-Levin cost
     contract for a selected compiler
K06: actual Karp-21/CNF instance rather than a synthetic toy edge
K07: exact-head parallel_checker acceptance pending

The statement P != NP remains equivalent to SAT not in P only under
the selected established-background hypotheses. The Conway notation
alone does not establish a lower bound.
