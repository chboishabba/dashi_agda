# Clay Braid Correlation Frontier

This receipt records the refined 369 game-proof frontier.

The conditional criterion is:

```text
BraidResidue369(K) <= C * r^K
r * sqrt(2) < 1
=> high-shell vortex stretching is summably absorbed by viscosity
```

Recorded regimes:

| Regime | Residue base | Outcome |
| --- | ---: | --- |
| independent trits | `27^-K` | closes the criterion |
| DNS-like partial correlation | `(2/3)^K` | closes: `(2/3) * sqrt(2) ~= 0.943 < 1` |
| BT-carrier decorrelation | `(6/7)^K` | does not close alone: `(6/7) * sqrt(2) ~= 1.212 > 1` |
| coherent vortex tube | `1^K` | fails |

This converts the NS game proof into a clear regularity criterion.  It does
not prove deterministic Navier-Stokes regularity.  The remaining NS terminal is
`CoherentTubeFormation`, equivalently the classical direction-regularity /
coherent-tube obstruction associated with Constantin-Fefferman-Majda-style
criteria.

The same receipt also records `HyperbolicShimuraToEuclideanUniversality` as a
shared blocker:

```text
YM: BT/hyperbolic carrier results must transfer to flat Euclidean R4.
NS: BT decorrelation must transfer strongly enough to physical R3 flow.
```

The current BT rate `(6/7)^K` is not sufficient by itself for the NS
half-derivative gap.  A proof would need stronger decorrelation or a second
suppression mechanism.

All Gate3, Navier-Stokes, Yang-Mills, and Clay promotion flags remain false.
