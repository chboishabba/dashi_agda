# NS Dynamic Braid Depletion

This receipt records the conditional NS game-proof surface.

The safe conditional theorem is:

```text
AdjacentOnlyTransfer
+ BadStretchResidue_K <= C * 3^-K
+ summability of 3^-K * 2^(K/2)
=> vortex-stretching absorption
```

The calculation is the useful part:

```text
3^-K * 2^(K/2) = (sqrt(2) / 3)^K
```

Since `sqrt(2) / 3 < 1`, the high-shell danger is summable and can be
absorbed into viscosity after a finite low-shell split.

The later braid-correlation frontier generalizes this as:

```text
BraidResidue369(K) <= C * r^K
r * sqrt(2) < 1
=> high-shell vortex stretching is absorbed
```

The recorded regimes are:

| Regime | Residue base | Outcome |
| --- | ---: | --- |
| independent trits | `27^-K` | closes |
| DNS-like partial correlation | `(2/3)^K` | closes because `(2/3) * sqrt(2) ~= 0.943 < 1` |
| BT-carrier decorrelation | `(6/7)^K` | not enough alone because `(6/7) * sqrt(2) ~= 1.212 > 1` |
| coherent vortex tube | `1^K` | fails |

The hard boundary is also explicit: trit branch-counting does not by itself
prove a deterministic Navier-Stokes theorem.  For Clay, one must prove:

```text
DynamicBraidResidueDecayForNS:
  ActualNSSolution u ->
  BadStretchResidue u K t <= C * 3^-K
```

or the weaker but sufficient half-derivative form:

```text
DynamicHalfDerivativeDepletion:
  BadStretchResidue u K t <= C * 2^(-(1/2 + eta)K)
```

If the residue decay is proved only for carrier-structured data, the result is
only a carrier-structured NS theorem until density and stability transfer are
also proved.  All Clay promotion flags remain false.

The current NS terminal is `CoherentTubeFormation`, equivalently the
direction-regularity/coherent-tube obstruction surfaced by classical
Constantin-Fefferman-Majda-style criteria.  The 369 language records that
frontier; it does not bypass it.
