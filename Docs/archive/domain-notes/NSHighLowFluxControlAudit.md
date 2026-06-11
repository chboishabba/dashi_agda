# NS HighLow Flux Control Audit

This receipt records the corrected Navier-Stokes HighLow audit surface.

The previous tail-dominance receipt keeps HighHigh as the absorptive partial
result.  The live obstruction is the HighLow/LowHigh term.

The previous claim is now retracted:

```text
HighLow flux has K^(-1/2) suppression against tail dissipation
without hidden L_infinity, H^(1/2), Serrin, BKM, or global H^(11/8) input.
```

The genuine partial result is:

```text
<(u_<K . grad) u_>K, u_>K> = 0
```

by integration by parts and incompressibility.  Therefore the HighLow term is
reduced exactly to the commutator:

```text
B_HL = <[P_>K, u_<K . grad] u_>K, u_>K>
```

The accepted audit bound has the wrong direction for tail dominance:

```text
theta_HL <= C * 2^K * sqrt(E0) / (nu^(1/2) * Diss_>K^(1/2))
```

The live obstruction is `CommutatorLipschitzControl` without importing
Serrin/BKM/global `H^(11/8)`/hidden `L_infinity` control.

No cumulative tail dominance, `K*` no-drift, global `H^(11/8)` bound, or Clay
Navier-Stokes promotion follows from this receipt.
