# NS HighLow Commutator Obstruction

This receipt records the corrected NS HighLow state.

Agda receipt:

```text
DASHI/Physics/Closure/NSHighLowCommutatorObstructionReceipt.agda
```

Proved/supported facts:

```text
transport term vanishes exactly
HighLow reduces to the commutator
K^(-1/2) suppression is retracted
Leray + Bernstein gives growing low-mode Lipschitz control
```

Transport cancellation:

```text
<(u_<K . grad)u_>K, u_>K> = 0
```

Commutator reduction:

```text
B_HL = <[P_>K, u_<K . grad]u_>K, u_>K>
```

The live obstruction:

```text
CommutatorLipschitzControlWithoutRegularity
```

Forbidden inputs:

```text
Serrin
BKM
global H^(11/8)
hidden L_infinity
the retracted K^(-1/2) shortcut
```

Dichotomy:

```text
Either prove non-circular commutator control,
or produce a Leray-energy-bounded HighLow counterfamily.
```

Boundary:

```text
This receipt does not prove CumulativeTailDissipationDominance, K* no-drift,
global H^(11/8), continuation, or Clay NS.
```
