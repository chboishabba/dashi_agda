# Monster / Ogg Prime Correction

This note records the corrected moonshine indexing statement.

The Monster has `194` conjugacy classes / irreducible characters.  Monstrous
moonshine assigns McKay-Thompson series to Monster conjugacy classes, and the
genus-zero/Hauptmodul property belongs to that McKay-Thompson lane.  The
`15` Ogg/supersingular primes are a different indexing set: they are the prime
divisors of the Monster order and the primes for which the Ogg modular-curve
condition holds.

So the ledger must not read:

```text
194 Monster classes = 15 genus-zero + 179 genus-positive
```

The fail-closed reading is:

```text
194 Monster classes/conjugacy lanes
15 Ogg/supersingular prime carrier lanes
179 non-carrier bookkeeping remainder
```

The `15 + 179` split is carrier quotient bookkeeping, not a genus partition.
It does not prove Gate3, Yang-Mills, Navier-Stokes, gravity, or any terminal
claim.
