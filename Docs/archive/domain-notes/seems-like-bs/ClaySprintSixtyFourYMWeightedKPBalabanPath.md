# Clay Sprint Sixty Four YM Weighted KP Balaban Path

Sprint 64C records the current shortest honest Yang-Mills path.

## Live Obstruction

The current in-repo YM blocker is not `q < 1`.  Sprint 55 already established:

```text
q(beta_blocked = 16.7) = 0.23178189475262734
8q                         = 1.8542551580210187
beta_needed_for_8q_lt_1    = 19.251582989089552
```

So the finite-prefix/geometric activity ratio is encouraging but insufficient.
The KP polymer sum sees the incompatibility branching:

```text
weighted KP gate = 8q < 1
```

At the current blocked beta, this fails.

## Shortest YM Route

The manageable YM route is now:

```text
1. Weighted KP threshold:
   prove or compute q(beta) with 8q(beta) < 1.

2. Balaban RG scale transfer:
   beta_bare = 6.0 -> beta_blocked >= 19.251582989089552
   while preserving the polymer activity/leakage bound.

3. All-diameter KP certificate:
   KPActivity(d) <= A * q^d and the weighted incompatibility sum is finite.

4. Continuum rho/leakage:
   keep the bounds uniform as the cutoff is removed.

5. OS/Wightman reconstruction plus mass gap:
   transfer the lattice certificate into the continuum Clay YM target.
```

## Governance

This ledger makes YM the clean in-repo analytic lane, but it does not promote
YM.  The following remain open:

- `8q < 1` at the consumed blocked scale;
- Balaban transfer from physical beta `6.0` to the weighted-KP threshold;
- activity/leakage preservation under RG;
- all-diameter KP;
- continuum rho/leakage;
- OS/Wightman reconstruction;
- mass-gap survival.

No Clay/YM promotion follows.
