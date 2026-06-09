# Clay Sprint Three Six-Worker Assignment

This receipt records the corrected Sprint 3 worker split after the three lane
updates:

```text
Gate3: O_K Hecke/BT model passes the 3D taper test.
NS:    HighLow K^(-1/2) suppression is retracted; transport cancels exactly.
YM:    one-loop diagnostic gives a 42--43 step Balaban target.
```

The Agda receipt is:

```text
DASHI/Physics/Closure/ClaySprintThreeSixWorkerAssignmentReceipt.agda
```

## W1 Gate3 Identification

```text
Task: prove or kill SSPCarrierEqualsOKHeckeModel
Input: O_K = Z[(1+sqrt(-7))/2], 118 atoms, norm <= 49
Target: actual SSP carrier architecture equals the O_K Hecke/BT model
```

This is the only bridge that can turn the model-side spread result into a
physical Gate3 support theorem.

## W2 Gate3 Frame Consumer

```text
Task: consume O_K spread into UniformFrameLowerBound only conditionally
Guard: SSPCarrierEqualsOKHeckeModel must be proved first
```

Until W1 closes the identification bridge, W2 may record only conditional frame
bookkeeping, not Gate3 closure.

## W3 NS Commutator Lipschitz

```text
Task: prove or kill CommutatorLipschitzControl
Forbidden inputs: Serrin, BKM, global H^(11/8), hidden L_infinity
```

The transport term is gone:

```text
<(u_<K . grad) u_>K, u_>K> = 0
```

The remaining term is the commutator:

```text
[P_>K, u_<K . grad] u_>K
```

## W4 NS Counterfamily And Audit

```text
Task: search for a Leray-energy-bounded HighLow counterfamily
Guard: the retracted K^(-1/2) claim cannot be consumed
```

The accepted audit bound grows like:

```text
C * 2^K * sqrt(E0) / (nu^(1/2) * Diss_>K^(1/2))
```

That is not a cumulative tail dominance proof.

## W5 YM 42--43 Step Target

```text
Task: prove or kill uniform non-perturbative Balaban contraction
Target: beta_eff*c_min_BT - a_BT > log(2*p)
Robust sample: beta_eff >= 13.7
Diagnostic scale: about 43 block-spin steps / 42 integrations
```

The one-loop map is a scale estimate only.  It is not
`NonperturbativeBalabanScaleTransfer`.

## W6 Governance

```text
Task: preserve retractions, exact margin statements, and false promotions
```

W6 owns the mechanical guardrails:

```text
O_K model evidence is not SSP identification.
Transport cancellation is not HighLow dominance.
K^(-1/2) suppression is retracted.
One-loop 42--43 steps is not Balaban transfer.
All Clay/Gate3/YM/NS promotion flags remain false.
```

## Boundary

This is an assignment and governance receipt.  It does not prove
`SSPCarrierEqualsOKHeckeModel`, `UniformFrameLowerBound` for the physical
carrier, `CommutatorLipschitzControl`, `CumulativeTailDissipationDominance`,
`NonperturbativeBalabanScaleTransfer`, Gate3, Navier-Stokes, Yang-Mills, or
Clay.
