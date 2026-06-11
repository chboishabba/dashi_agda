# Clay Sprint Three Implementation Work Orders

This document is the implementation-facing companion to
`ClaySprintThreeSixWorkerAssignmentReceipt`.

Agda receipt:

```text
DASHI/Physics/Closure/ClaySprintThreeImplementationWorkOrderReceipt.agda
```

The work orders are concrete implementation contracts.  They assign deliverables
and kill criteria; they do not mark any hard bridge solved.

## W1 Gate3 Identification

Deliverable:

```text
Implement or refute SSPCarrierEqualsOKHeckeModel by comparing the actual SSP
carrier architecture with the O_K Hecke/BT model.
```

Acceptance:

```text
actual SSP carrier = O_K Hecke/BT carrier
```

Kill criterion:

```text
SSP architecture is not the O_K Hecke/BT model, or the map collapses to the
degenerate 1D toy.
```

## W2 Gate3 Frame Consumer

Deliverable:

```text
Implement only the conditional chain:
SSPCarrierEqualsOKHeckeModel
  -> PhysicalSSPSpreadBound
  -> UniformFrameLowerBound
  -> Gate3MoscoNoPollutionTransfer
```

Acceptance:

```text
Every frame/Mosco step consumes W1 explicitly.
```

Kill criterion:

```text
Any frame lower bound that consumes O_K spread without W1's identification
bridge.
```

## W3 NS Commutator Lipschitz

Deliverable:

```text
Implement or refute CommutatorLipschitzControl for
[P_>K, u_<K . grad] u_>K.
```

Forbidden inputs:

```text
Serrin
BKM
global H^(11/8)
hidden L_infinity
the retracted K^(-1/2) suppression claim
```

Acceptance:

```text
non-circular commutator control sufficient for the HighLow part of
CumulativeTailDissipationDominance
```

## W4 NS Counterfamily And Audit

Deliverable:

```text
Search for a Leray-energy-bounded HighLow counterfamily and audit every
attempted W3 proof for hidden regularity input.
```

Acceptance:

```text
either a valid counterfamily, or a proof that the attempted counterfamily
violates Leray energy / incompressibility / LP support constraints
```

Kill criterion:

```text
counterfamily uses energy growth, pressure inconsistency, or a hidden
regularity assumption.
```

## W5 YM Balaban Uniformity

Deliverable:

```text
Implement or refute uniform 42--43 step Balaban contraction:
rho_k < 1 with summable leakage until
beta_eff*c_min_BT - a_BT > log(2*p).
```

Robust numerical sample:

```text
beta_eff >= 13.7
```

Acceptance:

```text
uniform rho_k < 1 for the whole finite block-spin run, plus summable leakage.
```

Kill criterion:

```text
any block step lacks uniform contraction, or leakage cannot be summed without
an unproved continuum regularity/universality assumption.
```

## W6 Governance

Deliverable:

```text
Keep the K^(-1/2) retraction, exact Balaban margin, O_K/SSP distinction, and
all false promotion flags mechanically aligned.
```

Acceptance:

```text
no receipt consumes a retracted or merely model-side result as a theorem.
```

Kill criterion:

```text
any Clay/Gate3/YM/NS promotion flag turns true before the hard bridge is
inhabited.
```

## Boundary

These work orders do not prove `SSPCarrierEqualsOKHeckeModel`,
`UniformFrameLowerBound`, `CommutatorLipschitzControl`,
`CumulativeTailDissipationDominance`, `NonperturbativeBalabanScaleTransfer`,
Gate3, Yang-Mills, Navier-Stokes, or Clay.
