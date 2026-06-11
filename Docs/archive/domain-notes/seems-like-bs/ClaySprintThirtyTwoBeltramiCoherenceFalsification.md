# Clay Sprint 32 Beltrami Coherence Falsification

Sprint 32 sharpens the ternary residue mask around the surviving adversary
from the pressure-decorrelation audit: globally coherent parallel or
Beltrami-like tubes.

The point is not that coherence is automatically bad.  Exact Beltrami
coherence is neutral after Leray projection.  The dangerous branch is:

```text
coherent direction
+ non-Beltrami
+ not pressure-decorrelated
```

## Three Defects

Beltrami defect:

```text
B_Bel(K) =
  ||P_K(u x omega)||_2
  /
  (||P_K u||_2 * ||P_K omega||_2 + epsilon)
```

Direction coherence defect:

```text
D_dir(K) =
  2^(-K) * ||grad xi_K||_{L2(|omega_K|^2 dx)}
  /
  (||xi_K||_{L2(|omega_K|^2 dx)} + epsilon)
```

Pressure decorrelation score:

```text
P_decorr(K) =
  |<H_K e_1(S_K), omegaHat_K>|
  /
  (|H_K| * |omega_K| + epsilon)
```

## Ternary Rule

```text
neutral:
  B_Bel(K) <= beta_Bel

antiStretch/decorrelated:
  P_decorr(K) >= c_decorr

expansive/dangerous:
  D_dir(K) <= d0
  B_Bel(K) > beta_Bel
  P_decorr(K) < c_decorr

neutral:
  otherwise
```

Exact Beltrami must be neutral, not bad:

```text
B_Bel(K) = 0 -> tritMask(K) = neutral
```

Pressure decorrelation may downgrade expansive danger to neutral only when it
is measured:

```text
braidMask(K) = expansive
P_decorr(K) >= c_decorr
-> totalMask(K) = neutral
```

It becomes anti-stretch only with a stronger negative-work proof.

## Falsification Test

The hard gate is now:

```text
NonBeltramiCoherentTubeCannotPersist:
  coherent direction
  + Beltrami defect > beta_Bel
  + pressure decorrelation < c_decorr
  -> R^+_(K+1) <= r * R^+_K
     with r * sqrt(2) < 1
```

If this fails with `rho_K ~= 1` on coherent non-Beltrami tubes, the DASHI
pressure/braid route fails cleanly.

## Boundary

This sprint records a sharper NS-only falsification surface.  It does not
prove the Beltrami defect is dynamically small, prove pressure decorrelation
for all coherent tubes, prove `NonBeltramiCoherentTubeCannotPersist`, prove
`Q_K <= C R_K^+`, close Gate3, prove Yang-Mills uniformity, perform Lean-port
work, prove constructive QFT, or promote any Clay claim.  Uploaded notes,
preliminary computations, external artifacts, and tool outputs are context
only, not Agda authority or promotion evidence.
