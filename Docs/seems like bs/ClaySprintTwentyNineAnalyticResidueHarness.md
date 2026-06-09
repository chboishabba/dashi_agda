# Clay Sprint 29 Analytic Residue Harness

Sprint 29 records the concrete candidate for `BraidResidue369` and the tests
that can make or kill the Navier-Stokes braid route.

## Candidate Residue

```text
omega_K = P_K omega
S_K = P_K S
lambda_1^+(S_K) = max(lambda_1(S_K), 0)
```

Alignment:

```text
a_K = |omega_K dot e_1(S_K)|^2 / (|omega_K|^2 + epsilon)
```

Positive stretching potential:

```text
P_K = integral lambda_1^+(S_K) * |omega_K|^2
```

Bad mass:

```text
B_K = integral chi_K * a_K * lambda_1^+(S_K) * |omega_K|^2
```

Residue:

```text
R_K = B_K / (P_K + epsilon)
```

This is non-tautological because it combines DASHI/trit/braid masking with
physical strain-vorticity geometry rather than defining the residue as
stretching itself.

## Physical Test

Shell stretching:

```text
T_K = |integral (S_K omega_K) dot omega_K|
```

Shell dissipation:

```text
D_K = nu * 2^(2K) * ||omega_K||_2^2
```

Normalized stretching:

```text
Q_K = T_K / (2^(K/2) * D_K + epsilon)
```

The decisive bridge is:

```text
Q_K <= C * R_K
```

Audit ratio:

```text
C_K = Q_K / (R_K + epsilon)
```

## Ratio Test

```text
rho_K = R_(K+1) / (R_K + epsilon)
```

The route needs:

```text
rho_K < 1 / sqrt(2)
```

## Outcome Table

```text
Q_K <= C R_K and rho_K < 1/sqrt(2):
  route becomes serious

rho_K < 1/sqrt(2) but Q_K not <= C R_K:
  symbolic failure

Q_K <= C R_K but rho_K >= 1/sqrt(2):
  coherent-tube failure

both fail:
  full route failure
```

## Pressure Mask

Pressure decorrelation score:

```text
Pi_K =
  |<H_K e_1(S_K), omega_K / |omega_K|>|
  /
  (|H_K| * |omega_K| + epsilon)
```

Continuous mask:

```text
chi_K = 1_expansive * 1_BT-adjacent * (1 - Pi_K)
```

New open lemma:

```text
PressureDecorrelatesCoherentStretching:
  Dangerous coherent tube
  -> PressureDecorrelation >= c0 or BeltramiSafe
```

## Boundary

This sprint records a candidate formula and falsification harness only.  It
does not prove `R_K` is bounded, prove `Q_K <= C R_K`, prove dynamic decay,
prove pressure decorrelates coherent stretching, prove regularity, close
Gate3, perform Lean-port work, or promote Clay Navier-Stokes.  Uploaded notes,
preliminary computations, and external artifacts are context only, not Agda
authority.
