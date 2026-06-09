# Clay Sprint 30 Ternary Residue Refinement

Sprint 30 refines the Sprint 29 analytic residue harness.  The DASHI mask is
ternary first, then projected to a nonnegative badness weight only when forming
the physical upper bound.

## Ternary Mask

```text
tau_K in {-1, 0, +1}
```

Interpretation:

```text
-1  anti-stretch / cancelling branch
 0  neutral / transport branch
+1  expansive / dangerous branch
```

Projection:

```text
tau_K^+ = max(tau_K, 0)
tau_K^- = max(-tau_K, 0)
```

## Residue Triple

Positive stretching potential:

```text
P_K = integral lambda_1^+(S_K) * |omega_K|^2
```

Expansive bad mass:

```text
B_K^+ = integral tau_K^+ * a_K * lambda_1^+(S_K) * |omega_K|^2
```

Cancelling mass:

```text
B_K^- = integral tau_K^- * a_K * lambda_1^+(S_K) * |omega_K|^2
```

Residues:

```text
R_K^+ = B_K^+ / (P_K + epsilon)
R_K^- = B_K^- / (P_K + epsilon)
R_K^0 = 1 - R_K^+ - R_K^-
```

Clay-facing scalar:

```text
BadResidue_K = R_K^+
```

DASHI-facing scalar:

```text
NetResidue_K = R_K^+ - R_K^-
```

The physical bridge must use the positive part:

```text
Q_K <= C * R_K^+
```

The dynamic depletion test remains:

```text
R^+_(K+1) / R^+_K < 1 / sqrt(2)
```

## Pressure Trit

Pressure is ternary too:

```text
-1  pressure decorrelates or stretch-cancels
 0  pressure is neutral
+1  pressure reinforces dangerous coherence
```

Fail-closed combination:

```text
tau_total = +1  if braid = +1 and measured pressure != -1
tau_total =  0  if braid = +1 and measured pressure = -1
tau_total = -1  if braid = -1
tau_total =  0  otherwise; unknown pressure keeps danger visible
```

Pressure may downgrade danger only when the pressure-decorrelation term is
actually measured.  It cannot hide danger by assertion, missing data, or
generic expectation.  Unknown pressure keeps danger visible.

## Boundary

This sprint records a ternary refinement of the residue harness only.  It does
not prove `Q_K <= C R_K^+`, prove `R^+_(K+1)/R^+_K < 1/sqrt(2)`, prove net
residue improvement, prove pressure decorrelation, close Gate3, perform
Lean-port work, prove Yang-Mills uniformity, or promote any Clay claim.
Uploaded notes, preliminary computations, external artifacts, and tool outputs
are context only, not Agda authority or promotion evidence.
