# Heegner CKM Diagnostic v2 Status

Date: `2026-05-29`

Status: diagnostic receipts landed; no physical CKM or Clay promotion.

## New Manager A Receipts

| Receipt | Role | Submission use |
|---|---|---|
| `DASHI.Physics.Closure.OSPositivityDissolvedReceipt` | Corrects the H0 blocker: bare Yukawa entries are not Hamiltonian entries. | Appendix-clean as claim-governance. |
| `DASHI.Physics.Closure.PhysicalMassMatrixReceipt` | Applies external PDG `v = 246.22 GeV` to compute `M_d = Y_d v/sqrt(2)`. | Diagnostic-only; masses miss PDG. |
| `DASHI.Physics.Closure.CKMFromPhysicalMassMatrix` | Records CKM eigenvectors after VEV calibration. | Diagnostic-only; global VEV scale does not fix CKM. |
| `DASHI.Physics.Closure.Deg23RGRunningHypothesisReceipt` | Tests one-loop QCD running as the `deg23` residual explanation. | Diagnostic-negative; best scan overshoots. |
| `DASHI.Physics.Closure.VubVtdFromFullCKM` | Records `|Vub|`, `|Vtd|`, and Jarlskog from the complex matrix. | Diagnostic-only; Jarlskog is about `11.26x` PDG-sized target. |

## Numerical Outcomes

The VEV-calibrated down-sector diagnostic gives mass eigenvalues

```text
[0.013417, 7.147906, 59.686732] GeV
```

against rough PDG comparison targets

```text
[0.00467, 0.0934, 4.18] GeV.
```

The VEV factor rescales masses but does not alter the eigenvectors. The current
diagnostic CKM matrix remains

```text
|V| ~= [[0.648665, 0.089765, 0.755762],
       [0.749691, 0.095891, 0.654804],
       [0.131142, 0.991336, 0.007398]]
```

and is not a physical CKM match.

The Jarlskog diagnostic is

```text
J ~= -3.4677e-4,  |J|/J_PDG ~= 11.26.
```

The one-loop QCD running scan requires `2.16%` to explain the `deg23` residual.
The natural `p5 -> p7` scale test gives about `4.26%`, so it overshoots. A
tuned high scale near `5.919 GeV` can reproduce the factor, but this is not a
carrier derivation.

## Tag Message Prepared

Suggested tag, after the full worktree is intentionally committed:

```text
Heegner-CKM-diagnostic-v2
```

Suggested commit message:

```text
record Heegner CKM v2 diagnostics with VEV mass matrix and negative RG checks
```

Do not use this tag to imply a physical CKM derivation. The relevant false flags
remain false: `physicalCKMPromoted`, `physicalCPPhaseDerived`,
`physicalMassMatchesPDG`, `rgRunningResolvesDeg23Residual`, and
`physicalVcbPromoted`.
