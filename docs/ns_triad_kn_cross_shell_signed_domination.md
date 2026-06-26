# NS Triad K_N Cross-Shell Signed Domination

> **Status:** Proof target fixed. This is the live Gate 1 theorem surface.
> No promotion claim made.

---

## Definition

On the seam block \(C = \{\text{shells } N-1, N\}\), write

\[
S_C = L_{\mathrm{good}} - L_{\mathrm{bad}}
\]

with \(S_C \mathbf{1}_C = 0\) and the live coercivity question posed on
\(\mathbf{1}_C^\perp\).

Define the signed domination ratio

\[
\rho_N
=
\sup_{x \perp \mathbf{1}_C}
\frac{x^\top L_{\mathrm{bad}} x}
     {x^\top L_{\mathrm{good}} x}.
\]

---

## Observed

- \(\rho_6 \approx 0.6076\)
- \(\rho_8 \approx 0.6257\)
- \(\rho_{10} \approx 0.6144\) via projected CPU matrix-free generalized eigensolve
- \(\rho_{12} \approx 0.6577\) via projected CPU matrix-free generalized eigensolve
- \(\rho_{14} \approx 0.5956\) via projected CPU matrix-free generalized eigensolve
- \(S_C\) is PSD with nullity one at \(N=6,8,10,12,14\) in the current audits
- \(S_C \mathbf{1}_C = 0\) is proved analytically and machine-zero numerically
- All currently tested domination ratios remain below \(2/3\), with the present worst case at \(N=12\)
- The current worst generalized eigenvectors are concentrated on the seam shells \(N-1\) and \(N\), carry negligible axis mass, and are led by non-axis modes such as \((-1,0,N-1)\)
- Ordinary Laplacian reduction is dead: positive off-diagonals occur in the dense sign audit
- The “balanced signed graph” framing is demoted: it is not the active theorem route

---

## Target Theorem

\[
\boxed{
\exists \rho_* < 1 \text{ such that } \rho_N \le \rho_* \text{ uniformly in } N.
}
\]

Equivalently, for every \(x \perp \mathbf{1}_C\),

\[
x^\top S_C x
=
x^\top L_{\mathrm{good}} x - x^\top L_{\mathrm{bad}} x
\ge
(1-\rho_*) x^\top L_{\mathrm{good}} x
\ge 0.
\]

This is now the single live Gate 1 proof obligation.

---

## Consequence

If the uniform bound holds, then:

- \(S_C \succeq 0\) on \(\mathbf{1}_C^\perp\)
- \(\ker S_C = \operatorname{span}\{\mathbf{1}_C\}\)
- the Gate 1 block floor follows through the Schur complement route

---

## Receipt Boundary

```text
schurSignedPsdRequired = true
signedDominationProbeInstalled = true
signedDominationRatioBelowOneObserved = true
schurComplementPsdVerified = true

signedDominationRatioUniformlyBounded = false
schurSignedFactorizationProved = false
schurComplementPsdProved = false
gate1ConditionalTheoremProved = false

ordinaryKronLaplacianRoute = false
balancedSignedGraphRoute = false
```

---

## Agda Status

```text
Python regression: passed
Matrix-free audit: passed
Dense sign/factorization audit: passed
Focused Agda check: passed
Full Everything.agda check: attempted, killed exit 137
Promotion check: not yet run
```

Exit `137` is an environment/resource failure, not a proof failure.
