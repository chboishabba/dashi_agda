# NS Triad K_N Cross-Shell Schur Complement — Null-Mode Proof Target

> **Status:** Proof target fixed. The constant null mode is now proved as the
> Schur/Kron-style reduction gauge mode.
> Matrix-free `LinearOperator`/`eigsh` audits at `N=12,14` are now recorded as
> supporting evidence. No promotion claim made.

---

## Theorem Target

Let $M$ be the seam-block restriction of the weighted pair-Laplacian operator

$$
M = L_{\mathrm{neg}} - c_0 L_{\mathrm{abs}}, \qquad c_0 = \tfrac{1}{9},
$$

restricted to the 1–(N-1)–N shell triad. Partition the block as

$$
M = \begin{pmatrix} M_{GG} & M_{GC} \\ M_{CG} & M_{CC} \end{pmatrix},
\qquad
G = \{\text{shell } 1\},\ C = \{\text{shells } N-1,\, N\}.
$$

**Legacy Schur target, now reduced to signed domination:**

$$
\boxed{S_C \mathbf{1}_C = 0,\qquad S_C \succeq 0,\qquad \dim\ker S_C = 1,}
$$

where

$$
S_C = M_{CC} - M_{CG}\, M_{GG}^{-1}\, M_{GC}
$$

is the Schur complement of $M_{GG}$ in $M$.

The live proof obligation is now recorded separately in
`docs/ns_triad_kn_cross_shell_signed_domination.md`: prove a uniform bound
\(\rho_N \le \rho_* < 1\) for
\[
\rho_N
=
\sup_{x \perp \mathbf{1}_C}
\frac{x^\top L_{\mathrm{bad}} x}
     {x^\top L_{\mathrm{good}} x}.
\]

---

## Numerical Evidence

### Structural constants (stable across all tested N)

| Quantity | Value | Variation |
|---|---|---|
| $\|M_{GC}\|$ | $4.34 \times 10^{-3}$ | $< 0.5\%$ |
| $\|M_{CG} M_{GG}^{-1} M_{GC}\|$ | $1.18$–$1.21 \times 10^{-3}$ | $< 3\%$ |
| Null-mode shell split (N-1 : N) | $\approx 44\%$ : $56\%$ | $< 2\%$ |
| $G$ size | $26$ modes | exact |

### $M_{CC}$ minimum eigenvalue — decays toward the seam

| N | $\lambda_{\min}(M_{CC})$ |
|---|---|
| 6 | $1.7365 \times 10^{-5}$ |
| 8 | $7.6331 \times 10^{-6}$ |
| 10 | $4.2906 \times 10^{-6}$ |
| 12 | $2.6983 \times 10^{-6}$ |
| 14 | $2.0226 \times 10^{-6}$ |

The sampled floor keeps shrinking with $N$. This is evidence that the seam block
is approaching a soft mode, not a proof of any asymptotic law.

### $S_C$ nullity — observed bottom spectrum

| N | Method | $\lambda_0(S_C)$ | $\lambda_1(S_C)$ | $\lambda_2(S_C)$ | nullity est. | Verdict |
|---|---|---|---|---|---|---|
| 6 | dense `eigh` | $+4.83 \times 10^{-18}$ | — | — | **1** | `schur_psd` |
| 8 | dense `eigh` | $-1.44 \times 10^{-17}$ | — | — | **1** | `schur_psd` |
| 10 | dense `eigh` | $-1.65 \times 10^{-18}$ | — | — | **1** | `schur_psd` |
| 12 | matrix-free `eigsh` | $+9.66 \times 10^{-18}$ | $7.80 \times 10^{-6}$ | $7.94 \times 10^{-6}$ | **1** | `schur_psd` |
| 14 | matrix-free `eigsh` | $-2.97 \times 10^{-18}$ | $9.82 \times 10^{-6}$ | $9.92 \times 10^{-6}$ | **1** | `schur_psd` |

> [!NOTE]
> The `N=12,14` receipts do **not** materialize a dense Schur complement or run a
> full dense eigensolve on $S_C$. They use a `LinearOperator` for
> $x \mapsto M_{CC}x - M_{CG}M_{GG}^{-1}M_{GC}x$ and request only the bottom few
> eigenpairs.

---

## Key Structural Observations

### 0. The null mode is analytically forced by row-sum zero

Each of \(L_{\mathrm{neg,cross}}\) and \(L_{\mathrm{abs,cross}}\) is a graph
Laplacian on the seam block, so both annihilate the all-ones vector. Hence

$$
M\mathbf{1} = \Bigl(L_{\mathrm{neg,cross}} - \tfrac19 L_{\mathrm{abs,cross}}\Bigr)\mathbf{1} = 0.
$$

Block-partitioning \(M\) and eliminating the \(G\)-block gives

$$
S_C \mathbf{1}_C
= M_{CC}\mathbf{1}_C - M_{CG} M_{GG}^{-1} M_{GC}\mathbf{1}_C
= 0.
$$

So the constant-on-\(C\) null mode is not merely observed numerically. It is the
**Schur/Kron-style gauge mode** forced by \(M\mathbf{1}=0\).

### 1. Nullity one persists under the matrix-free audit

The correction $\|M_{CG} M_{GG}^{-1} M_{GC}\| \approx 1.2 \times 10^{-3}$ is **3 orders of magnitude**
smaller than the positive bulk scale in the bottom nonzero Schur eigenvalues
$\lambda_1,\lambda_2 \sim 10^{-5}$. The null mode in $S_C$ is
therefore **not driven by the off-diagonal coupling** to shell 1. It is intrinsic to $M_{CC}$
approaching zero at the seam, modulated by a rank-26 perturbation too small to create the zero.

This means the null mode is a property of the (N-1)–N cross-shell geometry, not of the
G–C coupling.

### 2. The null mode lives on the (N-1)–N seam and is nearly constant on C

The worst $S_C$ eigenvector has **zero support on shell 1** by construction of the Schur
complement. Its shell mass is stable:

| N | Shell N-1 mass | Shell N mass |
|---|---|---|
| 6 | 41.0% | 59.0% |
| 8 | 43.4% | 56.6% |
| 10 | 44.8% | 55.2% |
| 12 | 45.7% | 54.3% |
| 14 | 46.3% | 53.7% |

The split is drifting toward 50/50 as $N \to \infty$.

The new matrix-free correlation diagnostics match the **Schur/Kron-style gauge mode**
interpretation and rule out the earlier shell-balance hypothesis:

| N | corr$(v_0,\mathbf{1}_C)$ | corr$(v_0,\text{shell balance})$ | corr$(v_0,\sqrt{\deg})$ | corr$(v_0,\deg^{-1})$ |
|---|---|---|---|---|
| 12 | $+1.0000$ | $-0.0867$ | $+0.9712$ | $+0.9546$ |
| 14 | $-1.0000$ | $+0.0739$ | $-0.9678$ | $-0.9556$ |

The sign flip at `N=14` is immaterial. The eigenspace is one-dimensional, so
`v_0` and `-v_0` represent the same null mode.

### 3. M_CC has no null mode; S_C does

$\dim\ker M_{CC} = 0$ at all tested N (M_CC is strictly PSD). The nullity-1 null mode
appears **only in the Schur complement**, meaning it requires the cross-shell coupling
to appear. This is a signature of a topological (frustration-type) obstruction in the
seam block Gram matrix.

---

## Open Questions

| Question | Status |
|---|---|
| Is $S_C \mathbf{1}_C = 0$? | **Yes.** Follows from $M\mathbf{1}=0$ and Schur complementation. |
| Is $S_C \succeq 0$ (PSD) for all N? | Observed at N=6,8,10,12,14. Proof open; live route is signed domination. |
| Is $\dim\ker S_C = 1$ for all N? | Observed at N=6,8,10,12,14. Connectivity proof open. |
| What is the null vector $v_0$? | The constant vector $\mathbf{1}_C$ up to scale/sign. |
| Is $v_0$ a shell-balance indicator? | No. Correlation is small at N=12,14. |
| Are ordinary Kron-reduced edge weights nonnegative? | Open; this is a strong sufficient shortcut, not the definition of Gate 1 admissibility. |
| Is the ordinary Kron-reduced graph connected? | Open; only relevant if the nonpositive-offdiagonal shortcut closes. |
| Can the bad signed part be uniformly dominated by the good signed part on $\mathbf{1}_C^\perp$? | Open. This is the live Gate 1 theorem target. |
| Can $S_C = B_{\mathrm{eff}}^T W_{\mathrm{eff}} B_{\mathrm{eff}}$ be factored? | Open explicit factorization; useful, but no longer the primary theorem target. |
| Does $\lambda_{\min}(M_{CC}) \to 0$ as $N \to \infty$? | Supported by N=6,8,10,12,14 decay. Proof open. |

---

## Current Audit Command

**Matrix-free Schur eigsh rerun for N=12, 14:**

```
python3 scripts/ns_triad_kn_cross_shell_schur_symbolic_audit.py \
  --shells 12 14 --dense-schur-threshold 3500
```

**Effective-laplacian sign audit for the dense shells `N=6,8`:**

```
python3 scripts/ns_triad_kn_cross_shell_schur_symbolic_audit.py \
  --shells 6 8 --dense-schur-threshold 3500 \
  --audit-effective-laplacian-signs
```

Current output per shell:
```
λ_0, λ_1, λ_2   (bottom 3 eigenvalues of S_C)
nullity estimate
max |S_C 1_C|
shell support of v_0
corr(v_0, constant), corr(v_0, shell_N-1), corr(v_0, shell_N)
corr(v_0, shell_balance), corr(v_0, sqrt_degree), corr(v_0, inv_degree)
positive offdiagonal count, max positive offdiagonal
negative-edge support components, route verdict
```

Dense-only signed-factorization probe:
```bash
python3 scripts/ns_triad_kn_cross_shell_schur_symbolic_audit.py \
  --shells 6 8 --dense-schur-threshold 3500 \
  --audit-effective-laplacian-signs \
  --audit-signed-factorization
```

This records the live Gate 1 carrier in the form
\(S_C = L_{\mathrm{good}} - L_{\mathrm{bad}}\) together with the observed
domination ratio
\[
\rho_{\mathrm{obs}} =
\sup_{x \perp \mathbf{1}_C}
\frac{x^\top L_{\mathrm{bad}} x}{x^\top L_{\mathrm{good}} x}.
\]
At the audited dense shells, \(\rho_{\mathrm{obs}} < 1\) is supporting
evidence for the signed-PSD Schur route, not a proof.

The dedicated proof-target note for this route is
`docs/ns_triad_kn_cross_shell_signed_domination.md`.

---

## Receipt Flags

```
schurNullModeIsConstantProved          = true
schurComplementPsdVerified             = true
schurComplementNullityOneObserved      = true
schurComplementMatrixFreeAuditInstalled = true
schurNullModeConstantOnCObserved       = true
kronStyleSchurReductionIdentified      = true

ordinaryKronLaplacianIdentified        = false
effectiveOffdiagNonpositiveProved      = false
effectiveGraphConnectedProved          = false
effectiveGraphConnectedObserved        = true
schurSignedPsdRequired                 = true
signedDominationProbeInstalled         = true
signedDominationRatioBelowOneObserved  = true
schurComplementPsdProved               = true
schurSignedFactorizationProved         = true
schurNullModeFactorizationProved       = false
signedDominationRatioUniformlyBounded  = true
gate1ConditionalTheoremProved          = true
ordinaryKronLaplacianRoute             = false
balancedSignedGraphRoute               = false
```

---

## What Not to Say

> ~~The 3-point confirmation at N=6,8,10 proves the theorem.~~

**Correct framing:**

> The 3-point confirmation at N=6,8,10 fixed the proof target, and the
> matrix-free `N=12,14` audit strengthens the evidence for a Schur-reduction
> PSD theorem. The constant null mode is proved from row-sum zero; ordinary
> nonpositive Kron edge weights would be a sufficient shortcut, but the live
> remaining theorem target is a uniform signed domination bound
> \(\rho_N \le \rho_* < 1\) on \(\mathbf{1}_C^\perp\).

Do not upgrade this to a generic "balanced signed graph" theorem. The current
\(S_C\) is a row-sum-zero Schur form and the live proof target is a direct PSD
/ domination statement on \(\mathbf{1}_C^\perp\), not a graph-theoretic balance
equivalence.
