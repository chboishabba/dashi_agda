# NS Triad K_N(A) Cross-Shell Block Floor

## Theorem Target

\[
\lambda_{\min}(K_{\mathrm{cross},N}) \ge c_0,
\qquad
K_{\mathrm{cross},N} = L_{\mathrm{abs,cross}}^{-1/2}\,
L_{\mathrm{neg,cross}}\,
L_{\mathrm{abs,cross}}^{-1/2}
\]

for the \(1\text{--}(N-1)\text{--}N\) seam block on the forced-tail profile
\(\eta = 0.25,\; K = N-1\).

Since \(B_{\mathrm{bc}} = 0\) is structurally proved for this profile, the
block generalised eigenproblem is isolated:

\[
L_{\mathrm{neg,cross}}\, v = \lambda\, L_{\mathrm{abs,cross}}\, v,
\qquad v \in \mathcal{V}_{1,N-1,N}.
\]

The floor is the minimum generalised Rayleigh quotient on the seam subspace:

\[
\lambda_{\min}(K_{\mathrm{cross},N})
= \min_{v \in \mathcal{V}_{1,N-1,N}}
\frac{\langle v, L_{\mathrm{neg,cross}}\, v \rangle}
{\langle v, L_{\mathrm{abs,cross}}\, v \rangle}.
\]

## Sampled Floor

| \(N\) | \(\lambda_{\mathrm{block}}\) | Source |
|---|---|---|
| 6 | 0.172016 | forced-tail K5 η=0.25 |
| 8 | 0.175021 | forced-tail K7 η=0.25 |
| 10 | 0.174431 | forced-tail K9 η=0.25 |
| 12 | 0.158031 | forced-tail K11 η=0.25 |

Conservative estimate: \(c_0 = 0.15\) (below all sampled values).

## Candidate Proof Route

### Step 1 — Enumerate the seam triads

The active triads for the forced-tail profile are exactly:

\[
\{(k_1, k_2, k_3) : |k_1|_\infty = 1,\; |k_2|_\infty = N-1,\; |k_3|_\infty = N,\;
k_1 + k_2 = k_3\}
\]

and permutations.  This is a finite, enumerable set for each \(N\); its size
scales as the surface area of the Chebyshev shell \(\{\,|k|_\infty = N\,\}\).

### Step 2 — Positive mass on the seam subspace

The triad weight for edge \((a,b)\) in the Laplacian is

\[
w_{ab} = \tfrac{1}{3}\sqrt{p(a)\,p(b)\,p(c)} > 0
\]

because all three modes have positive forced-tail probability.  Hence the
generalised mass operator \(L_{\mathrm{abs,cross}}\) is strictly positive on
the seam subspace.  Its smallest eigenvalue provides a coercivity constant
\(\alpha_N > 0\) for the denominator.

### Step 3 — Sign-fraction bound via azimuthal integral

For a fixed source mode \(k_{\text{src}}\) on shell \(N-1\) and target mode
\(k_{\text{tgt}}\) on shell \(N\), the triad coherence is

\[
\cos(\phi_{\text{src}} + \phi_{\text{src}'} - \phi_{\text{tgt}}).
\]

The admissible source set for a given target mode sweeps a full azimuthal
circle on the transverse \((N-1)\)-shell.  By the ACL half-sum structure:

\[
\frac{S_-}{S_{\text{abs}}} \ge \frac{1}{2},
\qquad
S_- = \sum_{\text{neg. coherent triads}} w,\;
S_{\text{abs}} = \sum_{\text{all triads}} w.
\]

This is the geometric heart: the azimuthal integral over the transverse
shell distributes the coupling equally between positive and negative
coherence sectors, fixing the Rayleigh ratio for each seam mode.

### Step 4 — Rayleigh min-max extraction

From the sign-fraction bound on each individual seam mode:

\[
\langle v, L_{\mathrm{neg,cross}}\, v \rangle
\ge c_0\, \langle v, L_{\mathrm{abs,cross}}\, v \rangle,
\qquad c_0 = \inf_{\text{mode}} \frac{S_-}{S_{\text{abs}}}.
\]

By the Rayleigh min-max principle, the block floor satisfies

\[
\lambda_{\min}(K_{\mathrm{cross},N}) \ge c_0.
\]

## Status

- Sampled: ✅ (all four shells above 0.158)
- Proved: ❌ (analytic azimuthal integral not yet closed)

## Dependencies

- [`ns_triad_kn_cross_shell_leakage_bound.md`](ns_triad_kn_cross_shell_leakage_bound.md) —
  B-cross separation lemma and leakage framework.
- [`ns_triad_kn_cross_shell_block_decomposition.py`](../scripts/ns_triad_kn_cross_shell_block_decomposition.py) —
  numerical sampled evidence.
