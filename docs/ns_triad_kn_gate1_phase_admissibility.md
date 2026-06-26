# Gate 1 Phase Admissibility — Corrected Architecture

## DASHI Weight Convention

\[
\gamma_e = \cos(\phi_\ell + \phi_r - \phi_o), \qquad
w_{\text{neg}} = \max(-\gamma_e, 0), \qquad
w_{\text{abs}} = |\gamma_e|
\]

Each seam edge is either fully negative (\(\gamma_e < 0\)) or fully positive (\(\gamma_e \geq 0\)).

---

## Level 0 — Exact (Tautological) Target

\[
\boxed{L_{\text{neg,cross}} - \tfrac19 L_{\text{abs,cross}} \succeq 0}
\]

---

## Level 1a — Schur PSD (Correct Sufficient Condition)

Partition the seam vertex set into \(G = \{\text{shell }1\}\) and
\(C = \{\text{shell }N-1, \text{shell }N\}\).  Write

\[
M = L_{\text{neg,cross}} - \tfrac19 L_{\text{abs,cross}}
= \begin{pmatrix} M_{GG} & M_{GC} \\ M_{CG} & M_{CC} \end{pmatrix}.
\]

**Lemma (Schur ⇒ PSD).** If \(M_{GG} \succ 0\),
\(\operatorname{range}(M_{GC}) \subseteq \operatorname{range}(M_{GG})\), and
\(S = M_{CC} - M_{CG} M_{GG}^+ M_{GC} \succeq 0\), then \(M \succeq 0\).

### Schur Audit Results (numerical, `ns_triad_kn_cross_shell_schur_symbolic_audit.py`)

| N | M_GG rank | M_GG λ_min | ‖M_GC‖ | M_CC n | M_CC λ_min | M_CC nullity | Verdict |
|---:|---:|---:|---:|---:|---:|---:|:---|
| 6 | 26/26 | 1.23e-04 | 4.36e-03 | 1468 | 1.74e-05 | 0 | mcc_psd |
| 8 | 26/26 | 1.84e-04 | 4.35e-03 | 2716 | 7.63e-06 | 0 | mcc_psd |
| 10 | 26/26 | 1.35e-04 | 4.34e-03 | 4348 | 4.29e-06 | 0 | mcc_psd |
| 12 | 26/26 | 8.22e-05 | 4.34e-03 | 6364 | 2.70e-06 | 0 | mcc_psd |

**Key findings:**
1. \(M_{GG} \succ 0\) at all audited N (full rank, λ_min ~ 1e-4)
2. \(M_{GC} \neq 0\) but small (‖M_GC‖ ≈ 4.3e-3, stable across N)
3. \(M_{CC} \succ 0\) at all audited N, but this is no longer the load-bearing target
4. The Schur null mode is almost perfectly correlated with \(\mathbf{1}_C\)
5. Since \(M\mathbf{1}=0\), the Schur complement satisfies \(S\mathbf{1}_C=0\) exactly

So the constant null direction is analytically forced. The open issue is not
identifying the null mode; it is proving that \(S\) is PSD on
\(\mathbf{1}_C^\perp\). Ordinary Laplacian signs would be a strong sufficient
shortcut, not the definition of admissibility.

---

## Level 1b — Cut Domination (Downstream Diagnostic)

Cut domination is a **necessary consequence** of Level 0, not a path to it.
Spectral sparsification theory confirms: every Loewner sparsifier is a cut
sparsifier, but the converse fails.

\[
\underbrace{M \succeq 0}_{\text{Level 0}} \;\Longrightarrow\;
\underbrace{\text{every cut} \geq 1/9}_{\text{Level 1b}}
\]

The arrow does **not** reverse.

---

## Level 2 — Waleffe Helical Decomposition (Motivation Only)

Waleffe (1992) decomposes every triad into 8 helical classes. The F-class
(\(s_p = -s_q\), forward cascade) is dynamically amplifying, accounting for
∼86% of energy flux. The ϕ=0 collapse (all γ_e=1) corresponds to the
degenerate case where the F-class vanishes — not on the turbulent attractor.

**This is motivational, not a proof route.**

---

## The Sharp Open Gates

\[
\boxed{
\text{Level 0 exact target: } S_C \succeq 0
\quad\text{and}\quad
\ker S_C = \operatorname{span}\{\mathbf{1}_C\}.
}
\]

The strongest checkable shortcut is:

\[
\boxed{
\text{(i) } -S_{ij} \ge 0 \text{ for all } i \neq j \in C
\qquad\text{and}\qquad
\text{(ii) the negative-edge support graph on } C \text{ is connected.}
}
\]

Because \(M\mathbf{1}=0\), condition (i) makes \(S\) an ordinary graph
Laplacian on \(C\). Then condition (ii) upgrades this to
\(\ker S = \operatorname{span}\{\mathbf{1}_C\}\) and \(S \succeq 0\) on
\(\mathbf{1}_C^\perp\). If condition (i) fails, Gate 1 does not break; the
proof route simply shifts to a signed/sum-of-squares factorization of \(S_C\).
The dense Schur audit now records this fallback as
\[
S_C = L_{\mathrm{good}} - L_{\mathrm{bad}}
\]
with the observed domination ratio
\[
\rho_{\mathrm{obs}} =
\sup_{x \perp \mathbf{1}_C}
\frac{x^\top L_{\mathrm{bad}} x}{x^\top L_{\mathrm{good}} x}.
\]
The theorem target is a direct PSD / domination argument on
\(\mathbf{1}_C^\perp\), not a generic signed-graph balance equivalence.

---

## Obligation Stack

| Level | Condition | Status |
|-------|-----------|--------|
| 0 | \(L_{\text{neg,cross}} - (1/9)L_{\text{abs,cross}} \succeq 0\) | OPEN — **Gate 1** |
| 1a | \(M_{GG} \succ 0\) | ✅ numerically supported |
| 1a | \(\operatorname{range}(M_{GC}) \subseteq \operatorname{range}(M_{GG})\) | ✅ M_GG full rank |
| 1a | \(S_C \mathbf{1}_C = 0\) | ✅ analytic from \(M\mathbf{1}=0\) |
| 1a | \(S_C \succeq 0\) on \(\mathbf{1}_C^\perp\) | **⬜ OPEN exact Gate 1 theorem target** |
| 1a | Ordinary effective weights \(-S_{ij} \ge 0\) | **⬜ OPEN strong sufficient shortcut** |
| 1a | Ordinary Kron support connected | **⬜ OPEN only if the shortcut holds** |
| 1a | Signed domination/factorization of \(S_C\) on \(\mathbf{1}_C^\perp\) | **⬜ OPEN live route** |
| 1b | Cut domination ≥ 1/9 | Demoted (downstream diagnostic) |
| 2 | Waleffe helical | Motivation only |

---

## Related Files

- `ns_triad_kn_cross_shell_block_floor.md` — Schur complement structure, PSD certificate
- `ns_triad_kn_cross_shell_leakage_bound.md` — leakage bound, B-cross separation lemma
- `scripts/ns_triad_kn_cross_shell_schur_symbolic_audit.py` — Schur audit script
- `DASHI/Physics/Closure/NSTriadKNCrossShellLeakageBoundReceipt.agda` — receipt with obligation tracking
