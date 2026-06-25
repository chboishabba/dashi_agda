# Gate 1 Phase Admissibility — Corrected Architecture

## DASHI Weight Convention

The cross-shell block operator \(K_N\) uses the sign-split phase-coherence weight:

\[
\gamma_e = \cos(\phi_\ell + \phi_r - \phi_o), \qquad
w_{\text{neg}} = \max(-\gamma_e, 0), \qquad
w_{\text{abs}} = |\gamma_e|
\]

Each seam edge is either fully negative (\(\gamma_e < 0\)) or fully positive (\(\gamma_e \geq 0\)). This is not the smooth \((1-\cos)/2\) phase-distance weight.

---

## Level 0 — Exact (Tautological) Target

\[
\boxed{L_{\text{neg,cross}} - \tfrac19 L_{\text{abs,cross}} \succeq 0}
\]

The PSD inequality itself. The goal.

---

## Level 1a — Schur PSD (Correct Sufficient Condition)

Partition the seam vertex set into \(G = \{\text{shell }1\}\) (corner) and
\(C = \{\text{shell }N-1, \text{shell }N\}\) (bulk).  Write

\[
M = L_{\text{neg,cross}} - \tfrac19 L_{\text{abs,cross}}
= \begin{pmatrix} M_{GG} & M_{GC} \\ M_{CG} & M_{CC} \end{pmatrix}.
\]

**Lemma (Schur ⇒ PSD).** If:

1. \(M_{GG} \succeq 0\),
2. \(\operatorname{range}(M_{GC}) \subseteq \operatorname{range}(M_{GG})\), and
3. the Schur complement \(S = M_{CC} - M_{CG} M_{GG}^+ M_{GC} \succeq 0\),

then \(M \succeq 0\) (Level 0).

**Status for the forced-tail seam graph:**

| Condition | Status | Evidence |
|-----------|--------|----------|
| \(M_{GG} \succeq 0\) | ✅ | No G–G edges in seam, so \(M_{GG} = 0\) (trivially PSD). |
| \(\operatorname{range}(M_{GC}) \subseteq \operatorname{range}(M_{GG})\) | ✅ | \(M_{GG} = 0\) reduces this to \(M_{GC} = 0\). Supported by \(B_{\text{cross}} = 0\) at all tested N (B-Cross Separation Lemma). |
| **\(M_{CC} \succeq 0\)** | **⬜ OPEN** | **The single Gate 1 target.** |

---

## Level 1b — Cut Domination (Downstream Diagnostic Only)

Cut domination requires:

\[
\forall S \subset V_{\text{seam}}:\;
\frac{\sum_{e \in E_-(S)} |\gamma_e| w_e}
     {\sum_{e \in E(S)} |\gamma_e| w_e}
\;\ge\; \frac19
\]

**Warning:** Cut domination is **weaker** than Loewner/PSD domination. Spectral
sparsification theory confirms that every Loewner sparsifier is a cut
sparsifier, but the converse fails in general. Cut control on indicator
vectors does not imply quadratic-form control on all real vectors.

In the hierarchy:

\[
\underbrace{M \succeq 0}_{\text{Level 0}} \;\Longrightarrow\;
\underbrace{\text{every cut} \geq 1/9}_{\text{Level 1b}}
\]

The arrow does **not** reverse. Level 1b is a necessary consequence of the
target, not a path to it.

---

## Level 2 — Waleffe Helical Decomposition (Motivation Only)

Waleffe (1992) decomposes every triad into 8 helical classes \((s_k, s_p, s_q)\).
The F-class (\(s_p = -s_q\), forward cascade) is dynamically amplifying and
accounts for \(\sim 86\%\) of energy flux. The \(\phi = 0\) collapse (all
\(\gamma_e = 1\)) corresponds to the degenerate case where the F-class
vanishes — not on the turbulent attractor.

**This is motivational, not a proof route.** The Waleffe interaction
coefficient and the DASHI coherence weight \(\gamma_e\) are correlated under
a chosen helical projection but are not identically signed objects.
Treating the W→C sign identity as a high-confidence theorem target is not
warranted.

---

## The Single Open Gate

\[
\boxed{M_{CC} \succeq 0}
\]

where \(C = \{\text{shell }N-1, \text{shell }N\}\) is the bulk of the seam
block. Prior computations found \(\lambda_{\min}(K_{\text{cross},N}) \approx
0.158\text{–}0.175\) across \(N=6,8,10,12\), so the empirical evidence
supports that \(M_{CC} \succeq 0\) holds at \(c_0 = 1/9\). The Schur audit
script will determine whether this is symbolically provable.

---

## Obligation Stack

| Level | Condition | Status | Target |
|-------|-----------|--------|--------|
| 0 | \(L_{\text{neg,cross}} - (1/9)L_{\text{abs,cross}} \succeq 0\) | **⬜ OPEN** | Gate 1 |
| 1a | \(M_{GG} \succeq 0,\; M_{GC} = 0,\; M_{CC} \succeq 0\) | Partial | M_GG, M_GC done; M_CC ⬜ |
| 1b | Every cut \(\geq 1/9\) negative fraction | Downstream | Demoted — not a proof path |
| 2 | Waleffe helical F-class | Motivation | Not a proof |

---

## Related Files

- `ns_triad_kn_cross_shell_block_floor.md` — Schur complement structure, PSD certificate
- `ns_triad_kn_cross_shell_leakage_bound.md` — leakage bound, B-cross separation lemma
- `DASHI/Physics/Closure/NSTriadKNCrossShellLeakageBoundReceipt.agda` — receipt with obligation tracking
