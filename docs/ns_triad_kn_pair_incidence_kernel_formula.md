# NS triad exact pair-incidence kernel formula

Date: 2026-07-04

## Purpose

This note closes the definitional part of Stage 3 for the exact scripted
finite-to-tail operator. It turns the repeated-edge Laplacian definition into
an explicit cross-block kernel formula that can later be counted profile by
profile.

It does not prove the `C / N` operator bound. It fixes the exact kernel that
the weighted Schur-product route must estimate.

## Setup

Fix a shell cutoff `N`, an admissible amplitude profile `A`, and the retained
resonant triad set `T_N` from the current scripted carrier. For a triad

`tau = (i, j, l; gamma_tau)`

write

`m_N(tau) = (A_i A_j A_l / 3) * max(gamma_tau, 0)`.

Equivalently, on the current probability normalization

`m_N(tau) = (sqrt(pi_i pi_j pi_l) / 3) * max(cos(phi_i + phi_j - phi_l), 0)`.

Let `P(tau) = {(i,j), (i,l), (j,l)}` be the three unordered pair edges of the
triad, and let `b_{ab} = e_a - e_b` be the standard incidence vector of the
unordered edge `{a,b}`.

The exact positive-sector Laplacian is

`L_+(A) = sum_(tau in T_N) sum_(e in P(tau)) m_N(tau) b_e b_e^T`.

The finite-to-tail scripted operator is the corresponding cross block:

`L^N_{FT,script}(k,p) = (L_+(A))_{k,p}`

for `k` in the finite carrier and `p` in the tail carrier.

## Kernel Formula

For a finite mode `k` and a tail mode `p`,

`L^N_{FT,script}(k,p) = -sum_(tau : {k,p} in P(tau)) m_N(tau)`.

Equivalently, the nonnegative Schur kernel is

`K^N_{kp} := -L^N_{FT,script}(k,p) = sum_(tau : {k,p} in P(tau)) m_N(tau)`.

So the exact scripted cross block is a repeated-pair incidence kernel: each
retained resonant triad contributes its positive-sector weight to each of its
three unordered pair edges, and the `(k,p)` entry accumulates exactly the
weights of the triads whose pair set contains `{k,p}`.

## Proof

Take one triad `tau` and one of its pair edges `e = {a,b}`. The corresponding
rank-one Laplacian contribution is

`m_N(tau) b_{ab} b_{ab}^T = m_N(tau) (e_a - e_b)(e_a - e_b)^T`.

Its `(k,p)` entry is:

- `-m_N(tau)` if `{k,p} = {a,b}`,
- `0` otherwise.

This is the standard off-diagonal sign pattern of a graph Laplacian: the
diagonal entries are positive edge masses, and each off-diagonal entry is the
negative sum of the weights of the edges joining the two vertices.

Summing over all three pair edges of the triad, and then over all retained
triads, the only contributions that survive in the `(k,p)` entry are the triads
for which `{k,p}` is one of the three unordered pair edges. Therefore

`(L_+(A))_{k,p} = -sum_(tau : {k,p} in P(tau)) m_N(tau)`,

which is exactly the claimed formula.

Since `A_i A_j A_l >= 0` and `max(gamma_tau, 0) >= 0`, every summand `m_N(tau)`
is nonnegative. Hence `K^N_{kp} >= 0`.

## Consequence For Stage 3

The live weighted Schur route should be applied to the nonnegative kernel

`K^N_{kp} = -L^N_{FT,script}(k,p)`.

That reduces the next open work to:

1. decompose the repeated-pair incidence count into geometric profiles,
2. choose weights `w_N`,
3. prove `R_N(w_N) * C_N(w_N) <= C^2 / N^2`,
4. deduce `||L^N_{FT,script}||_op <= C / N`.

So the kernel-formula step is no longer the live obstruction. The first open
nontrivial Stage 3 theorem is now the profile decomposition together with the
weighted Schur-product estimates.
