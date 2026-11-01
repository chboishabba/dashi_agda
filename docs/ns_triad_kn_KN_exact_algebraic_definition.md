# NS triad exact algebraic definition of `K_N(A)`

Date: 2026-06-25

## Purpose

This note closes the object-definition part of Gate 1. It defines the live
high-high Gram operator `K_N(A)` without reference to any one diagnostic run and
matches that algebraic object to the current scripted matrix construction.

It does not prove coercivity. It fixes the object, the normalization, the
admissible profile surface, and the exact script-to-algebra dictionary needed
before diagonal/coherence estimates can be attempted.

## Carrier And Admissible Profiles

Fix a shell cutoff `N` and let `M_N` be the finite set of shell-selected modes
used by the active high-high carrier. Let `T_N` be the corresponding finite set
of admissible high-high triads

`t = (i, j, k; gamma_t)`

with mode indices `i, j, k in M_N` and signed coherence `gamma_t in [-1, 1]`.

An admissible amplitude profile is a nonnegative mode profile

`A : M_N -> [0, +infty)`

coming from the current scripted probability surface by

`A_m = sqrt(max(p_m, 0))`

for a shell-selected probability vector `p`. The profile is admissible on this
 carrier when:

- `A_m >= 0` for every `m in M_N`,
- the triad carrier is the same shell-selected high-high carrier used to build
  the scripted edge-incidence object,
- the induced absolute operator `L_abs(A)` is not identically zero on the
  selected carrier, so `im(L_abs(A))` is defined as the positive subspace used
  by the current generalized eigen solve.

This note records the exact current profile class. It does not yet prove that
this is the final sharp theorem class for the eventual coercivity bound.

## Triad Weighting

For each admissible triad `t = (i, j, k; gamma_t)`, define the raw triad weight

`w_t(A) = A_i A_j A_k`.

The scripted construction splits this weight equally across the three pair edges
of the triad, so the pair weight is

`w_t^pair(A) = w_t(A) / 3`.

The sign split is determined by the coherence:

`w_t^neg(A) = w_t^pair(A) * max(-gamma_t, 0)`

`w_t^pos(A) = w_t^pair(A) * max(gamma_t, 0)`

`w_t^abs(A) = w_t^pos(A) + w_t^neg(A) = w_t^pair(A) * |gamma_t|`.

So the exact normalization factors are:

1. amplitude square root from the probability profile,
2. cubic triad weight `A_i A_j A_k`,
3. equal `1/3` split across the three unordered mode pairs,
4. sign split by `max(±gamma_t, 0)`,
5. absolute weight `|gamma_t|` on the absolute operator.

## Pair-Incidence Operator

For each triad `t = (i, j, k; gamma_t)`, introduce its three unordered pair
edges

`(i, j)`, `(i, k)`, `(j, k)`.

For an unordered pair edge `e = {a, b}`, let `b_e in R^{M_N}` be the standard
edge-incidence vector

`b_e = e_a - e_b`.

The exact scripted operator is the repeated-edge Laplacian sum

`L_abs(A) = sum_(t in T_N) sum_(e in P(t)) w_t^abs(A) b_e b_e^T`

`L_neg(A) = sum_(t in T_N) sum_(e in P(t)) w_t^neg(A) b_e b_e^T`

where `P(t) = {(i, j), (i, k), (j, k)}` is the triad pair set. Equivalently,
if `B_N` is the rectangular incidence matrix with one row per repeated pair
edge, and `W_abs(A)`, `W_neg(A)` are the diagonal matrices of edge weights, then

`L_abs(A) = B_N^T W_abs(A) B_N`

`L_neg(A) = B_N^T W_neg(A) B_N`.

This is the same operator family used by the matrix-free implementation:

- `scripts/ns_triad_kn_matrix_free_operator.py`
- `scripts/ns_triad_kn_exact_identity_scan.py`

## Normalized Gram Operator

The live theorem object is the positive-subspace normalized negative block

`K_N(A) = L_abs(A)^(-1/2) L_neg(A) L_abs(A)^(-1/2)`.

Here `L_abs(A)^(-1/2)` means the inverse square root on the positive subspace
`im(L_abs(A))`, implemented by the current spectral pseudoinverse
construction:

- diagonalize `L_abs(A)`,
- keep only eigenvalues `> tol`,
- rescale each kept eigendirection by `lambda^(-1/2)`.

So all statements about `K_N(A)` are statements on `im(L_abs(A))`, not on the
full ambient mode space.

The Rayleigh quotient is therefore

`R_A(v) = <v, K_N(A) v> = <x, L_neg(A) x> / <x, L_abs(A) x>`

with `v = L_abs(A)^(1/2) x` on the positive subspace. The Gate 1 target remains

`lambda_min(K_N(A)) = inf_(|v|_2 = 1) <v, K_N(A) v> >= c / N`.

## Script Match

The current scripted matrix and the algebraic object above match as follows.

In `scripts/ns_triad_kn_matrix_free_operator.py`:

- `build_profile(...)` constructs the repeated pair-edge carrier,
- `weights_abs` are exactly the edge weights `w_t^abs(A)`,
- `weights_neg` are exactly the edge weights `w_t^neg(A)`,
- `matvec_abs` and `matvec_neg` apply the Laplacians
  `L_abs(A)` and `L_neg(A)`,
- `dense_laplacians_from_matvec(...)` materializes those same operators,
- `dense_parity_adapter(...)` restricts to `im(L_abs(A))` and computes the
  eigenvalues of the conjugated matrix `K_N(A)`.

In `scripts/ns_triad_kn_exact_identity_scan.py`, the same normalization is used
to record the corrected signed identity

`L_signed = L_abs - 2 L_neg`

`L_signed_norm = I - 2 K_N`

on `im(L_abs)`.

Therefore the current dense scripted matrix for the generalized eigen lane is
not a new object. It is exactly the algebraic `K_N(A)` attached to the repeated
pair-incidence Laplacians above.

## Gate-1 Exactness Status

Written here:

- exact algebraic definition of `K_N(A)`,
- exact definitions of `L_abs(A)` and `L_neg(A)`,
- exact current admissible-profile surface,
- exact normalization factors,
- exact script-to-algebra match.

Still open after this note:

- a theorem-level proof that every scripted matrix instance is exactly this
  algebraic object in all later variants,
- diagonal mass lower bound,
- coherence / off-diagonal control,
- admissible-profile theorem sharpness,
- the coercive lower bound `lambda_min(K_N(A)) >= c / N`.

This note is fail-closed and object-fixing only.
