# NS triad cross-shell Rayleigh mechanism

Date: 2026-06-25

## Thesis

The sampled worst Rayleigh direction for the live Gram operator is not a generic
high-high mode. In the current receipts it localizes on low-high-high shell
triples of the form

`(1, N - 1, N)`

or the equivalent ordering

`(1, N, N - 1)`.

So the active seam is best described as:

- low-high-high Gram coercivity at the high-high seam,
- or near-diagonal high-high output driven by a low-shell cross-shell lever.

This note is fail-closed. It records a candidate mechanism for the sampled
`1 / N` scale. It does not prove the global theorem

`lambda_min(K_N(A)) >= c / N`.

## Mechanism Boundary

The algebraic Biot-Savart factor satisfies

`|k x p| / |k|^2 <= |p| / |k|`.

Therefore for a low-vs-high shell interaction with `|p| = O(1)` and
`|k| ~ N`,

`|k x p| / |k|^2 <= C / N`.

This is the geometric source of the sampled `1 / N` scale. It identifies the
natural size of the dangerous cross-shell channel. It does not by itself give a
coercive lower bound for `K_N(A)`.

The correct theorem-shaped statement is:

- the sampled worst direction appears to live in a cross-shell `1-N-(N-1)`
  channel,
- that channel carries a natural `1 / N` Biot-Savart scale,
- the next proof task is to show this channel is the global worst block and
  still retains a positive Rayleigh margin of order `c / N`.

## Current Sampled Read

The current Rayleigh-margin receipts show worst support on:

- `N = 6`: `[1, 6, 5]`
- `N = 8`: `[8, 7, 1]`
- `N = 10`: `[10, 9, 1]`
- `N = 12`: `[12, 11, 1]`

and dominant negative shell pairs on:

- `1-6`, `1-5`, `5-6`
- `1-8`, `1-7`, `7-8`
- `1-10`, `1-9`, `9-10`
- `1-12`, `1-11`, `11-12`

So the sampled minimizing direction is concentrated on the `1-(N-1)-N`
cross-shell block, not on a pure same-shell high-high block.

## Revised Lemma Stack

1. Cross-shell Biot-Savart decay
   - Prove `|k x p| / |k|^2 <= |p| / |k|`.
   - For shell pair `1-N`, this gives an exact upper-bound mechanism of order
     `1 / N`.
   - Status: closed as geometry; not a coercivity theorem.

2. Worst-direction localization
   - Show the minimizer `v_min(K_N(A))` localizes on the
     `1-(N-1)-N` block.
   - Status: strongly sampled, theorem open.

3. Cross-shell Rayleigh lower bound
   - On the localized block, prove
     `<v, K_N(A) v> >= (c / N) * |v|_2^2`.
   - Status: core estimate, open.

4. Complement-subspace comparison
   - Show all vectors outside the dangerous cross-shell block have Rayleigh
     quotient at least as large, or larger.
   - Status: needed to turn block control into global `lambda_min` control.

5. Admissible profile condition
   - State the exact amplitude-profile class preventing profile degeneration and
     preserving a shell-uniform denominator.
   - Status: essential and open.

## Theorem Boundary

Do not state:

- `lambda_min(K_N(A)) ~ 1 / N because |p| / |k| = 1 / N`.

State instead:

- the sampled worst direction is cross-shell,
- the Biot-Savart homogeneity gives the correct candidate `1 / N` scale on that
  channel,
- the theorem still requires a lower-bound argument on the dangerous block plus
  a comparison showing no other block is worse.

## Next Computation

The next diagnostic should be a shell-block decomposition of `K_N(A)` with
blocks such as:

- `(1, N - 1, N)`
- `(1, N, N - 1)`
- `(N, N, N)`
- `(N / 2, N, N)`

For each block, record:

- `block_lambda_min`
- `block_rayleigh_mass_of_global_vmin`
- `block_diag`
- `block_cross`
- `N * block_lambda_min`

The point is to determine whether the `1-(N-1)-N` block is genuinely the
universal dangerous block or only the worst block on the current sampled
profiles.

## Promotion Boundary

- No theorem promotion.
- No full-NS promotion.
- No BKM exclusion claim.
- No residence-time exclusion claim.
- No Clay promotion.
