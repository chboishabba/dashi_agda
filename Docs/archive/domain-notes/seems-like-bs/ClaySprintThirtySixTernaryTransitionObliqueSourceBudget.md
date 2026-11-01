# Clay Sprint 36 Ternary Transition and Oblique Source Budget

Sprint 36 records the transition-law correction:

```text
per-shell bad fraction != bad-lineage probability
```

A shell can have one dangerous trit out of three at every level and still have
`R_K^+ ~= 1/3` for all `K`.  That does not decay, and the weighted shell sum
diverges.

## Ternary Transition Row

The Clay-facing row is the positive row of the ternary transition matrix:

```text
R^+_(K+1)
  <= M_(+,-) R^-_K
   + M_(+,0) R^0_K
   + M_(+,+) R^+_K
   + source_K
```

The absorbed form is:

```text
R^+_(K+1) <= c * R^+_K + s_K
```

The closeable condition is:

```text
c * sqrt2 < 1
Sum_K 2^(K/2) * s_K < infinity
```

Then:

```text
Sum_K 2^(K/2) * R^+_K < infinity
```

This is a closed transition/source-budget algebra lemma.  It does not prove
that actual NS supplies such a `c` or such a summable source.

## Negative Micro-Lemma

Constant positive oblique fraction does not close:

```text
R^+_K = p > 0 for every K
```

implies:

```text
Sum_K 2^(K/2) * R^+_K = infinity
```

This kills the old symbolic branch-counting shortcut unless branch counting is
upgraded to real shell-mass/source decay.

## Oblique Source

Oblique geometry creates the real adversary, but angular probability alone is
not decay.  For tube angle `alpha`:

```text
a(alpha) = sin^2(alpha)
```

The dangerous angular fraction is constant at each scale, not summable by
itself.

The oblique source functional is:

```text
s_obl(K) =
  ||Pi_danger,K+1 P_(K+1)[(u_K dot grad) omega_K]||_2
  / (2^(K/2) * D_K + epsilon)
```

The effective source includes all nonlinear vorticity source terms:

```text
s_eff(K) =
  ||Pi_danger,K+1
      P_(K+1)[(u dot grad)omega - (omega dot grad)u]||_2
  / (2^(K/2) * D_K + epsilon)
```

The hard source theorem is:

```text
Sum_K 2^(K/2) * s_eff(K) < infinity
```

or, in the more specific oblique lane:

```text
ObliqueStrainCrossShellCouplingDecays
```

## Source Decay Threshold

If:

```text
s_obl(K) = S0 * q^K
```

then weighted source summability needs:

```text
q * sqrt2 < 1
```

So oblique source amplitude must decay faster than `2^(-K/2)`.

## Low Shells

For fixed viscosity `nu > 0`, shells below the Kolmogorov scale are finite:

```text
Sum_{K <= ceil(K_Kolm(nu))} 2^(K/2)
```

This contributes a `nu`-dependent finite constant.  It is not the Clay-hard
infinite-tail problem.

## Pass / Fail Tests

For each shell, output:

```text
K
R_K^-
R_K^0
R_K^+
M_(+,+) = c_K
s_oblique_K
s_external_K
s_eff_K
2^(K/2) * s_eff_K
partial_sum_source
Q_K
C_K = Q_K / (R_K^+ + epsilon)
concentrationRatio_K
```

Pass conditions:

```text
sup_K C_K < infinity
sup_K c_K < 1 / sqrt2
Sum_K 2^(K/2) * s_eff_K < infinity
concentration exponent beta < 2
```

## Worker Lanes

```text
W1: compute the ternary transition positive row and M_(+,+)
W2: estimate oblique/external/effective source summability
W3: prove or falsify Q_K <= C R_K^+
W4: estimate concentration ratio and beta
W5: carry forward Gate3 Mosco and YM rho/leakage as separate false gates
W6: validate aggregate Agda and keep all promotion flags false
```

## Boundary

This sprint records transition/source-budget algebra and analytic audit
surfaces only.  It does not prove the physical bridge, persistence bound,
weighted source summability for actual NS, no concentration, oblique
cross-shell decay, Gate3 Mosco/no-pollution, YM nonperturbative uniformity,
Lean-port work, or any Clay promotion.
