# Bishop/eta P2: actual compact-uniform Dirichlet eta estimate — 14 November 2026

## Source and provenance

Original selected finite eta: `DASHI/Analysis/BishopOriginalDirichletEtaFinitePairingExact.agda`, `OriginalRound11DirichletEta.sourceTerms` via `BishopRiemannDirichletExponentialTermExact.bishopDirichletExponentialTerm`. Selected exponent is `expC(-s*canonicalNatLog(k))` and `canonicalNatLog(k)` is intended to equal `log(k+1)`, not an arbitrary Nat-to-real map.

Original constructive real/completion: Bishop/Bridges, *Constructive Analysis* (1985), and Zachary Murray, *Constructive Analysis in the Agda Proof Assistant* (2022), arXiv:2205.08354. Dirichlet/Abel summation is classical. This document supplies the exact analytic proof target and its derivation; it is **not** a new Agda kernel-accepted theorem.

## The nontrivial complex-uniform tail is actually manageable

Let `s=sigma+i*tau`, `sigma>0`, `a_n=n^{-s}=exp(-s log n)`, and `N>=1`. For every `m>=1` let `A_j = sum_(k=0)^j (-1)^k`. Then `A_j` is exactly 0 or 1, and finite summation by parts gives

```
 sum_(j=0)^(m-1) (-1)^j a_(N+j)
  = A_(m-1) a_(N+m-1)
    + sum_(j=0)^(m-2) A_j (a_(N+j)-a_(N+j+1)).
```

Using the exact complex derivative `d/dx x^{-s}=-s x^{-s-1}` and the fundamental theorem along the **real positive** x-axis:

```
 |a_n-a_(n+1)| <= |s| integral_n^(n+1) x^(-sigma-1) dx.
```

The finite block hence obeys, for all `m`,

```
 |block_(N,m)(s)|
 <= (N+m-1)^(-sigma)
    + (|s|/sigma) (N^(-sigma)-(N+m-1)^(-sigma))
 <= (1+|s|/sigma) N^(-sigma).
```

For a compact `K` with `Re(s)>=delta>0` and `|s|<=M`, every finite tail satisfies

```
 sup_(s in K)|block_(N,m)(s)|
    <= (1+M/delta)*N^(-delta).
```

This tends uniformly to zero as `N->infty`. Therefore the **classical correctly represented** eta series is compact-uniformly convergent on `Re(s)>0`. The proof does **not** use the false bound `2/(N+1)^sigma` for complex alternating tails and does **not** require absolute convergence of the eta series.

## Exact original Agda weld still open

1. `OriginalNatLogMatchesPositiveRealLog`: certify selected `sourceCanonicalNatLogCandidate n = log(n+1)` on the **vendor Bishop real setoid**, with `log(1)=0` and multiplicativity. Source `OriginalDyadicNatLogLaw` is the selected even-scale consumer.
2. `OriginalComplexExpAddition`: either prove the two original `OriginalCosineAddition`/`OriginalSineAddition` identities or complete the generic factorial-complex Cauchy product and transport `BishopComplexExpFactEqualsNativeExpExact` to `expC(z+w)=expC(z)expC(w)`. Existing complex rectangle, triangle-tail and finite-binomial machinery must be reused.
3. `OriginalBishopComplexPositiveRealDerivative`: prove the derivative and FTC bound for exactly `expC(-s*log x)` using Bishop setoid real integrals, not an unrelated imported native-complex exponential.
4. `OriginalBishopEtaFiniteAbel`: transport the displayed exact finite Abel identity through `OriginalRound11DirichletEta.sourceTerms` and the **same** finite `originalEtaPrefix`.
5. `OriginalBishopEtaCompactUniform`: construct the compact-uniform limit with modulus `(1+M/delta)*N^-delta` and original indexed SeriesOf.
6. Retain nonzero denominator/removable-singularity proof as distinct if using `eta(s)=(1-2^(1-s))zeta(s)`; uniform eta convergence by itself proves neither RH nor zeta zero-freeness.

## Reproduce exact finite and numerical diagnostics

```sh
python3 scripts/check_bishop_eta_abel_uniform_tail.py
```

Finite rational Abel identity: **9841 complete cases** for sequences of length 0–8 over `{-3/2,0,2/3}`; 320 complex `s`/tail numerical diagnostics. This is evidence for the arithmetic and indexing **not** formal acceptance of the original Bishop analytic carrier.

Acceptance: pinned Agda 2.9/Nix original module, full transitive trust and no uninhabited log/exp/FTC sources. Status **A mathematics known / A-to-B original formalization OPEN**.
