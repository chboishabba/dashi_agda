# Balanced ternary shell sign, 369/27-cube, Pickover and twin-prime BIDI steelman
31 October 2026. Source-written audit; no new analytic theorem.

## Retain the trit and its value
Existing `DASHI.Physics.WaveAlgorithmLift.Trit` = neg | zero | pos, with exact sign involution and wave-phase mapping. Do NOT reduce to a binary `nonzero` bit. Nor replace the full scalar by its ternary sign: vectors (1,-3,1) and (2,-1,2) share the (+,-,+) trit cube cell but have different total signs. The full 27 = 3^3 set of sign triples is a legitimate coarse observer with many collisions. Pair it with signed magnitude, phase and history residual, reusing `TwinPrimeResidualMangoldtBidiExact.liftNatConsumer`. The new `TwinPrimeTernarySignedShellHistoryBidiExact.agda` preserves signed value and orientation pointwise through Nat<->period code. Full signed value prevents that particular information loss; it does not prove positivity. A further refinement of blockwise history is required to preserve signed partial sums at aggregation boundaries.

A truthful order-consistency interface must additionally prove that `orientation n` is the trichotomy of `value n` in a specified ordered scalar. The generic module intentionally *does not* claim this proof without ordered-real premises.

## The two independent terminal estimators

**Twins** (T0 exact BIDI): Let `S(X)=sum Lambda(n)Lambda(n+2)`, `E(X)` proper-prime-power support, `P=S-E` actual prime-only. Show unbounded P, equivalent to infinitely many twins given actual real log weights. Strong steelman: `S(X)=2*C2*X+o(X)`. Explicit Fourier remainder: with f zero-extended on cyclic M>2X+2, `D(X)=|F(0)|²/M` and `U(X)=sum_{k !=0}|F(k)|² cos(4*pi*k/M)/M`, need `U(X)=2*C2*X-D(X)+o(X)`. Retain exact signed shell components `T_j`, exact sum and their trits. The triangle bound `U>=-sum |T_j|` is valid but not competitive; sharpening it requires genuinely prime-specific correlation structure. Neither CRT survivors nor signed cube patterns alone imply the quantitative estimate.

**Pickover** (P0 exact BIDI): `N=99^(9999!)`; the terminal consumer is `sign(sin N)`. A sound certified complex-phase enclosure `|Im z_approx-sin N|<=eps` with `|Im z_approx|>eps` determines the sign. Retained previous/live/terminal Bishop phase from PR #1260 maintains history, with `ActualAnalyticTerminalPhase.terminalIsTrueTrig` needed to tie it to the real sine. Strong steelman: a proof-carrying contraction or unitary-error estimate for the actual phase algorithm, yielding a sign-separating terminal interval, with explicit bit/operation complexity. No purely symbolic ternary label gives that sign without such a certificate.

## Is Pickover RH-adjacent?

**Methodological analogy, not reduction.** Both the zeta zero problem and the Pickover huge-phase problem involve analytic continuation, oscillatory/complex functions, cancellation, precision budgets and certified enclosures. Existing DASHI `RiemannVonMangoldtSpecification` is relevant to shifted prime correlation because von Mangoldt coefficients explicitly appear; actual proof of Hardy–Littlewood prime-pair correlations needs information on *paired* prime distributions beyond RH alone. For sin N, RH neither gives a sign theorem nor an inexpensive modular phase oracle. The honest bridge is an *analytic certified-phase / explicit-formula methodology*, not a theorem claiming Pickover follows from RH or that RH implies twin primes.

## Adversarial acceptance tests
1. Same three trits, different signed sum (demonstrated with rational exact arithmetic); preserve scalar/residual to distinguish.
2. Signed Fourier shell decomposition reconstructs true shifted correlation; zero net correlation examples prevent unsigned-norm promotion.
3. Retain actual prime-one and proper-power provenance in real scalar; no synthetic density promotion.
4. For Pickover, true-phase equality and enclosures must target the exact giant exponent, not a small stand-in or a periodic finite chart.
5. Import source-owner terms instead of re-authoring ESD or Pickover PR #1260, which remains a separate branch; kernel-check code before calling it verified.

**Pending:** certified ordered-real trichotomy for actual shell scalars, finite signed shell sum algebra, quantitative signed estimate for twins, and quantitative terminal-phase bound for Pickover.
