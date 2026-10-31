# RTX retained signed matrix ↔ prime correlation and Pickover 9999 steelman (2026-10-31)

## Source audit / ownership

Read chboishabba/dashiRTX `README.md`: PDA/MDL signed frontier S0, reprojection errors, learned refresh mask, quadtree/ultrametric transport; the repository reports *rendering benchmark measurements*, not a theorem about signed arithmetic correlations. Original dashiRTX scripts include `pda_mdl_light_transport_test.py`, `pda_mdl_light_transport_test_fixed.py`, and `dashi_test_pda_mdl_light_transport_kernel.py`. Read existing DASHI `RTXLightTransportRefinementExact`: `iteratedRefinementPreservesObservation` follows from a genuine observation-preservation witness, while `lowerMDLIsPhysicalTruth` is explicitly false. The existing `TwinPrimeResidualMangoldtBidiExact` and Pickover PR #1260 preserve concrete consumer-relevant history; do not replace these with a coarse frequency average.

## Finite matrix identity (actual signed arithmetic carrier)

For `f(n)=Lambda(n)` on `2<=n<=X`, zero elsewhere, take `M>2X+2`. With `F(k)=sum_n f(n)exp(-2*pi*i*k*n/M)`,

`S(X)=sum_n f(n)f(n+2)=(1/M)sum_k |F(k)|² exp(-4*pi*i*k/M)`.

Define an exact disjoint partition of the frequency indices into any shells `B_j`. The retained shell history consists of the **full complex individual terms** (or a lossless representation thereof), with signed shell observable
`T_j(X)=Re[(1/M)sum_{k in B_j}|F(k)|²exp(-4*pi*i*k/M)]`. Then `S(X)=sum_j T_j(X)`; the equality is exact if all terms are retained. The zero-frequency term is `D(X)=(sum f)^2/M`. A formally valid universal lower bound is
`S(X)>=D(X)-(1/M)sum_{k != 0}|F(k)|²`.
This is not a helpful positive lower bound: it discards precisely the signed phase information; keeping full history reconstructs the *actual* S, but a bound on signed cancellation is still independently necessary.

## Measured estimates, not just diagrams

New Python probe `scripts/check_twin_prime_rtx_retained_signed_matrix.py` constructs actual classical Mangoldt prime-power weights via exact integer sieve + floating log, FFT, disjoint dyadic index shells, and reports S/X, zero-frequency term D/X, signed nonzero contribution, naive universal lower bound and total absolute shell budget. Local numerical run:

|X|S/X|D/X|non-DC/X|absolute spectral budget/X|
|--:|--:|--:|--:|--:|
|100|1.128880|0.345489|0.783391|2.178815|
|1000|1.135463|0.485045|0.650418|3.748844|
|10000|1.330292|0.305994|1.024298|5.422181|
|100000|1.315229|0.381863|0.933366|6.817977|

The absolute spectral budget increasingly exceeds the actual shift-two correlation. Therefore the unqualified triangle-inequality estimate is *getting worse as an asymptotic discriminator*, despite exact signed reconstruction. This is a concrete falsification of a naive nonnegative-energy promotion, not a lower bound establishing infinitely many twins. FFT floating-point comparisons are numerical diagnostics, not interval-certified computation.

## Two BIDI steelman targets, including their terminal quantitative gates

### Twin primes

T0: `cofinally true TwinPrimeAt(n)` iff `P(X)` unbounded (`P=S-E` classical **real** log-weight sum). T1: positive limsup S/X; T2: positive liminf; T3: Hardy–Littlewood weighted S~2C2X; T4: unweighted pi2~2C2 Li2. Existing proper-power estimate E=o(X) is classical elementary. The *missing* signed Fourier estimate can be phrased relative to a **specified** main-frequency decomposition:
`sum_{k != 0} |F_X(k)|² cos(4*pi*k/M)/M = 2C2 X - D(X) + o(X)`.
This is an explicit, independent arithmetic statement rather than an arbitrary remainder definition, and remains an open consequence-equivalent restatement of the Hardy–Littlewood main term. A weaker goal is any cofinal lower bound `D+signedNonDC-E>0` on arbitrarily late windows; the exact history guarantees identity but **not** the inequality.

### Pickover 9999 terminal sign

Define `N=99^(9999!)` exactly (do not conflate with `9999!` alone). The needed consumer is `sgn sin N`, equivalently parity of `floor(N/pi)`, since N/pi is not an integer. More usefully, from the actual Bishop phase `z(N)=cos N+i sin N`, a certified rational complex enclosure `|Im z_approx - sin N| <= eps` and `|Im z_approx|>eps` gives a sign. Pickover PR #1260's `ActualAnalyticTerminalPhase` requires the real analytic producer; retaining prior/live/terminal history and being able to reopen coarse phase projection alone do not provide the quantitative enclosure. A proposed dashiRTX-style matrix evolution must carry **signed** terminal error with an explicit norm bound; proof of sign separation is still required. Purely finite periodic 270/101/369 labels cannot yield a universal true-sign readout.

## Explicit shared operator interface (future theorem, not assumed)

Given exact state `v`, transport `T`, observer `L`, approximation `Ttilde` and error operators, the telescoping equality
`T^n - Ttilde^n = sum_{j=0}^{n-1} Ttilde^(n-1-j) (T-Ttilde) T^j`
holds for linear endomorphisms on a common module (check orientation). Taking a submultiplicative norm yields a **quantitative** absolute-error upper bound if independent norm and growth estimates are supplied. It applies to RTX radiance and Pickover wave-phase approximation, or finite Fourier transport as *algebra*, but the resulting magnitude bound does not establish an arithmetic shifted-prime lower bound. No identification of light radiance, complex phase, and von Mangoldt as the same state is asserted.

## Max-cut

1. Import/reuse an actual finite cyclic harmonic algebra; kernel prove shell reconstruction and error telescoping, keeping signed residuals.
2. Distinguish full retained state/phase from lossy low-rank or shell-averaged projections using consumer-relevant collision tests.
3. For Pickover: certify true Bishop terminal imaginary-coordinate enclosure separated from zero.
4. For twins: prove signed arithmetic correlation lower bound beyond sieve parity (T0), or T3 signed-frequency asymptotic with singular series.
5. Attribute separately the historic Hardy–Littlewood conjecture, original LP/Bony mathematics, original dashiRTX implementation, original DASHI/9999/prime-fibre theorem owners. No ESD edits.

**Status:** quantitative finite probes and algebraic estimate proposals; neither analytic arithmetic estimate nor Pickover terminal certificate is proved. No Agda kernel verification claimed.
