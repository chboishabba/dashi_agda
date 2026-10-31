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


## Hyperfabric / hypervoxel / p-adic / cubie strengthened Pickover 9999 steelman (31 October)

**Reused actual owners:** `RecursiveRadixHypervoxel` supplies reversible rank/depth suffix refinement; `HypervoxelAdicYoungFibonacciBridge` has typed chart/valuation/parent/braid relation; `TrialecticStageThirteenMarkedC3CubieExact` supplies cubie C3 and reflection; `BalancedTernaryAntipodalOrbitExact` and `BalancedTernaryAntipodal369OrbitHierarchyExact` supply 13 signed antipodal pairs plus one uniquely fixed centre; `JInvariantBishopTrigUnitPhaseExact`, the vendored Bishop library and Pickover PR #1260 supply the *actual* analytic sine and historical phase readout. No extra phase owner or 27-cube reinvention.

**Forward BIDI:** actual exact exponent `N=99^(9999!)` → rigorous complex/unit-circle evolution with full winding and accumulated error history → hypervoxel rank/depth chart `coarseAddress + relativeAddress` with exact `fineAddressIsJoin` → sign-retaining antipodal/cubie/fibre projection with centre as one state → effective certified Bishop terminal `Im phase` interval → a true negative/positive terminal sign. This is a **required proof pipeline**, not an assertion that p-adic residue fixes the real sine sign.

**Backward BIDI:** demanded terminal orientation + certified `0∉[L,U]` → required numerical precision, phase winding, acceptable interval width → minimal query-sufficient hypervoxel/chart and adaptive refinement of its suffix. If sign is unresolved, refine without conflating unresolved with actual zero; neither ternary 27 nor 13 antipodal classes alone supplies the continuous phase margin. Prove every chart restriction/overlap preserves the genuine Bishop imaginary coordinate and certified error.

**Direct RH analogy, nonidentification:** Pickover requires *one* certified nonzero real sine; RH requires *all* zeta zeros on the line, and twin primes require unbounded arithmetic pairs. The common structure is globally consistent signed spectral gluing and quantified error/zero-exclusion. A p-adic cubie orbit count or an analytic-j chart match is not a reduction from either problem to another.

**Additional acceptances**: PH01 exact factorial/exponent representation; PH02 actual Bishop phase, normalization, and exact history; PH03 join/coarsen suffix commutation; PH04 cube antipodal class+retained sign+fixed centre and admissible consumer gluing; PH05 certified complex matrix transport and truncation error with a real scalar norm; PH06 effective winding/angle reduction at huge N; PH07 formally checked interval enclosure `0∉[L,U]` for the true sine, producing its actual sign; PH08 independent interval/proof checker and complexity receipt. Reuse phase and geometry owners first; PH05–PH08 are not discharged by finite geometric BIDI. No ESD edits.


## Complete executable-facing formalism — Pickover 9999 steelman v3

### 0. Actual input and retained original phase history

`m=9999!`, `N=99^m` as a mathematical natural number, and `z=exp(iN)=cos N+i sin N` in the genuine Bishop complex analytic carrier. Original state `H` retains the complete exponentiation lineage, CRT/p-adic residue information when relevant, signed/winding phase, interval error and chosen exact hypervoxel refinement suffix. The terminal query is `Sign(Im z)`, not a finite trit count.

### 1. Exact producer and transport identities

`phase(0)=1`, `phase(a+b)=phase(a)*phase(b)`, `phase(a*b)=phase(a)^b` for integer input, after proving the corresponding Bishop exponential laws on the actual analytic scalar. Exponentiation by squaring and factorial recursion produce a compact *algorithmic description* of `N`; they do not make the huge-bit integer inexpensive to materialise.

Reuse `RecursiveRadixHypervoxel`: `fine=joinAddress coarse suffix`; exact coarsening/relative refinement witnesses. Use the actual `BalancedTernaryAntipodalOrbitExact` action and 13 signed paired orbits + unique fixed centre. The 9→18→27 z-face map is a distinct chart. A phase may cross a trit boundary on refinement; only the original complex phase plus residual controls whether sign survives transport.

### 2. Quantitative forward error certificate

For complex approximate transfer `T_j`, exact `U_j`, use telescoping:
`U_m...U_1 - T_m...T_1 = sum_{j=1}^m T_m...T_{j+1} (U_j-T_j) U_{j-1}...U_1`
(with empty products identity). Supply actual submultiplicative operator norms and propagated interval roundoff for all factors, including phase-reduction and exponentiation steps. The final complex interval/enclosure `Z` must contain the **actual Bishop** `exp(iN)`, with `Im Z⊂(0,infty)` or `Im Z⊂(-infty,0)`. Distinguish exact sine zero (provably impossible for positive integer N, via π transcendence) from an unresolved interval crossing zero.

### 3. Canonical hypervoxel/adic/cubie certificate

The supplied p-adic chart carries digit, valuation, parent and residue, while complex sine uses archimedean real phase. A formal bridge requires a **specified compatible map**; p-adic congruence by itself does not determine `N mod 2π`. The canonical cube quotient `27=1+13*2` is a **discrete observer**, not an assumption that there are 13 analytic phase classes. Signed history can be stored through that observer only if `FactorsThrough` is proved for the terminal imaginary-coordinate consumer or an explicit residual is added.

Admissible joining must have exact agreement of signed complex local sections, phase/winding consistency, cocycle and propagated certified error. Use existing `JInvariantAnalyticHyperformChartGluingExact`, `JInvariantSheafHyperformAdmissibleDescentExact` and Bishop sine rather than claiming similarity of numbers proves same-object identity.

### 4. BIDI directions

Forward `N + original exponentiation/winding history -> recursively refined hypervoxel/adic charts -> glued unit-complex transfer -> exact actual Bishop Im -> rigorous enclosure -> sign`.

Backward `required terminal signed separation -> acceptable enclosure radius and norm budget -> necessary phase reduction precision and historical winding -> refinement depth + jet order + residual suffix -> exact producer H`.

An effective irrationality estimate for π could bound proximity to `kπ`, but usefulness requires explicit constants and algorithmic cost. A proof that `sin N ≠0` without a computable enclosure does **not** provide the sign.

### 5. Final concrete lemmas

- P9-A: kernel-check shared original-history hypervoxel BIDI, antipodal sign+fixed-centre and true Bishop carrier imports.
- P9-B: prove actual Bishop complex exponential semigroup/power identities for the chosen construction.
- P9-C: certified recursive exponentiation with submultiplicative complex error propagation.
- P9-D: explicit phase winding/argument-reduction of the specific `N=99^(9999!)`.
- P9-E: rigorous explicit interval enclosure for `Im exp(iN)` that **excludes 0** (terminal sign theorem).
- P9-F: independent proof-producing/checkable finite certificate and error/complexity receipt.
- P9-G: backwards fibre sufficiency and minimal adequate jet/refinement depth for the *actual* sign query.
- P9-H: verify only after proof any proposed connection between the zeta-zero spectral chart and this finite sine phase; analogy is not a theorem.

The exact history and refinement modules are implemented as source; P9-D/E/F are actual mathematical/computational deliverables, not free interface fields.

## Implementation continuation: distinguish exact shared history from a true Bishop sign evaluator

`DASHI.Core.TwinPickoverHistoryHypervoxelTransportExact` retains the original state and `RecursiveRadixHypervoxel` addresses/suffix; its readout equations are definitional. The companion new arithmetic concrete BIDI module proves invertibility of a real Nat-period codec while transporting the full hypervoxel history. Do **not** substitute this number-theoretic codec for the archimedean sine sign: actual Bishop exponential identities, validated phase reduction and a zero-excluding interval are still necessary. For Pickover use the true Bishop historical phase owner from PR #1260 and transport a *certified phase interval* with a consumer-specific refiner. A finite trit label or 270-residue is insufficient by itself. No fabricated terminal sign.
