## Strict P07 same-observer correction

The Lorentz+KK same-metric upgrade is no longer just a pairing of a selected (3,1) signature with an unrelated selected quantum clock. The revised SameMetric31ClockUpgrade carries an explicit mapping from the **original TSVF forward ket** into the original Lorentz arrow-source physical state, plus a proof that this forward ket maps to the same state selected by the physically reduced KK/4D metric. selectedObserverKetReallyIsMetricState projects this exact same-object witness. The core standalone Euclidean-4D YM/OS finite clock remains independent of 5D KK. The former arbitrary untyped ContinuumStoneOSClockMatch Set/witness has been **removed**: physically unprovided strongly continuous groups, Ward/Stone domains, same-source OS Hilbert and spectral estimates are honestly OPEN, not represented by a freely inhabited record token.

# 2017 TSVF complex gamma → original ABL → selected OS clock

**DASHI 3 November 2026 max-cut. SOURCE-WRITTEN ONLY. No Agda kernel or physical Yang–Mills/TSVF completion.**

## Primary source: amplitude versus probability

Yakir Aharonov, Eliahu Cohen and Tomer Landsberger, *The Two-Time Interpretation and Macroscopic Time-Reversibility*, Entropy 19(3):111 (2017), https://doi.org/10.3390/e19030111, Eqs. 22–25.

The manuscript considers N environment degrees, n disturbed, k=N−n surviving records, and a selected branch from pre/postselection. In Eq.23/24 gamma quantities are branch-state overlap amplitudes, whereas the printed Eq.25 uses unsquared products of gamma inside a probability ratio. Those two conventions are not automatically the same for complex amplitudes. The literal ratio of gammaR=i versus gammaW=1 is i, although both complex Born weights are exactly 1. The new source proves this phase counterexample. This is a necessary notation/phase check, **not** a claim that the original authors' physical setup is false.

For a factorized complex source, mathematical probabilities require the Born step:
\[
A_R=\prod_j\gamma_{R,j},\quad
A_W=(\prod_j\gamma_{W,j})\langle\epsilon_R|\epsilon_W\rangle^k,\quad
w_R=|A_R|^2,\quad w_W=|A_W|^2.
\]
With a strictly positive total, the normalized binary probabilities are wR/(wR+wW) and wW/(wR+wW), and odds wR/wW require a nonzero wrong weight. The actual paper's gamma definitions and environmental dynamical factorization need same-source physical identification, not blind substitution of norm-squared coefficients.

## Four new Golden source modules, all from original owners

1. [TSVF2017ComplexEnvironmentRobustnessExact.agda](../../DASHI/Quantum/TSVF2017ComplexEnvironmentRobustnessExact.agda) imports the original rational Cayley-Dickson complex algebra, exact gamma norm-product and rational square nonnegativity owners. It constructs an actual complex Hermitian two-coordinate overlap, arbitrary independent k-factor environmental overlap, arbitrary finite complex disturbance amplitudes and right/wrong Born weights. Theorems include complexPowerBornIsBornPower, environmentOverlapIsProductRate, wrongBornExact2017Factorization, rightWrongBornRatioCross, complexBornNonnegative, totalBornNonnegative and imaginaryGammaIsNotUnitComplex. A generic selected total must have literal strict positive rational weight.

2. [TSVF2017OriginalComplexABLSelectedExact.agda](../../DASHI/Quantum/TSVF2017OriginalComplexABLSelectedExact.agda) **instantiates the original** DASHI.Quantum.TSVF QuantumSurface, TSVFEnsemble, ProjectiveMeasurement, ABLContext and ablProbability on a rational-complex two-coordinate Hermitian carrier. Coordinate projectors are idempotent, mutually orthogonal and complete. The final bra conjugates the selected amplitude coefficients; original transition amplitudes reproduce the complex gamma/environment source. The selected right gamma product is nonzero (empty product = 1); the positive common ABL total is explicitly constructed. selectedOriginalABLNormalizes proves exact common-denominator normalization for the ORIGINAL Q.ablProbability, and selectedOriginalABLWrongIsFactorizedGammaOverlap proves its wrong-branch numerator factors into the complex gamma Born product and environment overlap. actualComplexSelectedBidiSource reuses the original two-admitted/one-excluded history owner and proves original Bidi amplitude commuting, without selecting physical worlds.

3. [TSVF2017QuantitativeRateExact.agda](../../DASHI/Quantum/TSVF2017QuantitativeRateExact.agda) proves for all k on the earlier concrete q=(9/25)^k source:
\[
25^k\ge 2^k 9^k,\qquad
\Gamma_W\le\Gamma_R\Longrightarrow
(2^k+1)\Gamma_W9^k\le \Gamma_R25^k+\Gamma_W9^k.
\]
For positive total this means P_wrong <= 1/(2^k+1), a genuine exponential finite-source guarantee. **The gamma Born-weight ordering is a physical hypothesis, not implied by many surviving records alone.** At k=2, gammaR=1, gammaW=100 yields wrong=8100 versus right=625. The complex gamma Born-product theorem relates complex amplitudes to nonnegative effective weights, but it does not itself prove the physical comparison assumption.

4. [TSVFOSSameSelectedClockIterateExact.agda](../../DASHI/Physics/Foundations/TSVFOSSameSelectedClockIterateExact.agda) imports the ORIGINAL OS reconstruction and R331 indexed transfer-coordinate theorem. The Hamiltonian in the bridge is definitionally OS.hamiltonian reconstruction, not a second chosen symbol. From an explicit physical observer/OS state identification, one-step clock intertwiner and readout preservation, the module derives observerOSClockAllFiniteTimes and observerOSAllFiniteReadouts for ALL n. A wrong OS step is refuted by a finite tick counterexample. A physically selected same-metric Lorentz (3,1)/spacelike KK upgrade is optional; standalone Clay YM does not require it. Actual real-time strongly continuous OS transfer, physical Hilbert unitary, same dense Stone domain and spectrum remain OPEN.

**Attribution:** original Aharonov/Bergmann/Lebowitz, Aharonov/Vaidman, Aharonov/Cohen/Landsberger; original DASHI bidirectionally-admissible histories, original TSVF, rational complex Cayley-Dickson, rational order, OS reconstruction, R331/R577 and stress/Ward/Stone owners. No competing abstract owners.

## Validation and exact frontier

An independently executed Python Fraction/Gaussian-rational calculation passed 7,250 arbitrary complex gamma + Hermitian/projector/ABL examples over 29 environment lengths, 51 selected original-ABL-style normalized cases, 100 exponent bounds, phase and bad-clock negative controls. The committed [reproducibility script](../../scripts/check_tsvf_2017_complex_abl_os_maxcut.py) contains the extended cases; it has not itself been run at the repository head. **No Agda compiler is present in the local runtime**; new source has not been typechecked, and transitive safe imports not accepted.

Remaining *physical P0* is the actual 2017 N-body pointer/environment with selected initial/final quantum states, disturbed gamma_j amplitudes, unitary dynamics, controlled correlations, correct source Eq.25 convention, positive Born normalizer and a proved physical gamma/overlap bound. Remaining *P1* is a physical selected Lorentz clock and a unitary onto same-state equivalence with a strongly continuous OS time-translation group plus Stone domain/generator uniqueness. Remaining *P2* is the independent Clay YM R443 physical continuous SU(N) Haar/CMP119, R445 continuum estimates, R320 differentiated-source decay, R333 positive continuum same-OS-H gap and H6 nontriviality. *P3* (5D KK, 2D/3D comparisons and positive-G stress) is separate.

The original 12-phase 186-lemma ledger remains numbered unchanged. SOURCE finite versus KERNEL versus PHYSICAL status must remain distinct; no macroscopic time travel, multiverse, physical Yang–Mills mass gap or unified theory is claimed.
