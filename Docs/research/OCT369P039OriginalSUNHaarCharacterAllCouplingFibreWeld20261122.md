# OCT369 × YM P0.39 — original SU(N) Haar/character quantum-fibre source weld

**Date:** 2026-11-22. **Ownership:** OCT369 #1534 cross-consumer, original source on YM #1444/#1536; KK/E6 #1241/#1106. These are distinct branches and theorem owners. **Status:** exact *finite two-layer open-interval* SU(N) identity derived from standard Haar/Schur theory; local SymPy/NumPy/mpmath test (85 checks) with continuous SU(2) Weyl moments and independent finite Q8 **geometry-only** control. No GitHub CI or Agda kernel. No physical Yang–Mills gap, E6 vacuum, anomalous gravity or new theorem of Haar integration claimed.

## 1. Live YM audit — source owners already general, latest physical boundary

The latest heads consulted were #1444 `9a0b7733e102a04f372a815c88cbe8862f7a799e` and #1536, which includes new `b6f836087d644ed7fce97da8ac7b5bb0d15dea93` (2026-11-22). The following original native modules **already exist** and MUST be consumed rather than reconstructed:

- `YMClaySUNVariablePeriodicGibbsGaugeExact`: arbitrary positive integer N, all periodic finite 4D lattice sizes and all six physical plaquette orientations, original gauge cancellation, Wilson action; finite fields and measure/continuum limitations explicit.
- `YMClaySUNMatrixWilsonTraceGaugeExact`: actual SU(N) matrix Wilson trace and conjugacy invariance, conditional on inherited matrix-trace axioms.
- `YMClaySUNWeightedHaarPairFibreDisintegrationExact` (F17), `YMClaySUNWeightedDisjointPairFibreReparamExact` and `YMClayOriginalWilsonPhysicalF19PartitionExact`: original weighted noncommutative Haar reparameterization for nonfactorizing weights, full 1024 fine links/64 selected coarse pairs/896 spectators and original F19 density.
- `YMClayOriginalWilsonTwoPlaquetteMarkedSourceExact`, `YMClayOriginalWilsonNativeOSPullbackExact`, `YangMillsDirectSourceOSSameHGapExact` and #1536 original time-reflection/CMP116/119/122/W3 owners: same-physical-source marked Hessian and OS/gap *conditional compiler*, with uninhabited analytic/source/continuum hypotheses. No new arbitrary “positive gap” assumption gets inserted by this consumer.
- **Newest native SU(N) source result:** `scripts/check_ym_original_wilson_sharp_dobrushin_link_clustering_20261122.py` on #1536: exact L>=3 periodic 4D source incidence, six plaquettes per link, 18 distinct other shared-plaquette links per link, small bare-coupling bound `q <= 18*tanh(beta) < 1` (e.g. beta<=1/36). It invokes *classical Dobrushin comparison* rather than proving a new estimate; the sharp TV/covariance normalization requires theorem-source checking. It fails the physical continuum `beta(a)->infinity` and does NOT pay W3/CMP119 rooted-shell physical decay, even if its finite-volume small-beta application is correct. The older #1444 current F19 original affine marks/absolute martingale scale L2 and complex zero-free two-source radius are different, real achievements but do not provide absolute spatial W3 shell decay.

Prior theoretical authors: Wilson; Haar, Peter--Weyl/Schur compact-group characters; Kaluza/Klein, Yang/Mills, Balaban and Osterwalder/Schrader. Do not relabel these as DASHI inventions. The new contribution here is *consuming* them for a precisely delimited fifth-direction source and an SU(2) exceptional-case regression.

## 2. The actual SAME five-dimensional interval-slab source

Let `G=SU(N)` for N>=2 and a single oriented square with four bottom links `U_0..U_3`, four upper links `T_0..T_3`, and four fifth-direction vertical links `W_0..W_3`. Physical mixed plaquettes are

`P_{e5}=U_e W_{e+1} T_e^{-1} W_e^{-1}` (vertices modulo 4).

Choose **exact same original normalized Wilson trace** `f_t(g)=exp[(t/N) ReTr(g)]`; the usual `exp[-t(1-ReTr(g)/N)]` differs only by a field-independent factor `exp(-t)` for that plaquette. At fixed bottom `U`, define

`K(U)=int_{G^8} dH(T_0)..dH(T_3) dH(W_0)..dH(W_3) f_{beta1}(T_0 T_1 T_2 T_3) * prod_e f_eta(P_{e5})`.

**One Haar change of variables, no new measure:** set `V_e=W_e T_e W_{e+1}^{-1}`. Haar bi-invariance, Fubini and the top trace's conjugacy invariance imply

`K(U)=int_{G^4} prod_e dH(V_e) f_{beta1}(V_0 V_1 V_2 V_3) prod_e f_eta(U_e V_e^{-1})`.

With *bottom gauge* fixing three links to the identity, `K(U)` depends only on the lower plaquette conjugacy class `P_0=U_0 U_1 U_2 U_3`. Because `f_t(g)=f_t(g^{-1})` is central, this is a **five-fold central convolution** on G. For irrep R, `dim R=d_R`, character `chi_R` and exact Haar coefficient

`c_R(t)=int_G dH(g) f_t(g) overline(chi_R(g))`,

Peter--Weyl/Schur convolution gives the all-coupling *finite open slab* identity

`K(P_0)=sum_R [c_R(eta)^4 c_R(beta1) / d_R^4] chi_R(P_0)`.

This does **not** assume K is constant or bare Wilson. It contains infinitely many irreps and hence generally induces higher-representation class functions and multi-trace/nonlinear contributions to `-log K`. The all-coupling representation expansion is an established harmonic-analysis theorem, not a new Clay result. For real nonnegative beta/eta, the original finite Haar integral is strictly positive; no complex zero-free analytic radius for this *new* K is inferred from the old original 4D two-mark Wilson radius.

## 3. Group dependence: SU(3) reproduces P0.38, SU(2) is exceptional

For `N>=3`, the fundamental and antifundamental irreps differ: Schur/center selection gives `c_F(t)=t/(2N)+O(t²)` and its conjugate, and all other nontrivial irreps start at higher powers. For the joint term of degree `beta1*eta^4`, this yields

`delta log K(P0) = [beta1 eta^4/(16 N^9)] ReTr(P0) + (constant and higher multivariate degrees)`,

`delta beta0 = beta1 eta^4/(16 N^8)` for the original Wilson coefficient `(beta0/N) ReTr(P0)`.

At **N=3** this reproduces P0.38 *exactly*: `delta beta0=beta1 eta^4/104976` and `delta log K=beta1 eta^4 ReTr(P0)/314928`.

For **SU(2)**, the fundamental is pseudoreal, i.e. `F≅Fbar`, and the fundamental trace is real. The factor `1/2` in each single-character leading coefficient must **not** be used. Instead `c_F(t)=t/2+O(t³)` for the selected Wilson normalization `t/N=t/2`, giving

`delta log K(P0) = [beta1 eta^4 / 512] Tr(P0) + ...`,

`delta beta0 = beta1 eta^4 / 256`.

Naively inserting N=2 into the N>=3 formula gives a **16-times smaller** result. This is a real construction/representation error; the correct distinction is SU(2) self-conjugacy versus SU(N>=3) two distinct conjugate fundamental characters, not a different Yang--Mills force law.

For SU(2), the original continuous **Weyl** integral gives `c_n(t)=I_n(t)-I_{n+2}(t)` (irreducible spin n/2, dimension n+1, modified Bessel I). Thus the entire finite-slab fibre kernel is explicitly

`K_SU2(P0)=sum_{n=0}^infty [(I_n(eta)-I_{n+2}(eta))^4 * (I_n(beta1)-I_{n+2}(beta1)) / (n+1)^4] chi_n(P0)`.

This is exact for *all finite real* selected beta and eta under the finite interval source. It is not a 4D YM continuum partition function. Its character coefficients were independently checked against SU2 Haar/Catalan polynomial moments and high-precision 1D Weyl integrals, NOT replaced by a quaternion finite subgroup.

## 4. Independent geometry, spectral and YM acceptance controls

Local `scripts/check_oct369_p039_sun_character_fibre_weld.py` checks 85 conditions using SymPy 1.14, NumPy 2.3.5 and mpmath 1.3.0. These include general symbolic N>=3 coefficients; N=2 pseudoreality negative control; genuine continuous SU2 Haar moments, orthogonality and Bessel character coefficients; high-precision Weyl quadrature; and **separate** exact Q8 finite-group lattice slab summation versus its own five-irrep Fourier formula on five bottom holonomies. **Q8 is geometry only**, not substituted for actual SU(N) Haar. The SU2 illustrative full K at beta1=1.1, eta=1.35 is `K(I)=2.820430128550953988211`, `K(-I)=2.763178206038639715221`, `K(trace=0)=2.791770137714761718063`; the all-order source is nonconstant and positive at those representative holonomies.

**Critical full 4D×I geometry negative control:** each vertical fifth-axis link is incident to **eight** mixed mu-5 plaquettes on an L>=3 periodic four-dimensional base, not merely the one-square interval slice. Those plaquettes share vertical links, so the full 4D source **does not factor into independent copies** of K(P). The compact circle has extra y-links and gauge-invariant Wilson holonomy; a fifth-direction gauge slice cannot remove it globally. This is the correct next physical **multi-plaquette K_n** input to original F19 weighted Haar, with all source spectators and counterterms. The Q8 finite-group result is not a justification of that coupling or of the physical continuum.

**Yukawa/scalar/fermion scope:** #1241's selected 5D color sector includes eight fundamental Dirac flavors and other matter, plus an independent U1_B and E6/trinification Higgs/VEV sector. Those determinants, decoupling thresholds, physical boundary/orbifold, gauge quotients, scalar A5/radion and actual photon mixing remain separate conditions before any pure 4D compact simple SU(N) endpoint. General N formula is an abstract native SU(N) source extension, not an arbitrary-N E6 model.

**OS and Clay nonpromotion:** P0.39 proves neither a new full 4D Gibbs expectation nor a uniform bound on `log K_n` or two-source derivatives in physical RG scale. Even native original strong-coupling `18 tanh beta<1` cannot be carried to `beta(a)->infinity` or to the altered K-weighted effective action without a separate source bound. Preserve original physical time reflection/R445, complex OS Gram on identical tests, same-H reconstruction and a positive **continuum infinite-volume** gap as actual separate proof work. KK Fourier n/R, Higgs masses and a finite cutoff gap are not automatically this nonperturbative gap.

## 5. Next big-bite P0.40 — one source, one full geometry

1. **Same original multi-plaquette source:** instantiate the full periodic 4D×(S1 or interval) 5D SU(N) Wilson/Haar with N>=2, physical bottom torus `n`, vertical adjoint scalar and holonomy, all 8 mixed plaquette incidences, normalized action/measure and physically correct 5D matter determinant. Avoid a fictional factorized K(P) from isolated plaquettes.
2. **Actual pushforward:** define positive `K_n(U_bottom)` by Haar integration of the complete top/vertical/matter sector. Keep every 4D bottom link, every spectator and the source counterterm; compare to original source `YMClayOriginalWilsonPhysicalF19PartitionExact` / `YMClaySUNWeightedHaarPairFibreDisintegrationExact` under exact original gauge/measure coordinates. No generic fresh `SUN` interface if existing owners suffice.
3. **Same marked response:** establish identity for *original two marked Wilson plaquettes* and actual normalized expectation: `E_push(F)-E_4(F)=Cov_4(F,K_n)/E_4 K_n`. Then control the *full* derivatives of `log K_n` and induced physical rooted-shell activities, not just its leading local fundamental character.
4. **Physical source and spectral weld:** only after cutoff/volume-uniform CMP116/119/122 bounds and original reflection-positive source transport, construct same physical OS Hilbert/semigroup and obtain an independent positive continuum mass gap. Compare metric/KK and EM branch by same action and stress only after this quantum source is physically identified.
5. **Prioritization:** consume recent #1536 SU(N) 18-link Dobrushin strong-coupling source as a *negative/high-temperature control* for the new K, not an asserted UV compiler. Compare #1444 original complex zero-free/marked F19 and absolute martingale L2 bounds without claiming they are the unpaid W3 physical distance estimate.

**Attribution:** Group character convolution and Weyl integration are classical mathematics; this report is a new test/adapter of pre-existing scientific and DASHI source owners, not an original group theorem or proof of Clay Yang--Mills.


### Live #1536 original SU(N) continuation after initial P0.39 source audit (2026-11-22 10:30Z)
**Not missing or reinvented:** #1536 then added `scripts/check_ym_original_sun_affine_marked_dobrushin_20261122.py`, original source audit `Docs/physics/YMClayOriginalSUNWilsonAffineMarkedStrongCouplingW1Spatial20261122.md`, commits `efb62f1ab5ca35d6e91866e2352b19bd6e1352d8` and `3c87cdd30937067d0f71173c3f4c2f3791bbab59`. It preserves exact original global two-mark affine positive density `(1+sF)(1+tG)` and applies the imported classical Dobrushin-Föllmer influence theorem to the SAME continuous SU(N) Wilson finite-volume action, not an independent source gas. With **disjoint original marked four-link plaquettes**, real `|s|,|t|<=9/100` and `0<=beta<=1/72`, each original link's ordinary graph degree is 18 with at most 3 same-mark neighbours, so the stipulated row-sum bound `q<=18*tanh(beta)+3r<=13/25`. The corresponding real mixed source `|partial_s partial_t log Z| <= [40000000000/295159683]*(13/25)^d` is a **strong-coupling W1 spatial estimate**, not just zero-source covariance; the precise theorem's probability/TV/prefactor conditions remain external and its proof is not a new Dobrushin result. It is not the original physical renormalized CMP119/122/CMP116 **W3 absolute rooted-shell** or a cutoff-uniform continuum mass-gap theorem. The latest #1536 `b1ab2a3a75912b4db5e3217ae72b024d3cd5e6d6` additionally records C3/time-mirror automorphism of the original 1024-link/1536-plaquette **influence support graph**; that neither constructs OS reflection positivity nor identifies spatial C3 with the internal gauge group or zero-aware cube.
**P0.39 implication:** any induced `K_n(U)` must have its OWN conditional/local-score influence matrix and mixed Hessian on the SAME original two marks; the foregoing W1 bound does not transfer merely because the bare 4D source satisfies it. P0.39's original interval SU(N) character formula and SU2 exception remain unchanged.
