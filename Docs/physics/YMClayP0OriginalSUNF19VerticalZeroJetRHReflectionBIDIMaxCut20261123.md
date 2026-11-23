# YM P0 — original SU(N) F19 signed zero first jet × RH critical-line reflection × existing same-H owners

23 November 2026. Geometric-forward/BIDI source test, local SymPy 1.14. Actual finite SU(N) Wilson 4D action and source geometry, not a continuum mass gap or a proof of RH. No Agda/Lean/CI.

## Reuse and source precedence

Checked current master (one unrelated NS roadmap change since PR base) and open YM #1536, original CMP119/122 #1444, time-reflection #1535, RH #1533 (new seven-bit Cech/Monster signed-C2 modules), indexed TOE H05 #1291 and R559 #1281. Owners already exist: SUNMatrixCarrier, YMClaySUNMatrixWilsonTraceGaugeExact, YMClaySUNVariablePeriodicGibbsGaugeExact, YMClayNative1024WeightedWilsonReindexExact, YMClaySUNWeightedDisjointPairFibreReparamExact, YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact, YMClayOriginalWilsonPhysicalF19PartitionExact, BalabanLiteralTwoWilsonCMP116ConnectingTailExact, and YMClayY369OriginalSingerWilsonFourMarkSourceWeldExact. No replacement SU(N), Haar, OS, FactorThrough or F19 construction.

## ORIGINAL SU(N) source: identical coarse holonomies, opposite fine Wilson derivatives

On original side-four periodic 4D lattice (256 sites, 1024 positive links, 1536 original plaquettes), select original y-z fine closed marks F at x=(0,0,0,0), G at x=(0,0,0,2). Take original native pair U=(x,2), V=(x+e_2,2), W=UV, one of 64 distinct R445 pairs, with all 896 spectator coordinates retained. Set disjoint fixed G positive link to Q=diag(e^(i*pi/3),e^(-i*pi/3),I_(N-2)); all other fine links identity. Original U,V,G source edges belong to THREE DISJOINT six-plaquette stars (full 1536 enumeration PASS).

For any N>=2, let omega=e^(2*pi*i/N), lambda=1 for odd N and e^(pi*i/N) for even N, and U0=lambda diag(1,omega,...,omega^(N-1)). det U0=1, Tr U0=0. Choose j,k with Im(U0_jj) != Im(U0_kk) and A=i(E_jj-E_kk) in su(N). Actual smooth source curves:

    U_plus(r)=U0 exp(r A),   V_plus(r)=exp(-r A);
    U_minus(r)=U0 exp(-r A), V_minus(r)=exp(r A).

The EXACT SAME original W=U0 for both arcs for ALL r. All other 63 native coarse W also unchanged. The original GAUGE-INVARIANT fine closed Wilson plaquette F(r)=ReTr P_F(r)/N has

    F_plus(0)=F_minus(0)=0,
    F_plus'(0)=-F_minus'(0) != 0.

Exact locally computed values F_plus'(0): SU2=-1; SU3=sqrt(3)/6; SU4=-sqrt(2)/4; SU5=sqrt(10+2 sqrt(5))/20. G(r)=(N-1)/N is constant. Traces of CLOSED plaquettes (and their derivatives) are invariant under gauge conjugation even when gauge transformations themselves vary with r. Therefore those signed first jets are physically distinguishable by gauge-invariant *observable derivatives*. The two arcs STILL share a single field at r=0, so this does NOT construct two independent zero-valued configurations, two OS Hilbert vectors, or physical vacuum degeneracy.

A true original source-specific FactorsThrough obstruction is now CONSTRUCTED: F does not descend pointwise to the 64 coarse W, because those W are fixed but F changes. The observer must retain the fine link fibre or its gauge-invariant first jet if its consumer asks for F or direction of crossing. Binary amplitude zero/nonzero alone does not encode a nonzero signed derivative, whereas support+orientation/velocity can. Mapping the abstract 10-state doubled-zero label to this tangent is a SOURCE-SELECTED first-jet assignment, not an intrinsic second sign for zero amplitude and not a global natural equivalence of the two carriers.

## Full original Wilson 1536-plaquette Gibbs score and four marked jets

The original density is w_beta=exp(-beta sum_p (1-ReTr P_p/N)). The selected field base has exactly sum_p ReTr P_p/N=1536-6-6/N, so w_beta(0)=exp(-beta (6+6/N))>0. The U-star's six plaquettes each contribute F_plus'(0); V-star has zero normalized trace derivative at r=0; G-star fixed. Therefore

    (d/dr) log w_beta |0 = 6 beta F_plus'(0).

For the ONE SAME original physical Gibbs weight, original 1,F,G,FG affine coefficient-jet derivatives divided by base w_beta are respectively

    (6 beta F',  F', 6 beta G0 F',  G0 F'), G0=(N-1)/N.

All reverse sign for the opposite tangent. This preserves the original nonlinear first-score term and the original four-column source distinction, not a separately selected gauge/free Hamiltonian. This is a FIELD-SPACE pointwise differential; the full finite product-Haar conditional integral, interacting continuum W3, actual CMP119 residuals and true OS semigroup are separate. The full original 1024-bond source was represented (mostly identity links), not sampled under Haar. No finite positive gap inferred from a local derivative.

## What RH half-line crossing can actually mean

Existing actual completed Riemann xi source has entire xi(s), functional symmetry xi(s)=xi(1-s) and conjugation xi(conj s)=conj xi(s). For an original fixed ordinate gamma and horizontal x, f_gamma(x)=xi(1/2+x+i gamma) obeys

    f_gamma(-x)=conj(f_gamma(x)).

Therefore Re f is even, Im f odd, and f_gamma'(0) pure imaginary. IF rho=1/2+i gamma is an ACTUAL SIMPLE xi zero, horizontal +/-x has opposite signed leading imaginary values. This is a real first-jet crossing of the critical LINE, not a motion in physical time. At multiple zeros the first nonzero Taylor order matters. Nothing in these source symmetries implies that all nontrivial zeta zeros are on that line.

More relevant to current RH #1533 signed reflected-pole owner: for a same-ordinate reflected OFF-critical pair at horizontal displacements +/-a, its selected contribution to completed xi'/xi is

    D_a(w)=1/(w-a)+1/(w+a)=2w/(w^2-a^2).

For a!=0, this PAIR contribution has observed cancellation D_a(0)=0 and nonzero odd first derivative D_a'(0)=-2/a^2. The original two xi zeros are the poles at w=+/-a, not the observed midpoint zero. At a=0 the pair tends to 2/w, a pole, not a zero. Other zeros and holomorphic source terms mean the full xi'/xi need not vanish at this midpoint. This exactly captures a lost-source warning: a binary observed-zero bit loses the two poles, multiplicities and signed derivative. RH #1533 current RHQuartic128Monster3BSSPSignedC2IntertwinerExact explicitly says the seven-bit nonzero signed encoding does not contain the ternary neutral; signedBit sends zeroMultiplicity to false, so that map is NOT a 3-way inverse.

An independent exact entire completed-symmetry COUNTERMODEL closes the false inference. Let z=s-1/2, a=1/3 and gamma=2:

    P(z)=(z^2+gamma^2) (((z-i gamma)^2-a^2) ((z+i gamma)^2-a^2)).

P is even with real coefficients and satisfies both xi-type symmetries, has SIMPLE critical zeros z=+/-i gamma and FOUR off-critical zeros +/-a +/-i gamma. At the critical zero its signed horizontal derivative is i*580/81 (SymPy PASS). Thus a genuine nonzero critical signed first jet and simultaneous off-critical zeros are compatible with those symmetries. P is a symmetry counterexample, not actual xi or an Euler-product replacement. Original RH post-sixth signed target H_W+S_W<4d_W(rho)+I_W, same-ordinate D, actual Gamma/mu/prime and Dirichlet character sheets remain OPEN.

## Existing positive-Hamiltonian theorem owners and the exact missing physical payment

Audited master and advanced YM #1536: BalabanUniformPhysicalMassGapAnalyticInhabitation, BalabanClayDenseCoreSpectralGapExact, BalabanOSMassGapClosure, YangMillsDirectSourceOSSameHGapExact, YangMillsWilsonSameHMassGapRound552Exact, YMClayR387PhysicalSpectrumExact, YangMillsStressOSSourceFirstSemigroupCoreToClosureExact and original finite transfer YMSprint107 and typed physical transfer conversion already exist. Furthermore R494, R556, R573 and source-first CMP116 WEXT compilers already carry original full connected Wilson covariance, T5 measure convergence and same-source mixed-log algebra. In advanced #1536 the original WEXT time-distance non-vacuity proof rejects universal quantification over ANY metric: use ONE source-selected physical Wilson distance.

But the uninhabited source fields are explicit in the real code. R494 literal absolute connecting-weight SUM/physical rooted shell is conditional; R556 same selected T5 covariance WEXT shell and bounded tests/time and order closure require source inhabitants; R551 original continuum Wilson same-family and physical time-support meaning are conditional; R552 requires source spectral transfer to the SAME reconstructed H; current all-size SU(N) CMP119/122 constrained T, beta(a), E/R/B/V and Faddeev–Popov/source residuals not physically identified. A finite positive transfer gap 1-lambda_2>0 is not equivalent to a cutoff-independent physical -log lambda_2/a>=m>0, and neither is implied by opposite first jets. These remain P0.T, P0.W3 and P0.OS, with E1/D1/D2/N1/G1 open.

## Execution and trust

Full executable local source in sandbox: /mnt/data/ym_p0/check_ym_sun_f19_zerojet_rhline_20261123.py, Python/SymPy exact PASS (all 1536 source plaquettes, N2/3/4/5, three disjoint six-face stars, 64 W, source Gibbs/1/F/G/FG jets, true SU(N) gauge conjugation, RH xi-type parity and off-line countermodel, reflected pair poles, transfer scaling). Committed compact source-equivalent script: scripts/check_ym_p0_sun_f19_vertical_zero_rh_jet_20261123.py. The compact copy was not separately locally executed byte-for-byte, so no such claim is made. No native Agda/Lean kernel, CI or proof of RH/Clay gap.

Attribution: Wilson, Haar, Faddeev–Popov, Bałaban CMP98/109/116/119/122, Osterwalder–Schrader, Riemann xi functional equation, original DASHI SU(N) and fine/coarse R445/F19, RH #1533 and TOE H05 #1291 signed-zero source owners.

## F. Stronger full continuous SU(N) F19 Haar result — positive conditional fine-Wilson variance

This is MORE than a selected field-space curve: it follows analytically for the ORIGINAL full finite continuous SU(N) product-Haar Wilson density, with no Z2 restriction or spectator deletion. It does NOT require a new Haar constructor: original YMClaySUNWeightedDisjointPairFibreReparamExact and YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact already supply the one-source 64-pair/896-spectator Haar disintegration.

For ANY selected complete 64-holonomy coarse field W, fix all F19 fine pair-fibre variables and 896 spectators EXCEPT the Haar variable V of the marked source pair U=W V^-1. The closed fine plaquette F includes U (one positive source edge) but does NOT include its next-bond partner V. Holding all other source variables fixed, its holonomy is a fixed left/right translate of V^-1, hence Haar-distributed in SU(N) under the reference product-Haar fibre. In particular, its normalized real-trace F has Haar mean zero and Haar variance

    v_N = 1/4 for N=2;
    v_N = 1/(2 N^2) for N>=3.

The standard facts follow from irreducible fundamental-character orthogonality: E_Haar |Tr U|^2=1, and E_Haar (Tr U)^2=0 for N>=3 (also from a nontrivial SU(N) centre phase z^2), while SU(2) has real fundamental trace and E(Tr U)^2=1. The local SymPy regression directly checks the SU(2) Weyl class integral with normalized density 2 sin²(theta)/pi: E cos(theta)=0 and E cos²(theta)=1/4. N>=3 imports the standard Schur/Peter-Weyl character identity; no claimed independent SymPy integration of arbitrary SU(N).

When V varies with U=W V^-1, ONLY the two disjoint native six-plaquette stars incident to U and V can change. All 12 plaquette normalized deficits d_p=1-ReTr(P_p)/N lie between 0 and 2. At physical beta>=0, the conditional V-dependent original Wilson Gibbs factor exp(-beta sum_of_12 d_p) is bounded between exp(-24 beta) and 1. Upon normalization over V against Haar, the probability density is therefore >=exp(-24 beta) pointwise. For ANY real constant c and ANY frozen other original F19 variables,

    E_Wilson[(F-c)^2 | W, others]
      >= exp(-24 beta) E_Haar[(F-c)^2].

Take infimum over c to get conditional variance at least exp(-24 beta) v_N. The law of total conditional variance, averaging all 63 other native V fibres and all 896 spectators under the ACTUAL one original interacting Wilson density, yields for every W:

    Var_Wilson(F | W)
       >= exp(-24 beta) * {1/4, N=2; 1/(2N^2), N>=3} > 0.

This is a FINITE-VOLUME, FULL CONTINUOUS SU(N) PRODUCT-HAAR, source-specific theorem, not a centre-slice toy: fine closed Wilson F is NOT measurable as a function of the 64 coarse W alone even almost surely. By Haar full support and strict Wilson positivity, both fine-F sign sectors have positive conditional probability for every W; the exact F=0 crossing itself is a measure-zero hypersurface in generic fibres. The retained sign is information about the fine observable and/or first jet, NOT proof of two independent spatial zeros, two Hamiltonian vacua or a separate physical zero-energy oscillator.

**Cutoff warning:** exp(-24 beta(a)) tends to zero along beta(a)->infinity; this inequality is not uniform in the weak-coupling continuum cutoff, is NOT a positive lower bound on an OS nonvacuum spectral gap, and does NOT bound the original distinct two-mark F,G covariance (which may cancel after integration). P0.T actual CMP119/122 localized density, true absolute CMP116/W3 source coupling and physical rate, original RP/OS same H remain open. We have paid the original *fine-to-coarse SufficientConsumer nonfactorability* at finite Wilson Haar, not the Clay mass-gap problem.

This new source certificate is added to the committed compact checker using the original twelve-plaquette incidence, SU2 exact Weyl integral and symbolic exp(-24 beta) bound. Independently extended local Python/SymPy checker has rerun and passed. Classical compact-group Schur orthogonality is an imported mathematical identity, not a new Agda kernel receipt or a claimed local SU(N) full manifold integration.
