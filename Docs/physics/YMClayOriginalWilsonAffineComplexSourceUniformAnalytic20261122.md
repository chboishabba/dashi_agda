# YM P0 — actual original Wilson conditional affine source: uniform complex zero-free polydisc and sharp real mixed Hessian

Date: 2026-11-22. Source owners are pre-existing: \`YMClayOriginalWilsonAffineMarkedPartitionExact\` (the actual positive original full Wilson/Haar finite two-source source), \`YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact\` (full 1/F/G/FG F19 and 896 spectator identity), \`YMClayOriginalWilsonPhysicalF19PartitionExact\` (actual positive full effective density), and [\`YMClayOriginalF19CMP119MarkedActionHessianTower20261122.md\`](YMClayOriginalF19CMP119MarkedActionHessianTower20261122.md) (signed finite RG Hessian telescope). This is a NEW elementary quantitative **source-analytic** bound that works for the actual *global affine* Wilson marked conditional law. It is NOT a construction of selected renormalized CMP116 small-field analytic J, any KP polymer activity, or W3 rooted-shell physical decay.

## All-cutoff original source statement: zero-free finite conditional two-J partition

Take the **same real positive original finite SU(N) Wilson Gibbs density** at any positive Wilson coupling, on any finite 4D periodic physical cutoff/volume. Let F,G be bounded **real** gauge-invariant original closed Wilson word/plaquette trace observables with |F|,|G|<=1 (normalized real trace; a raw deficit 1-t in [0,2] must first be divided by 2 or use a smaller source radius). Select ANY positive conditional Haar kernel of that original law, including fixed R445/F19 64 coarse noncommutative holonomies with all interacting 896 fine spectators integrated, or any subsequent exact positive coarse-fibre step. Assume the existing strict positive full density and real compact-Haar integration premises giving K0(W)>0 on the retained coarse field W (or K0>0 almost everywhere).

The ALREADY-existing four F19 coefficient functions are

    K0(W) = integral_fibre w
    KF(W) = integral_fibre w F
    KG(W) = integral_fibre w G
    KFG(W) = integral_fibre w F G

and, with the actual two unique GLOBAL original Wilson insertion labels,

    K_W(s,t)=K0+s*KF+t*KG+s*t*KFG
            =K0 * E_original[(1+sF)(1+tG) | W].

Extend the finite polynomial ONLY in the TWO source scalars to complex s,t; this does NOT complexify the SU(N) link carrier, change original Haar, or replace the real Gibbs action. From positivity and |F|,|G|<=1,

    |KF|<=K0, |KG|<=K0, |KFG|<=K0.

Therefore for ALL complex |s|,|t|<=r=9/100, at EVERY original cutoff and retained W,

    |K_W(s,t)/K0 - 1| <= 2r+r² = 1881/10000,
    |K_W(s,t)| >= (1-2r-r²)K0 = (8119/10000)K0 > 0.

Thus the existing true globally marked original F19/Wilson finite conditional source has a cutoff-, volume-, beta-, and fibre-independent **zero-free complex polydisc**; log[K_W(s,t)/K0] has its canonical analytic branch there by the power series log(1+z) with |z|<1, and ordinary mixed differentiation is allowed on each finite original Wilson conditional integration. This is stricter than an assumed merely formal source jet: the original finite source itself is a concrete entire polynomial, and its normalized log is holomorphic on this common polydisc. It remains a TWO global-source analytic neighbourhood, **not** the analyticity and spatial localization of a selected Bałaban/CMP116 infinite-dimensional bond J or all renormalized effective actions.

On the REAL square |s|,|t|<=r, the stronger pointwise (1-r)^2<= (1+sF)(1+tG) <= (1+r)^2 gives

    (8281/10000)K0 <= K_W(s,t) <= (11881/10000)K0.

The mixed LOG derivative is exactly

    d_s d_t log K_W(s,t)
       = (K0*KFG-KF*KG) / K_W(s,t)^2.

The intrinsic \`-log K\` marked action Hessian has the opposite sign, as already correctly recorded by the 22-Nov F19/CMP119 marked-action Hessian tower.

## NEW quantitative universal derivative envelope, actually original-source compatible

Let \`nu_{s,t,W}\` be the original **positive real-source** conditional probability with tilted density (1+sF)(1+tG). Define bounded scores

    f_s = F/(1+s F),       g_t = G/(1+t G).

Standard positive-measure differentiation (valid here for the concrete finite source) gives

    d_s d_t log K_W = Cov_{nu_{s,t,W}}(f_s,g_t).

For F,G in [-1,1], \`f_s\` and \`g_t\` are monotone transformations with ranges

    f_s in [-1/(1-s), 1/(1+s)],
    g_t in [-1/(1-t), 1/(1+t)].

Hence using Cauchy-Schwarz and Popoviciu's range variance bound (equivalently the elementary two-point covariance oscillation inequality),

    |d_s d_t log K_W(s,t)|
        <= 1 / [(1-s²)(1-t²)]
        <= 1 / (1-r²)^2
        = 100000000/98386561
        ~= 1.01639858.

This universal REAL-source bound is **sharp over all positive conditional probability laws**, realized by a two-atom law with F=G=+1 or F=G=-1 and original probabilities chosen proportional to (1-s)(1-t) and (1+s)(1+t), respectively, so both tilted atoms have probability 1/2. Sharpness is for the class of all bounded laws, not a claim that an original Wilson Gibbs fibre attains it.

For complex sources, the algebraic numerator and K denominator give the less sharp but universal zero-free bound

    |d_s d_t log K_W(s,t)|
       <= 2 / (1-2r-r²)^2
       = 200000000/65918161
       ~= 3.034.

For zero source, original conditional connected covariance is |Cov(F,G | W)|<=1. **None of these bounds decreases with physical separation**: they control analytic source differentiation and the magnitude of a local marked response, not the W3 **summation over distant connecting clusters**.

## Exact local SymPy 1.14.0 reference and negative controls

Executed locally in this turn: \`/mnt/data/check_ym_original_affine_analytic_polydisc_20261122.py\`. It checks 256 strictly positive two-global-mark endpoint laws (each with four atom weights from {1,2,3,4}), 1024 exact rational real source evaluations, the exact mixed-log Hessian determinant, the real density bounds and strict 8119/10000 complex zero-free floor; it verifies the sharp two-atom equality, rational real/complex constants, and a **nondecaying** global fair-sign countermodel whose Z(s,t)=1+st and connected covariance is 1 at arbitrarily selected spatial separation. This is a mathematical countermodel to the implication "uniform source holomorphy -> D1 physical clustering", NOT a counterexample to Yang-Mills. The original complex no-zero statement is an analytic theorem from positive Wilson/Haar and bounded marks, independently of this finite discrete regression; no continuous full-SU2 Haar numerical integration is claimed in this test.

No Agda 2.9 kernel check, no GitHub CI, no new postulate-free real/complex formal library and no Clay mass gap claim. This note uses established real/complex elementary inequalities conditional on the ORIGINAL source's explicit one-link Haar positivity. Other source marks outside [-1,1] require corresponding adjusted radii.

## Revised priority and exact limits

**PAYMENT NOW:** literal finite original globally affine 2-J normalizing function, already source-owned; NEW uniform source complex zero-free radius and exact real mixed-derivative bound, at each original cutoff and every strictly positive original Haar fibre; original F19 KFG/c_W remains intact. This is not an additional independent Wilson Gibbs source or generic KP gas.

**STILL UNPAID:** an analytic identification of this actual ORIGINAL two-source finite Wilson J with the SOURCE-SELECTED CMP116 bond-valued/renormalized J and its local marked energy; physical original CMP119/122 selected E/R/B/V source, blocked good/large-field region, renormalized (NOT microscopic) globally marked KP cluster-log with original Wilson parity and full spectator data; **ABSOLUTE** connected physical rooted-shell W3 charge with cutoff/volume-independent rate; original E1 nontrivial R4 continuum RP/OS and dense SAME H_OS D2 spectrum; N1 continuum noncollapse and group-dependent G1.

The finite original marked RG Hessian **signed** telescope remains valid but cannot become an absolute W3 shell sum by cancellation; the existing 22-Nov original real D1 conditional compiler is ready only after actual full-source envelope. Preserve original Wilson, Bałaban CMP116/119/122, Kotecky-Preiss / Fernandez-Procacci and Osterwalder-Schroder/Menotti-Pelissetto attribution. P0 YM first.
