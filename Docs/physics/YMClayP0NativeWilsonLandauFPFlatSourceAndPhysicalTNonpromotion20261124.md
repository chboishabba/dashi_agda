# YM Clay P0 — original native Wilson Landau-FP exact source calculation; physical CMP119/122 T, W3, continuum OS remain OPEN
24 November 2026. Mathematical source result. Local SymPy 1.14.0: **101,448 / 101,448 exact assertion groups PASS**; byte-identical executable Git blob **1b3c24fe98801add1f4957cd21458aef774c8f4e**. No Agda/Lean compiler, GitHub CI, physical continuum mass-gap theorem or claimed Clay solution.

## P0 terminal predicate (do not replace with acceptance counts)

\`YangMillsClaySolved = true\` is permissible only after constructing an interacting nontrivial four-dimensional Euclidean Yang–Mills continuum for the selected compact simple gauge group, satisfying the required axioms including a common reconstructed OS Hamiltonian H, and proving a **strictly positive spectral gap on its entire non-vacuum sector**. Finite sources, locally passing calculations, standard representation theory, formal record inhabitation with physical fields supplied as assumptions, or a selected-observable decay rate do NOT imply this endpoint. E1/W3/D2/N1/G1 remain genuinely mathematical obligations.

Existing source owners have priority: original arbitrary-periodic SU(N) Wilson/Gibbs/gauge \`YMClaySUNVariablePeriodicGibbsGaugeExact\`; original L4 F19 disintegration and four global source columns \`YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact\`; original full 1536-face native source in \`check_ym_p0_original_wilson_marked_ordered_t_20261123.py\`; finite rooted-tree Haar quotient in \`YMClayP0OriginalWilsonRootedTreeHaarGaugeW3OSSourceCut20261124.md\`; tree-coordinate and conditional **different** background-slice owners \`BalabanClayGate4PeriodicTreeGaugeCoordinatesExact\` and \`BalabanClayGate4TreeBackgroundSliceTransitionExact\`; genuine CMP119/122 source E/R/B/V, Eq.(2.18)–(2.23)/Eq.(1.71) and CMP116/R573–R576 W3 owners; \`BalabanClayDenseCoreSpectralGapExact\`/\`YMPaper3RowCToDenseCoreGapAdapterExact\`. No generic replacement T, FP, W3 or OS carrier is introduced here.

## A. Genuine original lattice, standard Landau chart only

For the original 4D L-periodic SU(N) Wilson graph, oriented positive links E contain 4L^4 coordinates and six positive plaquettes per site; at L=4: 256 sites, 1,024 links and 1,536 plaquettes. An original positive bond e=(x,x+hat_mu) transforms exactly as \`U_e^g=g_x U_e g_(x+mu)^(-1)\`. The original action \`S=sum_(plaquettes)(1-ReTr P/N)\` and BOTH original global y-z plaquette deficit marks \`F,G\` are invariant.

The **standard Landau** gauge-fixing functional \`R(g;U)=sum_(original positive edges e=(x,y)) ReTr(g_x U_e g_y^(-1))/N\` is defined here solely to compute an explicit field-dependent FP/Gribov control. Its Hessian is *not* automatically the \`Q_B\`-dependent, axial/averaged, characteristic-function/delta-constrained gauge of Bałaban CMP119 Sect.2 and CMP122 Eq.(1.71). The latter must be identified from its ACTUAL source geometry, including physical gauge fixing, FP/ghost/Jacobian, E/R/B/V, and \`S_j\` summed **inside** \`T_k\`, before using any of the calculations here.

For site Lie-algebra fields \`omega_x in su(N)\`, \`g_x(t)=exp(t omega_x)\`, define the Hessian quadratic form

    Q_U(omega) = - d²/dt² R(g(t);U) |_(t=0)
       = -(1/N) sum_(e=(x,y)) ReTr(
           omega_x² U_e + U_e omega_y² - 2 omega_x U_e omega_y).

Use \`||omega||²=-(1/N)sum_x ReTr(omega_x²)\`, a positive Hilbert–Schmidt norm on anti-Hermitian traceless matrices. At the flat source U_e=I, the exactly evaluated Hessian is

    Q_I(omega) = sum_(original edges x~y) ||omega_x-omega_y||²
               = <omega, Delta_L omega>,
    (Delta_L omega)(x) = sum_mu (2omega_x-omega_(x+mu)-omega_(x-mu)).

The global constant gauge directions are the Lie-algebra zero modes; restrict to the mean-zero site-gauge tangent space, of real dimension \`D=(N²-1)(L^4-1)\`.

## B. All-mode exact L4 FP spectrum, determinant and local small-field bound

Fourier modes \`omega_k(x)=exp(2pi i k.x/L) X\` have scalar eigenvalues

    lambda_L(k) = 4 sum_(mu=1)^4 sin²(pi k_mu/L).

At L=4, the one-coordinate eigenvalue generating polynomial is \`1+2z+z²=(1+z)²\`; the whole four-dimensional generating polynomial is \`(1+z)^8\`. Thus the full EXACT scalar Laplacian spectrum is

| eigenvalue | multiplicity |
|---:|---:|
| 0 | 1 |
| 2 | 8 |
| 4 | 28 |
| 6 | 56 |
| 8 | 70 |
| 10 | 56 |
| 12 | 28 |
| 14 | 8 |
| 16 | 1 |

Therefore \`lambda_min(nonzero)=2\`, \`det'(Delta_4)=prod_(j=1)^8 (2j)^(C(8,j))\` and the scalar matrix-tree cofactor is \`det'(Delta_4)/256\`, the exact number of spanning trees of the underlying original connected multigraph. These objects are *not* unit: \`det'(Delta_4)\` has 223 decimal digits. For the flat standard Landau gauge on the SU(N) adjoint mean-zero tangent, \`det M_FP(I)=[det'(Delta_4)]^(N²-1)\`; in contrast the rooted maximal-tree **normalized Haar coordinate Jacobian** is exactly one. These are different gauge operations and different notions of Jacobian. Do NOT identify them.

**New local SU(N) Hessian stability inequality.** If all native links obey \`||U_e-I||_op <= delta\`, then elementary Hilbert–Schmidt trace Cauchy–Schwarz, including both source endpoints in every original link, gives

    |Q_U(omega)-Q_I(omega)|
       <= delta sum_(e=(x,y)) (||omega_x||+||omega_y||)²
       <= 16 delta ||omega||²,

because every original site has exactly eight incident oriented-edge endpoints. Hence, on mean-zero tangent vectors,

    Q_U(omega) >= [lambda_min(L)-16delta]||omega||².

At original L4 this is \`Q_U>0\` for all nonzero mean-zero omega whenever **delta<1/8**. In the same tangent chart, Weyl/min-max and determinant monotonicity give, with \`D=255(N²-1)\`,

    (1-8delta)^D
       <= det(M_FP(U)|mean-zero) / [det'(Delta_4)]^(N²-1)
       <= (1+8delta)^D.

This is a real, explicit local invertibility/relative-determinant estimate for the *standard Landau Hessian*. It is **not** global FP positivity, nonlinear gauge existence for every original field, a uniform all-volume estimate, or the literal Bałaban background chart. A source-specific small-field subset and an actual gauge-condition solution would be needed before using the estimate in a constrained integration theorem.

The all-periodic scalar smallest eigenvalue is \`lambda_min(L)=4 sin²(pi/L)\`, so a **raw global Landau** inverse bound in lattice units behaves as \`1/lambda_min(L) ~ L²/(4pi²)\`; its local-positivity condition becomes \`delta<sin²(pi/L)/4\` and shrinks as L increases. At physical spacing a, the actual eigenvalue scaling of \`Delta/a²\` must be tracked with the size of the physical box. This is a gauge-coordinate IR conditioning issue, **not evidence of massless physical particles**. Physically localized block gauges can change the geometry and must be analyzed on their selected domains.

## C. Exact wrong-sign gauge-stationarity witness on the SAME original Wilson orbit

For SU(2) on the even side-four periodic lattice choose two actual group-valued original 1,024-link configurations

    U_e^(+) = +I,   U_e^(-) = -I for EVERY original positive link.

Both have every ORIGINAL plaquette holonomy +I and hence the SAME action \`S=0\` and original two native deficit marks \`F=G=0\`. The genuine original site-gauge function \`g_x=(-I)^(sum_mu x_mu)\` transforms \`U^(-)\` into \`U^(+)\` on all original links; this is an *exact gauge equivalence in continuous SU(2)*, not a replacement Z2 gauge theory.

Both configurations solve the **first-order Landau stationarity equation** at \`g_x=I\`. Yet their Hessians satisfy

    Q_(U^+)(omega)= + <omega,Delta_4 omega>,
    Q_(U^-)(omega)= - <omega,Delta_4 omega>.

On the SU2 adjoint mean-zero site space \`D=3*(256-1)=765\`, the two determinants have opposite sign. The negative-Hessian representative is not a local Landau maximum and must not be called a second acceptable *positive-FP* fundamental-modular-region representative. It is a sharp **multiple-stationary-point / wrong-sign determinant counterexample** to any proposal that an unrestricted Landau-style delta constraint automatically supplies a globally constant positive FP normalization. The ACTUAL Bałaban axial and background-gauge terms may behave differently; nothing here computes their determinant.

## D. Reproducibility and exact local acceptance

[Committed checker](../../scripts/check_ym_p0_original_wilson_fp_flat_spectrum_gribov_20261124.py) imports only SymPy 1.14.0 and Python standard library; exact original periodic graph definitions, not a separate scalar lattice. **101,448/101,448 local assertion groups PASS**, comprising 3 original native graph counts; 3,072 actual centre-valued original plaquette holonomy evaluations; 1,024 original link gauge equivalences; original selected F/G face equality; 65,536 explicit eigenmode × source site Laplacian equalities; 256 exact diagonal checks and 256 zero-row-sum checks; 9 multiplicities; 7 exact nonzero determinant/sign/graph-tree checks; 31,250 exact noncommuting rational quaternion per-edge Hessian-error inequalities; 4 small-field radius algebra checks; and 21 finite-L/large-L spectral scaling tests.

Local executable SHA256 is \`5d6c3653f201cadcd4cfa664c734d78c3c11d463ee903812515c0f90b45c736b\`; verified GitHub Git blob \`1b3c24fe98801add1f4957cd21458aef774c8f4e\`, **byte-identical** to local execution. These check source geometry and identities; the all-SU(N) arbitrary-field trace norm estimate is a mathematical analytic proof, not an exhaustive SU(N) numerical enumeration.

## E. Reverse-solved P0 physical endpoint — exact remaining joins (not more abstract compilers)

**Physical T/source (CMP119/122):** select one true source-admissible \`Omega/Lambda/S\` domain history from CMP119 Eq.(2.18), with \`S_j\` inside the correct ordered \`T_k(X)\` and disjoint-component factors, actual source \`Q_B\`, background minimizer, constraints, gauge fixing, selected FP determinant/Jacobian, R-modifications and E/R/B/V with its running \`beta(a)\`. Prove the operator-level *functional* same-source identity on original F19/Haar and its 1/F/G/FG insertions (or a genuine four-relative-error bound including differentiated residual). The exact rooted tree Haar Jacobian=1 and this flat Landau determinant are both mathematical comparison inputs, **neither is the source-selected Eq.(1.71) Jacobian**.

**Absolute W3 (CMP116):** from that TRUE source, identify actual normalized two-mark \`partial_s partial_t log Z\` with the full physical **Ursell / incompatibility-connected** cluster expansion, not merely one bare factor-connected activity. The newest target \`master\` already contains the 23-Nov original Mayer one-component entropy, omitted-plaquette census and 24 cube-flipped twelve-interaction witnesses; reuse them. Prove the physical \`chargeSumBelowPhysicalRootedShell\` uniformly at the **actual weak-coupling \`beta(a)->infinity\`**, with absolute sums, large-field/small-field terms, entropy and a fixed positive physical length/time rate. Existing original \`beta<=1/72\` Dobrushin decay is a genuine small-beta theorem but does not apply on that path.

**Continuum + same-H OS:** construct the noncollapsed original interacting R4 continuum Schwinger/OS family, matching physical time scaling and reflection positivity, and show *every centered gauge-invariant vector of a dense core in the SAME H_OS* obeys a positive common-physical-exponent diagonal semigroup bound. The final spectral theorem allows finite \`C_v\` dependent on each core vector; do not demand uniform amplitudes in v, but DO require a common \`m>0\`, dense core and actual physical continuum. Reuse \`BalabanClayDenseCoreSpectralGapExact\`, \`YMPaper3RowCToDenseCoreGapAdapterExact\`. E1, D1, D2, N1, G1 and Clay "solved = true" remain **OPEN**. A finite side-four Hessian invertibility bound alone cannot produce the positive quantum mass.
