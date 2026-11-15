# Clay #1499 — C2 R853 selected-rate real-Fourier closure (Python/SymPy)

**15 November 2026. Gate C2.** Under the user's explicit Python/SymPy mathematical verification protocol, rather than Agda/CI, this establishes the original R853 **classical real-Fourier** selected-rate derivative and integral on the **unchanged** R854 horizon. This is *not* an Agda R408 rational-typed time-dependent packet, a native theorem/kernel receipt, or global Navier–Stokes regularity.

## Original source-defining owners and exactly identified functional

- R71: NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact.rawCanonicalRHSAt, the literal finite real Galerkin vector field, viscosity nu=1
- R224: NSTriadKNMixedHelicityFixedOutputSwapRound224Exact.mixedPlusMinus
- R230: NSTriadKNMixedHelicityForcingSwapRound230Exact.forcingCommutatorCell, including its essential minus sign
- R692: NSTriadKNR650GlobalCommutatorIncidenceExpansionRound692Exact.nonzeroGlobalCommutatorWork; Work.coherentWork = 2 Re Hermitian pairing
- R847: NSTriadKNR650Rational345CriticalFoldsRound847Exact production/dissipation, with the exact dyadic weight
- R853: NSTriadKNR650CanonicalSelectedRateNormalFormRound853Exact.selectedNormalForm, with margin=nu=1
- R830/R854/R856: original time horizon and exact safe integer-multiplier ceiling

For the complete radius-four nonzero cube (728 modes), use the genuine real-complex helical projectors for **all** modes:
  
    H_k^± v = (P_k v ± i(k × v)/sqrt(|k|²))/2,
    f_k(u) = -i P_k Σ_{p+q=k}(q·u_p)u_q,
    u'_k = -|k|² u_k + f_k(u).

Here f is the nonlinear-only forcing in R230, not the full viscous RHS. The exact original rate is

    M_k = Σ_{p+q=k} (H_p^+ u_p) × (H_q^- u_q),
    G_k = Σ_{p+q=k} [(H_p^+ f_p) × (H_q^- u_q)
                       - (H_p^- f_p) × (H_q^+ u_q)],
    C = 2 Re Σ_{k,j} conj(M_kj)*G_kj,
    P = 2 Re Σ_k w_k <u_k,f_k>,   D = Σ_k w_k |k|² |u_k|²,
    r(u) = 6(12*C-P+D),           w_k = 2^ceil(log2 ||k||_infinity).

These are **literal source formulas**, not a replacement with a zero-valued enstrophy residual.

## Independent exact original snapshot replay

The new executable acceptance script is scripts/check_clay_c2_r853_selected_rate_sympy_20261115.py. It reconstructs the six original nonzero velocity modes and the eight R829/R836 projected forcing modes, checks **24 exact complex forcing components**, then checks **all eight full mixed vectors and all eight full commutator vectors** against NSTriadKNR650Rational345VectorWorkRound829Exact.agda. It separately evaluates R692 C, R847 P/D and R853 r:

    C(0) = -557627/125,   P(0) = 0,   D(0) = 15834,
    r(0) = -28273644/125.

No numerical ODE trajectory, numerical quadrature or arbitrary candidate C/P/D values are used.

## Universal physical rate derivative bound

Work on the actual C1 2,184-dimensional real conjugacy-coordinate chart in the physical component ball ||x||_infinity <= M=12, with initial maximum 6. For every nonzero mode, the Leray matrix absolute row sum is <=2, and the curl cross row sum divided by |k| is <=sqrt(2). Thus **each real or imaginary coordinate** of a physical helical projection H_k^± is bounded by [(2+sqrt(2))/2] times the real-coordinate supremum, strictly below 2 times it.

Every fixed-output fibre contains <=n=728 ordered pairs, |q_j|<=4, |k|²<=48 and w_k<=8. Complex multiplication costs <=2 coordinate products per real/imaginary component, while the 3D cross is the signed difference of two such complex products. For any x,y in the ball and delta=||x-y||_infinity, the exact source finite-product bounds are:

    nonlinear forcing:    F=5031936,        FL=838656
    H velocity:           HU=24,            HUL=2
    H forcing:            HF=10063872,      HFL=1677312
    mixed vector M_k:     MB=1677312,       ML=279552
    commutator vector Gk: GB=1406687772672, GL=351671943168

Each first entry is an absolute component maximum; each second is a state Lipschitz coefficient. By the real Hermitian pairing and 728-mode sum,

    CL=12*n*(ML*GB+MB*GL)
      =8588413584135904296960,
    PL=2*8*n*3*2*(F+M*FL)
      =1055015829504,
    DL=8*n*3*48*4*M
      =40255488,
    Lambda=6*(12*CL+PL+DL)
      =618365778064115445891072.

Consequently |r(x)-r(y)|<=Lambda*delta universally on the ball. The genuine complete-real r is a finite polynomial with real algebraic coefficients. Along the C1 **actual** C¹ Galerkin solution, its chain rule and first-exit bound ||x'(t)||_infinity<=K=5032512 prove

    |r'(t)| <= Lambda*K for every 0<=t<=T_R854.

The original R854 reference scalar L=391309593930357307785216 satisfies Lambda < 2L. The already-present R856 **safe integer pointwise ceiling** is 10065030, and

    2K=10065024 <= 10065030.

On the **original** T=226189/3938540454339300631433585885184, exact rational arithmetic proves

    r(t) <= r(0) + Lambda*K*t
         <= r(0) + 2*L*K*T
         = -19/125 < 0.

The sharper exact upper is -19227416409761490377011/405027170798796125. FTC gives

    integral_0^T r(t)dt <= r(0)*T+(Lambda*K/2)*T² < 0,

with exact upper -25070826920278412129500923283/3190431794595304015221462227254444098439348224000.

This is a whole-ball, all-real-coordinates analytic proof. The script's 728 rational Leray row checks and all integer/rational comparisons are regression evidence; the finite-product inequalities and classical real ODE/FTC establish the universal inference.

## Acceptance and non-promotion

**Executed locally:** Python 3, SymPy 1.14.0; the committed script's exact Git blob was compared with the locally executed file and matched byte-for-byte (Git blob 90e75db5722afa236eeb06da68d6847c2d1933e2). All exact checks passed.

**C2 closure scope:** CLOSED_MATHEMATICAL_PYTHON_SYMPY, consistent with the C1 Python/SymPy gate protocol. No Agda 2.9 run, native C2 theorem term, Lean proof check, or actual rational-valued R408 global helical packet. Native R853/R408 real-field rebase and the historical original typed theorem/source trust obligations remain separately documented formalization debt. Existing Agda false booleans are not changed. P0/C1/C2 are 3/15 under the user's non-Agda protocol; 12 phase gates remain, 0/6 original endpoints are proved. E0 is still kernel-specific and cannot be closed via Python. The invalid unrestricted auxiliary W2/R823 reserve route is not resurrected by this negative signed-rate example.
