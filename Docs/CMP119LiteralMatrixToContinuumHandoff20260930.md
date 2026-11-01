# Selected CMP119 physical action / continuum handoff (2026-09-30)

## Primary source and actual code scope

Wilson, *Confinement of Quarks* (1974), DOI 10.1103/PhysRevD.10.2445: standard positive SU(2) plaquette cost W+(U)=1-ReTr(U)/2, bare beta=4/g0^2. Balaban CMP109 (1987), DOI 10.1007/BF01215223: coupling recurrence. Balaban CMP119 (1988), DOI 10.1007/BF01217741: selected complete effective-density sectors, requiring exact published-action/trace/exponent identification before any promotion.

The older Agda SUNWilsonAction and BalabanClayT4SUNWilsonActionConventionExact already operate on actual SU(N) plaquette loops and matrix trace authority, but choose a repository inverse-g-squared coefficient rather than the conventional four-times coefficient for standard bare SU(2) cost. CMP119AntigravityWilsonPlaquetteBasisOrientationExact already proved the factor-of-four conversion and sign reversal in the symbolic T4 coefficient basis. These are action conventions, not published CMP119 source identification.

NEW: CMP119SUNWilsonMatrixBareNormalizationExact.agda evaluates the SAME actual SU(2) matrix Wilson action with coefficient 4u, proves equality to u times a four-rescaled basis and (-4u) times the negative-cost basis, carries the full gauge-invariance theorem, and relates the matrix-action value to the T4 coefficient projector without identifying the complete CMP119 source action.

NEW: scripts/grqft_su2_literal_wilson_exact.py computes a single literal rational SU(2) quaternion link plaquette, exact matrix trace/cost, bare factor-four action and optional independent vertex-gauge transformations. A cross-audit regression uses two actual quaternion-computed plaquette traces as inputs to the existing grqft_selected_wilson_normalization_audit.py. E/R/B/vacuum exponents in these regressions are synthetic; neither a selected nonlinear Haar measure nor source-sector authority has been constructed.

NEW: scripts/grqft_selected_finite_stress_exact_audit.py now requires a separately identified Lorentzian timelike numerator before comparing against the selected weak YM E/B active-stress baseline. It computes exact active continuation correction and refuses automatic Euclidean C00 = Lorentzian rho. External continuation values and counterterm revisions remain unproved input, not physically derived tensors.

## The existing stronger Lean finite result

Connected Lean YM PR #15, YangMills/LiteralSU2FiniteWilson.lean, already defines the fundamental 2x2 SU(2) trace, bounded physical plaquette cost, standard bare beta, and four CMP119 sectors in a finite action. It has source-written finite Boltzmann/partition positivity and bounds for an explicit probability reference measure, given sector lower/upper bounds and measurability. That is more than a conditional abstract measure interface. But its sector bounds depend on cutoff and volume, and it does not select the published full CMP119 density/product Haar family or prove common-space uniform continuum moments.

The Lean DirectSourceOSContinuum theorem therefore remains generic: changing-cutoff selected physical measures must independently pay its common topology, coercivity, cylinder expectation limits and reflection-Gram hypotheses. The Yang-Mills mass gap, OS complex reconstruction and local interacting QFT remain open.

## Exact unclosed physical producers

1. Identify selected CMP119 published Eq.(2.23) action, SU(2) trace and plaquette basis, source coupling, sign and full non-Wilson E/R/B/vacuum sectors on the SAME literal matrix gauge action.
2. Supply actual Ward reduction plus 240-box quadrature/shell certificates; prove the strict beta floor inequality from the selected finite-mode integrals rather than setting the inequality field.
3. Build changing-cutoff product-Haar Gibbs measures on a common projective physical configuration space and prove cutoff-uniform moments, finite complex reflection positivity and cylinder expectation convergence.
4. Compute selected metric dependent D1 and insertion/measure/counterterm responses, construct independently the continued Lorentzian timelike stress and prove conservation, curvature convergence and source-consistent gravitational backreaction.
5. After construction, make independent fixed-parameter cosmology, antimatter and collider predictions; retain source provenance and SI normalisation.

No finite rational receipt, conditional continuum theorem, or CMS chi-square by itself proves quantum gravity or Clay Yang-Mills. No exact-head kernel/Actions acceptance is currently certified.
