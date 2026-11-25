# YM W0 — CMP119 source-domain and constrained-T prior-art audit (23 Nov 2026)

## Finding: most geometrical ingredients already exist

Before proposing another operator or domain AST, inspect the following actual source owners. Primary source archived in-repo: `Docs/support/reference/balaban-source-extracts/cmp119-rg-lattice-gauge-i.txt`, pp. 254–258, Sect. 2, Eqs. (2.1)–(2.3), (2.10)–(2.23). Text extracted from original CMP119, with some OCR symbols corrupted; do not infer an exact mathematical set inclusion from corrupt OCR.

- `P10SourceFaithfulActivityContract.agda`: `P10P11WeightedRelativeDomainCarrier` already exposes `inOmega`, `inRelativeDomain`, `nestedDomains`, `terminalOwner`, `ownerUnique`, explicit component coverage and uniqueness, relative-domain geometry, halo and weighted mass constraints. This is a strong **candidate donor** for the CMP119 Omega/determining-set geometry, not a proven source-identification theorem.
- `BalabanCubeEdgeDomains.agda`: `LocalizationDomain` and `AdmissibleCubeEdgeTree`, based on the existing connected face-cube graph and closed-cube edge incidence. These are CMP109 localization/tree constructions; they cannot be relabelled as a complete triple (Omega,Lambda,S) without a source proof.
- `BalabanClayGate4TypedReuseAndFiniteGeometryExact.agda`: typed existing large-field bad-component geometry and first-/second-class support split; `largeFieldEnlargementAndCollarInputsLevel` conditional.
- `BalabanClayGate4FiniteEnlargementCollarOwnershipExact.agda`: finite enlargement, source-boundary collar and support ownership, with metric source-radius and analytic boundary reinjection still conditional.
- `BalabanClayP3FiniteConstrainedIntegralExact.agda`: exact `blockMap`, `coarseMatches`, constrained finite sum and small/large partition; `p3CompactHaarIntegralLimitLevel` conditional.
- `BalabanClayGate4ComponentClassAndFiniteTOperationExact.agda`, `BalabanClayGate4CanonicalRationalPhysicalTExact.agda`: finite localized T acting on functionals; rational finite reference sum is not automatically continuous SU(N) Haar.
- `BalabanCMP122Equation171TOperationSemanticsExact.agda`: source T constrained-integral definition with `literalCMP122Equation171FiniteRealizationLevel` conditional.
- `BalabanCMP119Equation218FactorizedFunctionalDensityExact.agda`: `admissibleSequences`, `componentsAt`, `orderedStepsAt`, `oneStepValue`, `sequenceResidual`; Eqs. 2.18, 2.19 and 2.20 literal index/step extraction flags conditional.
- `BalabanCMP119Equation171WeightedStepApproximationExact.agda`: sequence/component/step-indexed `sourceTAt` and `sourceStepIsEquation171Mass` equality **field**; existing majorant propagation, not an independent proof of source physical equality.
- `BalabanCMP119FactorizedDensityApproximationExact.agda`: existing scalar step/component/sequence absolute majorant telescopes.
- `BalabanCMP119Section2SourceNativeStateExact.agda`, `BalabanSourceNativeStrongStateEntryExact.agda`: source-native complete E/R/B/T action and same-object projection; source physical instantiation still conditional.
- `YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact.agda`: existing same-original-interacting-Wilson 1/F/G/FG four-moment F19 Haar transport, with 896 spectators; Agda kernel receipt pending.

## Comparison to literal CMP119

Reading the actual CMP119 source extract at pp. 254–258 yields:
1. Nested Omega_j domains, plus Lambda_j and S_j families, with source-specific (2.1) set conditions, nonempty S when Omega meets Lambda, original large-field characteristic factors, and determining set B; also background minima U_B(V) and source averaging M_B(U).
2. Eq. (2.18) sum over admissible domain sequences, with S_j summation **included in T_k**, and A_k depending on all three domain families; 2.17 carries an independent characteristic function.
3. Eq. (2.19) T_k disjoint-region component factorization/commutation, only when genuine separated source regions allow it.
4. Eq. (2.20) ordered product of scale steps, including specific fluctuation/gauge field integrations on intersections Z_(j+1)∩Omega_(j+1)∩X, with localization/characteristic, constraint-delta and gauge-fixing factors. R-operation changes the characteristic/domain conditions; (2.22) splits a sequence of unmodified and modified T steps.
5. Eq. (2.23) physical action Wilson + E + R + B - vacuum contribution on the source-selected background.

Thus **the source itself confirms that the scalar path reconstruction is mathematically appropriate only AFTER all conditioned domain and field histories have been fixed**. S_j is summed INSIDE T, not independently overcounted in the outer (2.18) list. This prevents a subtle double-count/normalization error when adapting a generic path toy model.

## Primary-source Eq. (1.71) recheck from original CMP122-II PDF (25 Nov 2026)

Original journal PDF checked locally: T. Bałaban, *Large Field Renormalization. II. Localization, Exponentiation, and Bounds for the R Operation*, Commun. Math. Phys. 122 (1989), 355--392, DOI [`10.1007/BF01238433`](https://doi.org/10.1007/BF01238433). The in-repo text extract at `Docs/support/reference/balaban-source-extracts/cmp122-rg-lattice-gauge-ii.txt` truncates the displayed Eq. (1.71) formula; OCR of printed pp. 378--379 confirms the following structural ingredients:

- Eq. (1.71) defines `T_k(X)` for one component `X` by localized constrained integrations over fluctuation/gauge variables, with a sum over admissible domain histories and Euclidean symmetries `r`;
- the exponential density contains the Wilson/action and quadratic forms, `V(X~, U_k)`, `E_k(X)`, a `(-3d(g_k) log g_k + log c_0) |(B_0 \ T_0) ∩ X|` factor, and `-E(A \ X)`;
- p. 379 states `T = T_0 ∩ X`, `rT` is the axial tree in the transformed coordinate system, and the symmetry sum uses only the `2^d` coordinate reflections and `d!` permutations;
- pp. 379--380 then derive the analyticity/comparison bounds (1.73)--(1.75) and the small-factor bound (1.89).

This is a source-fidelity confirmation of `BalabanCMP122Equation171TOperationSemanticsExact`: the T-operation mass is the **result** of the localized integral, not a pre-existing global action exponential. It does **not** raise `literalCMP122Equation171FiniteRealizationLevel` or `literalCMP119StepIsEquation171OperationLevel`; the unpaid leaf remains one original Wilson/F19 four-mark instance whose conditional finite mass equals this literal localized T on selected CMP119 `Ω/Λ/S` histories with all gauge/FP/Jacobian/R and `E/R/B/V` factors. The original CMP119 journal PDF (DOI [`10.1007/BF01217741`](https://doi.org/10.1007/BF01217741), printed pp. 243--285) was located locally as well; its Eqs. (2.18)--(2.23) conclusion above is unchanged.

## Max-cut rather than another construction

Reuse the existing Omega ownership, cubical geometry, collars, P3 integration, source Eq171 T, CMP119 ordered scalar expression, beta history and exact F19 four-mark producers. The remaining source attachment is a **single compatibility/witness** demonstrating that:
- the source's genuine nested Omega/Lambda/S histories and determining B meet the exact CMP119 conditions at the selected original Wilson cutoff;
- source T step supports and correct R-modified histories agree with the existing P3/Gate4 fibre, conditional reference measure and original SU(N) product Haar;
- S_j is integrated in the T-coordinate and **not** additionally enumerated in the outer sequence; disjoint components are conditionally independent only with their specified boundary;
- the original global fine marks F and G remain unique, with all four fine-F19 K0,KF,KG,KFG coefficients and the 896 interacting spectators;
- all characteristic, delta, gauge-fixing, background, Jacobian, localized residual and vacuum normalization factors remain;
- E/R/B selected physical source action, active coupling history, Section-2 analytic bounds and W3 absolute rooted connecting-shell physical rate are proved, not instantiated as arbitrary record fields.

No checked module above has been shown to provide that whole source-specific compatibility proof; source-named types and `machineChecked` compiler-level tags alone are insufficient. In particular, an SU(N) finite-Haar-to-rational-quadrature limit is an explicit unresolved dependency, not a harmless normalization choice.

## Verification

Read the primary CMP119 source extract directly from the repository, inspected specific Agda record fields, and compared the existing inputs to its p.254–258 construction. This was a source audit; **no new physical numerical test, Agda kernel or CI** executed. Previous local finite path SymPy example remains a toy repair, not a literal CMP119 domain instance.

Attribution: Bałaban CMP109/CMP119/CMP122 original geometry and ordered T; original Wilson/Haar; existing DASHI P10/P11, P3, Gate4, CMP119/122 and F19 authors.
