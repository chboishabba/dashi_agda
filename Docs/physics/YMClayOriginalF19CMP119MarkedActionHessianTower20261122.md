# YM P0 — original F19 to CMP119/122 marked effective-action Hessian and W3 absolute-charge boundary

22 November 2026. This records an exact finite-original-Wilson analytic result and local SymPy acceptance. It does not certify a physical CMP119/122 renormalized activity, Agda kernel, W3 shell charge or Clay Yang–Mills theorem.

## Existing source owners, credited rather than rebuilt

The actual original 1024-fine-link R445/F19 reordering (128 selected fine links in 64 ordered pairs; all 896 interacting spectators retained) and arbitrary-Haar integrand transport already live in YMClaySUNWeightedDisjointPairFibreReparamExact, YMClayOriginalWilsonPhysicalF19PartitionExact, YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact, YMClayOriginalWilsonCanonicalMarkedReindexExact and YMClaySUNOriginal64Pair896MarkedEffectiveSourceExact. The last owns the original coarse-ONLY F19 two-source identity; the fine two-source four-coefficient owner was newly source-written and remains Agda-kernel pending.

CMP119/122 already owns the source density/action and component infrastructure: BalabanCMP119SourceNativeRawStateActiveBoundsExact (section-2 E/R/B/V fields and at-scale predicates), BalabanCMP119Equation218FactorizedFunctionalDensityExact (domain sequences and finite T-products), BalabanCMP119DensityEffectiveActionProjectionRound214Exact, BalabanCMP119PhysicalEffectiveActionRealizationExact, BalabanCMP119Round214BackedPhysicalEffectiveActionExact, BalabanCMP119FactorizedMarkedBudgetVanishesExact and BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact. Source-selected action meaning and physical marked-step error/absolute decay are conditional. Existing source-first W1, CMP116, P06/Step-V/R429/KP/FP and physical W3 compilers must not be duplicated.

## Exact original finite Wilson marked action, arbitrary finite SU(N)

For the *actual* finite original Wilson product-Haar Gibbs law mu and bounded gauge-invariant real Wilson observables F,G with absolute values <=1, select nested original coarse sigma-fields C_k. Initial C_0 is the fine link field; the R445 F19 C_1 is the 64 noncommutative ordered two-link products. The original interacting Wilson density and all 896 spectators remain inside its positive fibre integral. With the repository's affine source M=(1+sF)(1+tG), |s|,|t|<=r=9/100, define K_k(w;s,t) as the original positive Wilson weighted Haar conditional-density integral at fixed C_k=w.

The original finite source has exactly four coefficients

    K_k(w;s,t) = K0_k(w) + s KF_k(w) + t KG_k(w) + st KFG_k(w).

At every finite cutoff, positivity of the original Gibbs weight and |F|,|G|<=1 give

    (1-r)^2 K0_k <= K_k(s,t) <= (1+r)^2 K0_k.

The source-dependent *effective action* A_k(w;s,t)=-log K_k(w;s,t) therefore exists on this real marked neighbourhood, and ordinary differentiation gives the exact original-source Hessian

    D_st A_k(w;s,t)
      = -[K0_k KFG_k - KF_k KG_k] / [K_k(w;s,t)]^2.

At zero source this is minus the original conditional Wilson connected covariance Cov_mu(F,G|C_k=w). The four coefficients and the normalized mixed log-partition derivative are the same original Wilson source throughout; they are not a newly selected CMP119 T-operation density.

For a single actual Haar reparametrization C_k -> C_{k+1}, finite Fubini supplies

    exp(-A_{k+1}) = E_ref[exp(-A_k)|C_{k+1}].

Let pi_{k,s,t} be the *actual marked Wilson positive fibre probability* proportional to exp(-A_k). Differentiating this original same-weight identity gives the required CMP119-style source marked action chain rule

    D_s A_{k+1} = E_pi[D_s A_k],
    D_t A_{k+1} = E_pi[D_t A_k],
    D_st A_{k+1}
      = E_pi[D_st A_k]
        - Cov_pi(D_s A_k, D_t A_k).

BOTH the inherited intrinsic mixed Hessian and the conditional first-source-score covariance must be retained. Dropping the incoming Hessian or independently coarse-averaging F and G changes the original full Wilson normalized mixed log jet. This is exact finite compact-group conditional calculus, not a new physical polymer smallness or RG decay theorem.

## Exact signed scale telescope and nonnegotiable W3 absolute bound

For nested original Gibbs coarse filtrations C_0 ⊃ ... ⊃ C_m (C_m trivial), let F_k=E_mu[F|C_k], G_k=E_mu[G|C_k]. Repeated conditional covariance gives

    Cov_mu(F,G) =
      sum_{k=0}^{m-1} E_mu[ Cov_mu(F_k,G_k | C_{k+1}) ].

This is a SIGNED identity, not the existing absolute source-first W3 rooted-shell inequality. Rigorous negative control, distinct from the Wilson model: take independent fair signs e1,e2 and bounded F=(e1+e2)/2, G=(e1-e2)/2. Conditional on e1, the fine covariance contribution equals -1/4 and the coarse contribution +1/4. Their total covariance is 0 but the sum of the absolute contributions is 1/2. Hence even an exact same-source RG covariance telescope cannot inhabit chargeSumBelowPhysicalRootedShell without separately bounding the ABSOLUTE differentiated local activities.

The chain-rule triangle for a true selected CMP119/122 source reads

    |D_st A_{k+1}| <= E_pi[|D_st A_k|]
                      + |Cov_pi(D_s A_k,D_t A_k)|.

It identifies exactly two classes of marked source charge needing localization, actual support geometry and physical decay; it supplies neither estimate by itself.

## Locally executed strict source reference

scripts/check_ym_original_f19_cmp119_multiscale_marked_hessian_20261122.py imports and executes the existing exhaustive original L4 fine F19 checker (1536 native plaquette words, 1024 true link addresses, 3 actual paired directions +9 live spectators, all other 1009 links frozen to identity, SU2 center-subgroup +/-I values, beta=log 2). Independently enumerated 32768 fine and 32768 R445 fibre/spectator assignments establish exact 1/F/G/FG equality.

Nested retained coarse signs 3 -> 2 -> 1 -> none give 8/4/2/1 source states, with exact rational telescoping ZERO residual. Contribution shares to the finite original covariance:

- fine -> 3 retained coarse signs: 74.17933636896161%
- 3 -> 2: 0.1362328943141383%
- 2 -> 1: 12.779599822528337%
- 1 -> none: 12.904830914195914%

The same marked action mixed-derivative chain rule passed exactly at 21 parent-fibre/source pairs (7 parent fibres times 3 rational affine source settings, including nonzero ±9/100); all 15 coarse states pass the derivative, positivity and bounded-score tests. Independent signed-cancellation negative control passes 0 versus absolute 1/2. The committed checker is byte-identical by Git blob hash to the locally executed script. The 15-link center subgroup conditional slice is NOT full continuous SU2 Haar quadrature or the physical running beta(a) trajectory. No GitHub CI or Agda kernel run.

## Real P0 source maximum cut, explicitly unchanged

Use the existing original CMP119/122 E/R/B/V action sources and T operations to prove, on the selected original full Wilson RG family, (i) same-action/density identification at each cutoff and physical step with both source derivatives and inherited Hessian, (ii) actual *renormalized* localized two-source polymer activity/cluster-log identity with the source-first W1 normalized Wilson response, (iii) absolute connecting marked shell sum sufficient for physical W3 chargeSumBelowPhysicalRootedShell with cutoff/volume-independent physical separation rate, and (iv) original full-Gibbs good-versus-CMP116 small-field and large-field control for D1. These physical estimates are not supplied by the finite source Hessian identity. E1 interacting R4 OS continuum, D2 dense same-H gauge-invariant gap, N1 noncollapse and G1 all compact simple groups remain OPEN.

Original attribution retained: Wilson/Haar, Bałaban CMP109/116/119/122, Kotecký–Preiss/Fernández–Procacci, and DASHI existing source owners. No new analytic theorem is credited as an already inhabited physical source record.
