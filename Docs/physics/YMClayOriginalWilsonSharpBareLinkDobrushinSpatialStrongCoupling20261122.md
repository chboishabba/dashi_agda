# YM P0 — source-sharp bare-link Dobrushin clustering for full compact SU(N) Wilson at small beta

22 Nov 2026. This is an original-source strengthening of the repo's existing 18*tanh(12*beta) conservative bare-link criterion; it is NOT a new Dobrushin theorem or the continuum Yang–Mills W3 shell estimate.

## Exact full original Wilson source and 18-neighbour geometry

Use the genuine original full positive-link periodic 4D Wilson product-Haar source, with L>=3 and compact SU(N), N>=2, Wilson action
    S_L(U)=beta*sum_{p original positive plaquettes}(1-t_p(U)),
    t_p(U)=ReTr(U_p)/N in [-1,1].
This is the same original density as YMClaySUNVariablePeriodicGibbsGaugeExact.periodicSUNGibbsDensity, differing only by its configuration-independent exp(-beta*#plaquettes) factor from the exp(beta*sum_p t_p) presentation. There is no gauge fixing, discarded spectator link, or invented effective measure.

At any periodic L>=3, there are 4 L^4 original positively oriented links, 6 L^4 positive oriented plaquettes, and each original link belongs to exactly 6 plaquettes. The 3 other positive links in each of those 6 plaquettes are 18 DISTINCT neighbours; each pair shares at most ONE original plaquette. The local exact geometry test enumerates all link/plaquette incidences for L=3,4,5, including native L4 1024 fine links, 1536 full original plaquettes and 18432 directed link-neighbour incidences.

For original single-link conditional gamma_i(dU_i|external), changing only adjacent external link j changes its source log density by h(U_i)=beta*(t_p(U_i;A)-t_p(U_i;B)) for one shared plaquette p. Because the normalized real trace is in [-1,1], h lies in [-2 beta, 2 beta] and osc(h)<=4 beta. For ANY strictly positive reference probability, exponential reweighting by h of oscillation <=w changes total variation by <=tanh(w/4). Hence the true full continuous SU(N) Wilson one-link conditional total-variation influence satisfies

    c_ij <= tanh(beta) * 1_{links i,j share an original plaquette}.
    max_i sum_j c_ij <= q(beta):=18*tanh(beta).

This is a bound on the genuine compact SU(N) Haar conditional for ANY exterior configuration. No integration over SU(N) is numerically approximated.

## Application of classical Dobrushin covariance comparison

The published Dobrushin theorem (not an original DASHI result) states, when row-sum q<1, for original bounded local observables F,G,

    |Cov_mu(F,G)| <= (1/4) sum_{i,j} delta_i(F) D_ij delta_j(G),
    D=(I-C)^-1=sum_{n>=0} C^n,
    delta_i(F)=sup variation when only original link i changes.

For real |F|,|G|<=1 supported on disjoint original positive-link sets X,Y, delta_i(F)<=2 on X and zero elsewhere (similarly Y). Since C is upper-bounded by the SYMMETRIC actual original link adjacency matrix times tanh(beta), both row and column sums of the dominating C are <=q. If d_link(X,Y) is the link-neighbour graph distance, no graph walk of length <d connects the supports. Summing the nonnegative matrix geometric series from n=d gives the explicit genuine ORIGINAL FULL WILSON finite spatial clustering bound, uniformly in periodic volume L>=3 and normalized SU(N) rank:

    beta < atanh(1/18) approximately 0.05561281755511219
       ==> |Cov_mu(F,G)| <= min(|X|,|Y|) q^d_link/(1-q).

A particularly simple certified rational regime is
    0<=beta<=1/36 ==> q<=18 beta<=1/2,
       ==> |Cov_mu(F,G)| <= 2 min(|X|,|Y|) 2^(-d_link).

This is a true original SU(N) finite-Wilson spatial covariance bound in lattice graph hops, with strict small-beta assumptions. Its mathematical proof uses the classical Dobrushin theorem after a source-specific, fully identified original link-conditional estimate.

Primary source authority: Jesús Salas and Alan D. Sokal, Absence of Phase Transition for Antiferromagnetic Potts Models via the Dobrushin Uniqueness Theorem, Journal of Statistical Physics 86 (1997) 551–579, DOI 10.1007/BF02199113, arXiv:cond-mat/9603068, Theorem 2.2 / Eq.(2.9) for general Dobrushin covariance comparison. The Potts work is credited as a statement of the general theorem, not as a source proving Yang–Mills physical continuum. Earlier DASHI source owners: Docs/physics/YMClayPhysicalCubeDobrushinCMP116Transport20261106.md, BalabanFiniteDobrushinReopeningExact, BalabanFiniteBoundaryConditionedDobrushinExact, YMClayPhysicalRGDriftToUniformInfluenceExact, YMClayRGDriftOriginalGibbsInstantiationExact. Preserve their priority.

## Exact source geometry and strict high-beta negative control

Executed local SymPy checker scripts/check_ym_original_wilson_sharp_dobrushin_link_clustering_20261122.py:
- L=3: 324 original links, 486 plaquettes, 5832 directed adjacency incidences, exactly 18 neighbours per link with one shared plaquette per pair.
- L=4: 1024 links, 1536 plaquettes, 18432 directed incidences; same exact invariants.
- L=5: 2500 links, 3750 plaquettes, 45000 directed incidences; same exact invariants.
- Two opposite original L4 cube-face plaquette observables have disjoint four-link supports and graph-hop separation 2.
- beta=1/36 exact rational q_upper=1/2; symbolic tanh(1/36)<1/36. q at beta=0.05 below 1, beta=0.06 above 1, beta=1 above 1.
- Full continuous Haar source mathematical conclusion is NOT inferred from the discrete test; it follows from the source conditional trace range and classic Dobrushin theorem.
- Committed regression matches locally executed script at Git blob SHA ab57a4097550d28108a078bc17f4b48c159b7372. No Agda kernel or GitHub CI.

## W3 and 4D UV / continuum exclusion

The relevant Clay weak-coupling path has beta(a) increasing as a decreases; then q(beta(a))=18 tanh(beta(a)) eventually exceeds 1 and the sufficient theorem no longer applies. Existing native SU2 one-link UV influence negative control scripts/check_ym_su2_wilson_singlelink_uv_influence_20261109.py also shows actual large-beta boundary sensitivity can approach maximal. The new small-beta bound is NOT a cutoff-uniform fixed-physical-block q<1 certificate. In addition its bound controls the WHOLE finite Wilson connected covariance, not the SUM OF ABSOLUTE source-selected CMP119/122 renormalized E/R/B/V differentiated individual cluster weights, and prefactors depend on fine support cardinality.

Actual remaining source payment still lives in original CMP119/122 and CMP116: construct the true weak-coupling beta(a) selected physical block source / real renormalized activity, identify original fine F19 1/F/G/FG two-J marked effective-action Hessian with source-selected CMP119 E/R/B/V and literal source-first W1 log cluster terms, and prove absolute two-support CMP116 rooted-shell chargeSumBelowPhysicalRootedShell uniformly in cutoff, volume and fixed physical length. Or prove quantitative original good-conditioned versus selected CMP116 small-J response with genuine physical-rate large-field error. Neither is supplied by bare-link high-temperature Dobrushin. E1/D1/D2/N1/G1 open; no mass gap claim or new Clay theorem.

Attribution: Wilson/Haar, Dobrushin and general covariance comparison, Salas–Sokal, original Bałaban CMP109/116/119/122, original DASHI physical-cube/influence and source-first marked W1/W3 owners.
