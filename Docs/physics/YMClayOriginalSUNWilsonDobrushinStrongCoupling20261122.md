# YM P0 — original continuous SU(N) Wilson finite-volume uniform spatial decay in the genuine strong-coupling regime

Date: 22 November 2026. STATUS: **actual original 4D compact SU(N) Wilson law** analytic strong-coupling result (published standard Dobrushin/Föllmer covariance theorem applied to exact original source), original link/plaquette geometry and exact rational/SymPy local regression PASS. **Not** a weak-coupling continuum YM estimate, not actual CMP116/119/122 W3 root-shell inhabitant, not a new general spectral theorem, and NOT Agda 2.9 kernel acceptance. This is a source-grounded **restricted-coupling** D1 benchmark.

## Exact original source and link adjacency

Use the same variable-size 4D original periodic SU(N) Wilson product-Haar Gibbs source already defined by \`YMClaySUNVariablePeriodicGibbsGaugeExact\`, \`YMClayOriginalWilsonFiniteTwoSourceJetExact\`, \`YMClayOriginalVariableWilsonCovarianceSourceExact\` and \`YMClayE1OriginalSUNDependentCylinderExact\` (not a surrogate coarse/independent measure). On a periodic side-L four-torus with L>=3 the true positive link set has E=4L^4 and positive oriented Wilson plaquettes P=6L^4. The normalized trace is

    t_p(U)= (1/N) Re Tr(U_p) ∈ [-1,1],
    dμ_β(U) = Z_β^{-1} exp(β Σ_{p∈P} t_p(U)) ∏_{ell∈E} dH(U_ell).

The original deficit-action convention exp(-β Σ(1-t_p)) is equivalent up to exp(-β|P|), exactly cancelling in the normalized source.

Each original positive link ell belongs to SIX plaquettes. Each such plaquette has exactly THREE further positive link variables and, for L>=3, the six triples are disjoint. Thus its original plaquette-conflict neighbourhood N(ell) has EXACTLY 18 distinct links. Every pair (ell,j) shares at most one original plaquette. This is the native 4D graph used in the original 18-conflict degree and 12/8-color owners, not an abstract lattice. Independent exhaustive exact scripts for L=3,4,5 give

    L   |E|   |P|    distinct adjacent unordered link pairs
    3    324    486    2,916
    4  1,024  1,536    9,216
    5  2,500  3,750   22,500

and verify every original link six-plaquette incidence, every degree 18, and every unordered adjacent link pair sharing exactly one face. The all-L statement follows from the same explicit 4D periodic plaquette coordinate formula, with L>=3 preventing wrapped edge coincidences. No projection/frozen spectator alters the theorem.

## NEW quantitative same-original Wilson one-link conditional bound

Condition on ALL other original SU(N) links in the *same Wilson Gibbs law*. With six original three-link staples, the actual conditional distribution at ell is

    ν_ell(dU | η) ∝ exp[β Σ_{p∋ell} t(U S_p(η))] dH(U),

where orientations/inverse links are absorbed in the unitary staples S_p. Change exactly one exterior link j, holding every other actual original link fixed.

If j is not in N(ell), ν_ell does not change. If j is in N(ell), EXACTLY ONE original Wilson plaquette is affected, so for each value U of the updated link the difference h(U) of the two conditional log densities (before normalizers) is between -2β and 2β. The full oscillation obeys

    osc_U[h] = sup_U h(U) - inf_U h(U) <= 4β.

For any two Gibbs densities on the same base probability space related by an exponential tilt e^h, the sharp universal total-variation estimate is

    TV(ν_h,ν) <= tanh(osc(h)/4).

Proof (elementary): write Y=e^h ∈ [a,b], and ν_h(A)=E[Y 1_A]/E Y. Extremizing the TV ratio first reduces the distribution of Y to the two endpoint values a,b; for base mass x at b, TV=(b-a)x(1-x)/(a+(b-a)x), maximized at x=√a/(√a+√b), with maximum (√b-√a)/(√b+√a)=tanh((log b-log a)/4). This is a bound over ALL positive reference measures, including real continuous SU(N) Haar; no SU2-centre/Q8 quadrature premise.

Hence the true original Wilson one-link Dobrushin influence matrix C obeys

    0<=C_ell,j<= 1_{j∈N(ell)} tanh β
    α := sup_ell Σ_j C_ell,j <= 18 tanh β.

This is a stronger, explicit normalization-matched estimate than the old generic 18 tanh(12 β) source fallback and the external weak 18(e^{4β}-1) note; its strength is limited to **small β**. At β near a weak-coupling UV trajectory, α's upper bound is not below one. Nothing about the blocked CMP119/R445 influence is supplied.

## Actual source D1 covariance in the explicit strong-coupling window

When β<atanh(1/18) = (1/2)log(19/17)≈0.0556128175551, α<1. Standard Föllmer's covariance estimate from the Dobrushin interdependence resolvent D=(I-C)^-1=Σ_{n>=0}C^n applies to this finite compact spin Gibbs law. For a bounded cylinder observable F depending only on original positive link subset A, write δ_i F = sup_{U=U' off i}|F(U)-F(U')|. The standard theorem controls |Cov(F,G)| by a bilinear form in δF, D, δG. To be conservative about the oscillation normalization, we DROP any subunit prefactor and use

    |Cov_β(F,G)| <= Σ_{i∈A,j∈B} (δ_i F) D_ij (δ_j G).

The covariance theorem is standard imported mathematics (Föllmer 1982), not an original DASHI kernel proof.

Let d(A,B) be minimum distance between A and B in the **ACTUAL 18-neighbour plaquette-conflict graph**. Since C_ij=0 unless links share an original plaquette, (C^n)_ij=0 for n<d(A,B), while nonnegative matrix row sums obey Σ_j(C^n)_ij <= α^n. Consequently

    D_ij <= α^{d(A,B)} / (1-α).

For bounded original real gauge-invariant Wilson word/plaquette insertions |F|,|G|<=1, δ_i F,δ_j G<=2. Thus the honest finite-volume true-original covariance result is

    |Cov_{original β}(F,G)|
        <= 4 |A||B| α^{d(A,B)} / (1-α).

In particular for the explicitly rational strong-coupling window

    0 <= β <= 1/36

we have 18 tanh β < 18 β <=1/2, and therefore the all-finite-periodic-volume, all-compact-SU(N) source inequality

    BOX:
    |Cov_{original β}(F,G)|
      <= 8 |A| |B| 2^{-d(A,B)}.

For an original Wilson plaquette trace F and another closed plaquette trace G each supported on 4 positive links, the conservative bound becomes 128*2^{-d}. The rate is positive **per original bare-link conflict-graph step**, not a fixed continuum physical mass; graph distance n can be calibrated with a>0 only at a selected finite lattice spacing. There is no dependence on |E|, |P|, the 896 spectators, or volume in the amplitude other than local support sizes. At β=0, product Haar already gives zero covariance for disjoint link supports.

The theorem does not identify this strong-coupling Gibbs law with CMP116's selected analytic localized J, does not give W3 **absolute polymer charges** term-by-term, and does not prove any universal G1 local continuum theorem (although this finite bound uses any compact SU(N) normalized trace). No claim of a continuum D1 along the required asymptotically free bare coupling β(a)→∞ is valid.

## Exact local reference; trusted ingredients

Locally executed Python/SymPy 1.14 script:

    scripts/check_ym_original_sun_dobrushin_strongcoupling_20261122.py

GitHub commit d17e40ea. Exhaustive genuine periodic L=3,4,5 geometry tests PASS (324/1024/2500 original links; 486/1536/3750 original plaquettes; all six/18 incidences and unique shared face). Independent exact symbolic extremization for exponential-tilt TV passes, as do rational β<=1/36 and explicit graph-resolvent conservative spatial envelope. The committed code has been read back and its Git blob SHA a66563d2987a2e3f3768b06519a237a3e80ae732 was verified **equal to the locally executed file's independently computed Git blob SHA**. This is an exact byte-level local-source receipt (still not Agda or CI). This script is a geometric/elementary analytic reference **not** actual full original continuous SU(N) numerical integral, not an Agda proof, not CI.

Standard theorem/provenance:
- R. L. Dobrushin, 1968, interdependence uniqueness criterion.
- Hans Föllmer, "A Covariance Estimate for Gibbs Measures", Journal of Functional Analysis 46 (1982) 387–395 (the classical covariance comparison used here).
- Wilson original four-dimensional compact-group lattice gauge action, Haar positivity.
- DASHI existing original 4D all-L SU(N) Wilson/Gibbs carrier, source covariance, bare-link UV no-go, R445/F19 and W1/W3 sources.
- External independent earlier Wilson one-link sufficient strong-coupling discussion: https://arivero.github.io/navstokgap/notes/dobrushin-uniqueness-wilson.html, using a looser one-link estimate 18(e^{4β}-1). This note does not claim originality for the published covariance route.

## Mandatory P0 firewall: DO NOT PROMOTE THE WRONG BETA

At the physical 4D continuum trajectory for asymptotically free SU(N), β(a) grows as a→0. The sufficient bare-link inequality α<=18 tanh β becomes uninformative there, and the repo's existing UV bare-link opposite-staple TV lower bound shows why a fixed uniform bare-link Dobrushin contraction is not a viable physical strategy. This theorem occupies the true original Wilson **strong-coupling** regime, not the CMP119/122 renormalized weak-coupling region. It is a mathematically explicit original same-source spatial-decay control/negative comparator, and belongs in the REUSE ledger, not as a solved E1/D2 or physical W3 endpoint.

The actual P0 remains: construct the selected original Wilson CMP119/122 **renormalized** good-/large-field marked activity on the *same full real Wilson F19 1/F/G/FG source* including 896 spectators, pay its actual analytic bond-J/cluster log identification with CMP116/W1 and the ABSOLUTE W3 physical rooted shell charge at one cutoff/volume-uniform physical rate; then nontrivial original E1 continuum and full same-H dense nonvacuum OS spectral exclusion, N1 and G1. Finite original Wilson strong-coupling clustering does NOT automatically make the quantum continuum physical mass gap.
