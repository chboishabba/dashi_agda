# YM P0 — TRUE original SU(N) Wilson two GLOBAL affine marks: uniform REAL marked W1 spatial decay at small bare beta

22 November 2026. Companion to [genuine compact-SU(N) original Wilson unmarked strong-coupling Dobrushin source](YMClayOriginalSUNWilsonDobrushinStrongCoupling20261122.md). Uses ALREADY-WRITTEN original \`YMClayOriginalWilsonAffineMarkedPartitionExact\`, \`YMClayOriginalWilsonTwoPlaquetteMarkedSourceExact\`, \`YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact\`, original SU(N) all-size Wilson and selected 9/100 two-J analytic radius. The result is a **finite-volume uniform real affine marked mixed LOG response spatial estimate** at strictly SMALL original beta, not merely a zero-source covariance and not an independent per-polymer marking. Classical Dobrushin/Föllmer comparison imported, no Agda kernel. All all-cutoff original weak-coupling CMP116/119/122 physical W3 and same-H Clay endpoints remain OPEN.

## Exact source and local geometry (not new measure or polymer gas)

On actual 4D periodic L>=3 original SU(N) Wilson product Haar with positive links and full original interaction w_beta(U)=exp(beta Σ_original_plaquettes t(U_p)), fix two **different disjoint-link original positive plaquettes** p,q (for example the two opposite y-z cube faces in existing original marked-Mayer and full continuous SU2 tube owners). Define actual bounded real gauge-invariant normalized trace Wilson marks

    F(U) = (1/N)ReTr U_p,    G(U) = (1/N)ReTr U_q,
    |F|,|G|<=1,     |supp F|=|supp G|=4,    supp F ∩ supp G=∅.

The SAME original globally affine marked partition already constructed in the repository is

    Z_beta(s,t) = ∫ w_beta(U) (1+sF(U))(1+tG(U)) dH^E(U).

For REAL |s|,|t|<=r=9/100, both factors are strictly positive. Therefore this is the original normalized Wilson Gibbs distribution with **two added local source potentials**

    dμ_{beta;s,t} ∝ exp{ βΣ_p t(U_p)
                          + log(1+sF(U))
                          + log(1+tG(U)) } dH^E(U).

There is exactly ONE global s-label and ONE global t-label; the logarithm gives a SUM of two local plaquette-supported action terms (no st cross-action), while the RG-integrated effective action at coarse scales DOES generate an intrinsic mixed Hessian via source covariance, as already correctly derived in YMClayOriginalF19CMP119MarkedActionHessianTower20261122.md. Nothing here asserts a bare or renormalized KP polymer activity is marked independently.

Both extra source terms use only the original four edges of an original Wilson plaquette. Thus the original plaquette-conflict graph (18 neighbours per original link, six original plaquettes incident per link) already contains ALL single-link influence edges of the two marked Gibbs specifications. No extra long-distance pair is created at the **fine** level; this statement is restricted to source marks that are individual local plaquettes, not arbitrary nonlocal Wilson loops. Since the plaquette supports are disjoint, each fine link belongs to at most ONE mark.

## Precise source-dependent Dobrushin influence matrix

For every original fine link ell, the original unmarked 4D Wilson conditional has six staple terms. For an exterior change of exactly one original neighbouring fine link j, only ONE original plaquette term changes; its conditional log-density difference has oscillation <=4 beta over the updated U_ell.

If ell and j both lie in the same marked original plaquette p (or q), there is in addition a source-potential change. Each local log(1+sF) lies in [log(1-r),log(1+r)], so the difference between two fixed exteriors lies in [-a,a], where

    a = log[(1+r)/(1-r)] = 2 atanh r.

Therefore that difference has oscillation <=2a. Apply the SHARP general exponential-tilt probability lemma, TV <=tanh(osc(delta log density)/4):

    c^{beta,s,t}_{ell,j}
       <= tanh(beta+atanh r)
       <= tanh beta + r

if (ell,j) share a marked plaquette. For a neighbour in a distinct unmarked plaquette, c<=tanh beta. For non-neighbours, c=0. A given fine link is a member of at most one of the two marked plaquette supports, hence has only THREE marked neighbours among its 18 original neighbours. The EXACT original-source row-sum sufficient estimate is

    alpha_marked(beta,s,t)
       <= 18 tanh beta + 3r.

Take the strict, explicit strong-coupling window

    0 <= beta <= 1/72,    |s|,|t| <= 9/100,  s,t REAL.

Using tanh beta <= beta gives uniformly for every cutoff, periodic volume and compact SU(N),

    alpha_marked <= 18*(1/72)+3*(9/100)
                 = 1/4+27/100
                 = 13/25 =: q_marked < 1.

This is an actual original-source marked Gibbs Dobrushin margin for the REAL source neighbourhood, not complex positive Gibbs: for complex s,t the source may be nonpositive and Föllmer's probability theorem cannot simply be applied, although the earlier original SOURCE complex zero-free polydisc remains valid.

## Consequence for the exact globally marked W1 source mixed logarithmic response

Ordinary differentiation of the concrete original finite global affine Z yields

    ∂_s ∂_t log Z_beta(s,t)
       = Cov_{μ_beta;s,t}( f_s, g_t ),

where the scores f_s=F/(1+sF) and g_t=G/(1+tG) depend on the SAME original four fine links of F and G, respectively. Their exact pointwise ranges are

    f_s ∈ [-1/(1-s), 1/(1+s)] (and analogously for g_t),
    δ_ell(f_s) <= 2/(1-s²) <= 2/(1-r²),
    δ_j(g_t)  <= 2/(1-t²) <= 2/(1-r²).

By the standard imported Föllmer covariance estimate on the ORIGINAL positive marked Wilson compact product Haar Gibbs specification, with D=(I-C)^-1, graph distance d=d_conflict(supp F,supp G), and max row sum q_marked<1, the source-resolvent has D_ell,j<=q_marked^d/(1-q_marked). Using the conservative oscillation covariance normalization (no subunit factor), one obtains for the REAL source square the strict uniform original Wilson result

    |∂_s ∂_t log Z_beta(s,t)|
      <= [4/(1-r²)^2] [1/(1-q_marked)]
           |supp F| |supp G| q_marked^d
      = [2500000000/295159683] |supp F| |supp G|
           (13/25)^d.

For two original Wilson plaquette marks with four fine links each,

    BOX:
    |∂_s ∂_t log Z_beta(s,t)|
      <= [40000000000/295159683] (13/25)^d.

This is a genuinely **spatially decaying marked mixed logarithmic source response** of the true ORIGINAL 4D SU(N) Wilson finite Gibbs measure on the stated small-beta/real-source square, uniform in periodic volume; it preserves globally unique affine insertions and makes no independence assumption on the interacting fine links. At (s,t)=(0,0), this same mixed derivative is the original full connected two-plaquette covariance already owned by YMClayOriginalWilsonTwoPlaquetteMarkedSourceExact. No extra coarse effective measure is introduced.

The physical distance d is in the original fine-link **plaquette-conflict graph** and the rate -log(13/25) is dimensionless per such graph edge. A selected finite lattice spacing a gives a lattice physical inverse length of order -log(q)/a, but **this is not a continuum SI positive mass** and does not cover the required beta(a)->infinity asymptotically free trajectory.

## Exact local mathematical regression and receipts

Executed in local Python/SymPy 1.14:

- \`scripts/check_ym_original_sun_dobrushin_strongcoupling_20261122.py\`: exact full ORIGINAL periodic 4D L=3/4/5 six-plaquette / 18-neighbour incidence, 1024-link/1536-plaquette L4 and each link pair sharing at most one source plaquette, exact TV extremizer, alpha criterion and unmarked original covariance; Git blob a66563d2987a2e3f3768b06519a237a3e80ae732, byte-matched to locally executed file.
- \`scripts/check_ym_original_sun_affine_marked_dobrushin_20261122.py\`: EXACT symbolic source-local surcharge tanh(atanh r)=r, 256 positive four-atom two-global-mark laws and 1,024 rational real (s,t) source settings verify \`∂_s∂_t log Z=Cov_tilt(f_s,g_t)\`; sharp rational q=13/25 and score covariance-resolvent prefactor 2500000000/295159683; Git blob 2a9d340e96f04e66861527733fc42606a44a152b, byte-matched to locally executed file.

Full continuous SU(N) Wilson compact Haar steps are PROVED analytically using the bounded normalized trace and original actual six-staple structure and **standard imported covariance theorem**, not by full Haar numeric integration. Exact local scripts test finite geometry/algebra, not SU(N) Agda formalization, not a physical multiscale RG estimate. No GitHub CI, Agda 2.9 kernel, formal Borel measure-to-original compiler or Clay accepted endpoint.

## Source provenance and the next physical MAX CUT

Primary mathematical theory: R. Dobrushin (1968) weak dependence; Hans Föllmer, *A Covariance Estimate for Gibbs Measures*, JFA 46 (1982) 387–395 (existing published covariance comparison); original Wilson gauge action, Haar; previously implemented DASHI original 4D SU(N), genuine two-plaquette marked affine source, R445/F19 four coefficients and CMP119 signed marked Hessian tower. Compare the external earlier Wilson strong-coupling sufficient one-link inequality 18(e^{4 beta}-1) at https://arivero.github.io/navstokgap/notes/dobrushin-uniqueness-wilson.html ; the new estimate is an elementary bounded log-oscillation sharpening and applies additionally to the actual TWO global real source marks. No claim to invent Dobrushin or prove a new general spin-system theorem.

**The missing Clay YM physical W3 is STILL OPEN.** At required a→0 and beta(a)→∞, single-link Dobrushin is not uniformly contracting (original opposite-staple obstruction already documented). The new true-original small-beta W1 marked decay is useful as a positive same-source control and regression target, but it is NOT a source-native **renormalized CMP119/122 block** small/large-field activity and does not inhabit \`SourceFirstNormalizedWilsonJetExpansion.normalizedPhysicalLogJetIsLiteralKPClusterJetSum\`, the **ABSOLUTE** rooted polymer W3 charge \`chargeSumBelowPhysicalRootedShell\`, or original full E1 nontrivial continuum / same-H D2 spectral gap. To reach those one still must:
1. Build/source-identify actual CMP119/122 RG marked E/R/B/V small/large-field action and correct global two-mark K0/KF/KG/KFG transport with real original full 896 spectator fibres (already finite F19-welded);
2. Obtain a **physical-block** influence or source-rooted-shell inequality stable as beta(a) increases, with nonvacuous domain/positive-time support and volume/cutoff-independent margin q<1 at a fixed positive **physical** block length, including inherited Hessians;
3. Identify the same normalized Wilson marked source with renormalized literal CMP116 bond J/physical W1 cluster log and bound individual ABSOLUTE W3 connected charges, then E1 and same-H dense D2/N1/G1.

Do not credit this high-temperature theorem as a repaired UV mass-gap proof. It is restricted but mathematically source-specific positive progress.
