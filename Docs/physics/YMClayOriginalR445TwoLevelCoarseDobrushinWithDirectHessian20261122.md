# YM P0 — two-level original Wilson R445/F19 Dobrushin: real coarse K0(W) contraction with shared-plaquette Hessian

22 November 2026. **New exact original-source finite one-step RG quantitative result at SMALL bare beta.** This is the actual full original compact SU(N) Wilson/Haar marginal K0(W), NOT a bare-Wilson substitute effective action, not a toy decimation and not physical CMP119/122 W3. It builds specifically on the already-owned native R445 64 ordered product pairs/896 interacting spectators, the fixed-W 960-variable F19 conditional Haar bound, and true coarse log K0 mixed finite-difference source note. It pays a strictly stronger RESULT: the entire induced **coarse Gibbs specification** has a Dobrushin row coefficient <1 in an explicit source regime. No Agda kernel or CI.

## Original source definition and two Dobrushin levels

Use the original real 4D periodic side-four 1,024 positive-link compact SU(N) Wilson measure with ALL 1,536 original normalized real trace plaquettes, original positive product Haar and beta>=0. By existing original native R445 algebra, choose the genuine 64 axial pairs of consecutive original positive links from the 16 all-even original sites. Write W_i=U0_i U1_i, V_i=U1_i; reconstruct U0_i=W_i V_i^-1. The 896 remaining original positive links S are still interacting; the fixed-W reference is 64 V Haar factors times 896 S Haar factors.

Define the ACTUAL induced coarse law with product Haar reference on W_i,

    K0(W) = integral_(SU(N)^64 V × SU(N)^896 S)
                  exp(beta sum_[1536 original p] t_p(W,V,S)) dH(V)dH(S).

This is the same exact original F19 K0 source coefficient. Pair change-of-variables preserves full original product Haar. For every fixed W, each Wilson plaquette depends on FOUR DISTINCT post-reindex independent variables. Original full-action conditional Gibbs single-variable Dobrushin influence is dominated by c_ab<=m_ab*tanh(beta), where m_ab counts source plaquettes containing both conditional variables a,b. The maximum weighted row is 36 for V, 18 for S, yielding

    q_fibre(beta)<=36*tanh(beta).

The source conditional comparison and the original K0 source-local quasilocality were already proved in YMClayOriginalWilsonR445F19ConditionalMarkedFibreSpatialBound20261122.md and YMClayOriginalR445CoarseWilsonActionLogSpatialQuasilocal20261122.md. This new step is **COARSE conditional contraction**, not another source covariance telescope.

## New exact simultaneous overlap budget, source geometry rather than generic counting

Let i run through the actual 64 coarse first original positive links U0_i, and define the original affected six-plaquette set P_i. For a genuine conditional fibre variable a define

    n_i(a) = # { original positive plaquettes p in P_i with a in p after R445 }.

For i,j distinct define m_ij=#(P_i intersect P_j). Original even-origin geometry gives, for EVERY i:

    sum_a n_i(a)=6*4=24,
    # {a:n_i(a)>0}=19,
    n_i(V_i)=6, eighteen other n_i(a)=1,
    sum_(j≠i) m_ij=3.

In fact m_ij=1 for exactly the THREE other original coarse first links at the same even site (other directions), and m_ij=0 otherwise. Thus **96 of the 2016 unordered coarse pairs have one directly shared original plaquette**. Previous original coarse log K0 covariance-only proof was correctly restricted to the other 1920 pairs, where m_ij=0.

Most importantly, summing over ALL coarse sources i, at EACH fixed conditional variable a gives the EXACT stronger overlap bound:

    max_a sum_i n_i(a)=12.
    sum_i n_i(a)=12 for each of 64 fibre variables V;
    sum_i n_i(a) in {0,1,3} for each spectator S.

On original L4: fibre: 64 at 12; spectator: 512 at 0, 192 at 1, 192 at 3. On separately enumerated even-origin L6 extension: 324 fibre at 12; 2592 spectator at 0, 972 at 1, 972 at 3. These identities are local even-parity face counts, not finite-box extrapolation from a fake interaction graph. The L6 construction is a geometry reference, not a separately Agda kernel-accepted variable-cutoff R445 theorem. Both L4 and L6 preserve ALL original positive plaquettes and interacting spectator variables.

## Rigorous new all-pairs coarse mixed logarithmic source bound, including the direct term

For arbitrary endpoint changes of TWO coarse original holonomies W_i and W_j, define the four ACTUAL original conditional logarithmic Wilson integrands H_00, H_10, H_01, H_11 on THE SAME (V,S) original Haar carrier. **Do not assume** that their mixed difference is zero: if i,j share a source plaquette there is a nonzero direct Wilson mixed term

    J_ij(V,S)=H11-H10-H01+H00,
    |J_ij(V,S)| <=4*beta*m_ij.

Use the genuine bilinear interpolation of these four original source actions:

    H_uv=(1-u)(1-v)H00+u(1-v)H10+(1-u)v H01+uv H11,
    K_uv = integral exp(H_uv) dH(V,S),     0<=u,v<=1.

At four corners K_uv equals the four **actual original induced K0** endpoint values. For each original plaquette, the source trace in H_uv is a convex combination of its four original normalized SU(N) trace expressions in [-1,1]. Therefore EVERY interpolated positive conditional Haar law has the SAME original Wilson four-variable face supports and Dobrushin upper matrix C_ab<=m_ab*tanh(beta). Its row sum remains <=q_fibre. No invented RG measure or independent polymer activity is introduced.

The exact mixed-source identity (ordinary derivative under finite compact Haar integral) is

    partial_u partial_v log K_uv
       = E_(mu_uv)[J_ij] + Cov_(mu_uv)(partial_u H_uv, partial_v H_uv).

This is the direct-inherited Hessian PLUS first-source-score covariance; omitting either is wrong. The source score variations are bounded at each of the true 960 conditional variables:

    osc_a(partial_u H_uv) <=4 beta n_i(a),
    osc_b(partial_v H_uv) <=4 beta n_j(b).

Let D=(I-C)^(-1)=sum_k C^k, nonnegative, with all row sums <=1/(1-q_fibre). By classical Dobrushin–Föllmer covariance comparison (conservatively use prefactor one rather than the standard possible 1/4), the ACTUAL coarse log K0 four-corner contrast obeys

    |Delta_i Delta_j log K0(W)|
      <= 4 beta m_ij
         +16 beta^2 sum_(a,b) n_i(a) D_ab n_j(b),

uniformly in all fixed exterior W and all SU(N) ranks under the normalized real trace convention.

Now sum this UPPER BOUND over EVERY OTHER coarse index j, not only the 1920 face-disjoint pairs. Use

    sum_(j≠i) m_ij=3,
    sum_a n_i(a)=24,
    max_b sum_j n_j(b)=12,
    sup_a sum_b D_ab <=1/(1-q_fibre).

It follows that

    sum_(j≠i) sup_(all coarse exterior and endpoints)
           |Delta_i Delta_j log K0|
      <= 12 beta + (16 beta^2)(24)(12)/(1-q_fibre)
      = 12 beta + 4608 beta^2/(1-q_fibre).

**From actual coarse log K0 to true coarse single-W specification:** Since the exact original Haar reparametrization makes product Haar the reference measure on W, the actual conditional law of one coarse W_i given W_others has density proportional to K0(W). Varying only W_j, its log-density contrast as a function of W_i has oscillation bounded by the left-hand sup over W_i endpoints above. The general sharp positive exponential-tilt TV estimate c_ij^coarse<=tanh(osc/4)<=osc/4 gives

    q_coarse(beta) := sup_i sum_(j≠i) c_ij^coarse
       <= 3 beta + 1152 beta^2/(1-q_fibre(beta))
       <= 3 beta + 1152 beta^2/(1-36 tanh(beta)).

The second denominator is positive whenever 36 tanh(beta)<1. At the explicit exact rational source regime

    0<= beta <=1/72,

the original conditional fibre satisfies q_fibre<=36 beta<=1/2 and the ACTUAL coarse Wilson marginal satisfies

    q_coarse <=3/72 + 1152/(72^2*(1/2))
             =1/24+4/9=35/72<1/2<1.

Thus **BOTH the original fixed-W continuous Haar fibre and the original induced 64-variable coarse compact-Haar specification contract simultaneously at the first true R445 step**, with constants uniform in original source coarse external W values and (for even-origin L>=4 native-extension geometry) original finite volume and compact SU(N) rank. No hidden new coarse bare-Wilson action is assumed.

Important: this proves classical finite Dobrushin contraction on the actual coarse marginal; it does NOT certify a renormalized CMP119/122 E/R/B/V polymer expansion, source-dependent *two-affine-marked* coarse Dobrushin coefficient, W1 normalized cluster-log identity, or absolute W3 rooted charges. The prior original fine marked W1 decay and fixed-W affine marked conditional estimates remain valid in their separately stated coupling windows but are not silently promoted to the newly proved coarse **unmarked** q.

## Independent source-exact local acceptance and strict negative control

Locally executed Python 3/SymPy 1.14, detailed reference
    scripts/check_ym_original_r445_coarse_dobrushin_twoscale_20261122.py
(working copy /mnt/data/check_ym_original_r445_coarse_dobrushin_twoscale_20261122.py), and committed concise geometry/SymPy checker
    scripts/check_ym_original_r445_twolevel_coarse_dobrushin_20261122.py
(this shorter committed checker was ALSO EXECUTED LOCALLY BYTE-FOR-BYTE; git blob e2760d2ba26682cc2378dad775ff7710977d30bd matched the exact locally executed file).
Both report exact original L4 and native-style even-origin L6 incidence checks, with all 1536 / 7776 original positive Wilson plaquettes retained:
L4: 1024 links, 1536 source faces, 64 coarse W, 960 conditional variables, 18432 directed weighted conditional face edges. Source first-link count per face: 1248 containing 0, 192 containing 1, 96 containing 2 selected first links. Sum-over-coarse overlap histogram: fibre (12):64; spectators (0):512, (1):192, (3):192.
L6: 5184 links, 7776 source faces, 324 native-style even-origin W, 4860 conditional variables, 93312 weighted directed edges. Selected first-link count per face: 6318 (0), 972 (1), 486 (2). Overlap histogram: fibre (12):324, spectators (0):2592, (1):972, (3):972.
Exact Fraction q_fibre(1/72) upper=1/2, q_coarse upper=35/72, and sharp source summation -> coarse row bound PASS.
Independent symbolic negative control: take H_uv=lambda*u*v, so K_uv=2 exp(lambda*u*v). Then conditional source score covariance=0 identically, but the coarse log four-corner contrast and inherited direct mixed Hessian both equal lambda. This falsifies the common but incorrect covariance-only derivation for the 96 direct-overlap pairs.

These checks certify geometry, algebra and the theorem's numerical coefficients. The full compact SU(N) Haar implication comes from the analytic trace-range/exponential-tilt bounds and established Dobrushin–Föllmer covariance comparison, NOT full Haar numerical sampling. No Agda-kernel proof or GitHub CI is claimed.

## TOE inheritance and hard physical max-cut

TOE #1281 is an R559 normalizing RG/stress/Casimir consumer; #1291 retains the independent H05 8-vertex/12-map/6-commuting-face C3/ternary zero-aware provenance; #1217 universal/internal C3 physical realization is conjectural. The Wilson coarse R445 64-block lattice incidence, spatial C3 and time-mirror bond SUPPORT permutations furnish a legitimate source-side TOE geometry check, not a same-H gauge/TOE identification. Any C3 or time mirror generally changes coarse W, so no fixed-W physical positivity follows.

**All results are strong-coupling only.** Actual YM continuum beta(a)->infinity fails q_fibre<1, and the source-derived q_coarse sufficient condition fails too. Actual CMP119/122 selected renormalized E/R/B/V with scale-dependent small/large-field decomposition, globally unique marked 1/F/G/FG two-J, inherited mixed Hessian, first-source score covariance, and termwise ABSOLUTE CMP116/W1-W3 physical rooted shell at uniform SI physical separation are open. Original E1 interacting R4 OS, all-cutoff D1, same-H dense D2, N1 and G1 remain OPEN. The exact next max cut is source-derived **weak-coupling** physical-block marked activity and a cutoff-independent physical rate, not further finite-bare-link source algebra.

Attribution: original Wilson/compact Haar, classic Dobrushin one-site comparison and Föllmer covariance theorem, original Bałaban CMP109/116/119/122, previously source-written DASHI R445/F19 native geometry, original source W1 and TOE owner priority. No duplicate prior theorem invention.
