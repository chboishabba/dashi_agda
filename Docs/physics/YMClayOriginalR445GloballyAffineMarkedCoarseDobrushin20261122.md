# YM P0 — actual original R445 globally affine-marked coarse Wilson Gibbs Dobrushin, exact rational certificate

Date 22 November 2026. **Proved as a mathematical application of existing compact-Haar and classical Dobrushin–Föllmer probability theory; locally exact source graph/regression accepted, Agda kernel not run.** This closes the explicitly selected TWO-global-affine-mark coarse contraction for one actual original L4 pair of closed Wilson plaquette marks. It is SMALL bare-beta only. Do not promote it to full CMP119/122 weak-coupling RG, physical absolute CMP116/W3, original E1/D2 or TOE equivalence.

## Same original full Gibbs/Haar source, not a surrogate measure

Work on the actual 4D periodic side-four original SU(N) positive-link Wilson action with N>=2, 1024 fine links, 1536 positive plaquette words and product compact Haar, real beta≥0. Use the pre-existing native even-origin R445 64 axial two-link products W_i=U0_i U1_i, with the full exact Haar change U0_i=W_i V_i^-1, U1_i=V_i and ALL 896 interacting spectator variables. Fix real globally UNIQUE affine two-source labels |s|,|t|≤r=9/100 on two normalized real gauge-invariant closed Wilson plaquettes:

    F = (1/N) ReTr U_(y-z face at site (0,0,0,0))
    G = (1/N) ReTr U_(y-z face at site (0,0,0,2)).

These fine-link supports are disjoint AND their supports among the 960 true conditional Haar variables (64 V and 896 S) are eight distinct variables, four each. The marks are NOT independent per-polymer insertions or an arbitrarily chosen abstract spin system. For every coarse W and real source square, the ACTUAL induced coarse marked density is

    K(W;s,t) = ∫_{SU(N)^64 V × SU(N)^896 S}
                 exp(beta Σ_[all 1536 original p] t_p(W,V,S))
                 (1+sF(W,V,S))(1+tG(W,V,S)) dH(V,S).

Strict positivity follows from (1-r)^2>0, so the original marked induced COARSE Gibbs law has reference product Haar on the 64 coarse W coordinates. The source's F19 four columns K0,KF,KG,KFG are exactly the affine coefficients of this K, and the inherited mixed action Hessian and first-source-score covariance remain distinct downstream.

## Exact native marked source influence matrix, sharper than generic 6r

At fixed W the original face map gives 960 independent conditional SU(N) Haar variables, with four different conditional variables per original face. Define the positive symmetric multiplicity matrix M_ab counting original plaquettes containing both conditional variables a,b (a≠b). It has weighted row 36 for each V, 18 for each S, and total 18432 directed weighted source incidences.

Let T_ab count the two selected marked plaquettes containing both conditional variables. Their eight conditional supports are disjoint, hence every T row sum is at most THREE, not six. For any one changed conditional variable b in the actual positive Gibbs specification at a, log-density-difference oscillation is bounded by 4 beta M_ab + 4 atanh(r) T_ab; the classical sharp exponential-tilt TV lemma and tanh subadditivity give

    C_ab^fibre ≤ M_ab tanh(beta) + T_ab r
                ≤ M_ab beta + T_ab r.

On 0≤beta≤1/144, maximum row ≤ 36/144+3(9/100)=13/25<1. This is the SAME original interacting source at every fixed coarse W, not the prior conservative global-marked q_f≤79/100 needed when the two marks can share a single conditional V.

## Two arbitrary coarse W contrasts: retain direct Hessian PLUS covariance

For original coarse coordinates i≠j, consider their arbitrary four endpoint choices and actual four source log-weights H00,H10,H01,H11 on the SAME 960-variable Haar carrier. Interpolate by the literal convex bilinear combination

    H_uv = (1-u)(1-v)H00+u(1-v)H10+(1-u)v H01+uv H11,  u,v∈[0,1].

Every original full Wilson plaquette remains a convex mixture of its four bounded source trace expressions, and each marked log(1+sF), log(1+tG) remains a convex mixture of its original four source corner functions. All conditional measures in this interpolation have exactly the source interaction matrix domination above. Write

    J_ij = ∂u∂v H_uv = H11-H10-H01+H00.

This is generally NONZERO for directly shared original plaquettes and also for a marked plaquette containing both changed first fine links. Original mixed log identity is

    ∂u∂v log ∫exp H_uv dH = E_uv[J_ij]
                         + Cov_uv(∂u H_uv,∂v H_uv).

Integration in u,v yields the EXACT four-corner mixed finite difference of log K(W;s,t). In this selected source there are only three other first coarse links sharing an unmarked original six-plaquette star with each first link; for a coarse first link in one of the two selected marks there is at most one other coarse first link in that same mark. Denote m_ij the original shared-plaquette count, and t_ij the shared-MARKED-plaquette count; then

    |J_ij| ≤ 4 beta m_ij+4 atanh(r) t_ij.

Define original nonnegative incidence n_i(a)=# of the SIX original plaquettes containing selected first fine link i and conditional variable a. Each n_i is supported on 19 variables and Σ_a n_i(a)=24; exact full source maxima satisfy max_a Σ_i n_i(a)=12. Let h_i(a)=# of the TWO actual source-marked plaquettes containing both first coarse link i and conditional variable a. For the chosen two marks, h_i has FOUR ones for exactly four coarse i and zero otherwise. Let a_r=atanh(r) and source score bound vector

    v_i(a)=beta*n_i(a)+a_r*h_i(a).

Then osc_a(∂u H_uv)≤4v_i(a), and similarly in j. Apply the classical Dobrushin–Föllmer covariance comparison on the TRUE original positive conditional Haar Gibbs law, retaining a conservative covariance prefactor ONE (rather than the sharper 1/4). With D=(I-C)^-1 and source matrix C_ab≤beta*M_ab+r*T_ab, exact coarse conditional influence obeys

    c_ij^coarse ≤ beta*m_ij + a_r*t_ij + 4 v_i^T D v_j.

This is valid for ALL coarse pairs, including the 96 original direct shared-face pairs, for arbitrary coarse holonomy endpoint choices and for ALL real s,t in the source square. The actual single-coarse-W conditional is a positive density relative to compact SU(N) Haar, so taking the supremum of its log-density oscillation and applying the exponential tilt TV bound produces precisely this Dobrushin row estimate. No new coarse Wilson nearest-neighbour action is assumed.

## Exact RATIONAL 64-row certification, rigorous tail

Let beta*=1/144, r=9/100. The elementary series bound atanh(r)≤r/(1-r²)<91/1000 permits the rational replacement a*=91/1000. Monotone nonnegative upper data

    C*=beta* M+r*T,
    v_i*=beta* n_i+a* h_i,
    B*=Σ_(all 64 coarse j) v_j*,

dominate every real-source interpolation. The EXACT original 960×960 C* graph has maximum row 13/25. To avoid huge rational matrix inversion and certify every original coarse row, expand

    D* B* = Σ_(k=0..15) (C*)^k B* + Tail,
    0≤Tail_a≤(13/25)^16/(1-13/25) max_b B*_b.

Use D* v_i*≥v_i* componentwise to bound

    Σ_(j≠i) v_i*^T D* v_j*
      =v_i*^T D*(B*-v_i*)
      ≤v_i*^T (D*B*-v_i*).

Hence the COMPLETE coarse marked Dobrushin row has the explicit rational upper bound

    q_i≤ beta* Σ_(j≠i)m_ij + a* Σ_(j≠i)t_ij
        +4 v_i*^T [Σ_(k=0..15)(C*)^k B* - v_i*]
        +4 (Σ_a v_i*(a)) (max_b B*_b) (13/25)^16/(1-13/25).

ALL 64 source rows and the Neumann remainder are computed in exact Python integer and Fraction arithmetic with common denominator 18000, NOT floating-only. The largest resulting rational row is approximately 0.5320605746074196; the exact comparison proves

    BOX: q_coarse,marked < 11/20 = 0.55 < 1

uniformly for beta≤1/144, real |s|,|t|≤9/100 and ALL coarse holonomy exterior choices. The new result is an actual original first R445 coarse marked Gibbs Dobrushin contraction; this is strictly beyond the previous unmarked q_coarse≤35/72 and the conditional marked F19 Hessian alone.

The original negative control H_uv=lambda*u*v, log K_uv=lambda*u*v+constant, has nonzero intrinsic mixed Hessian with no score covariance: dropping E[J_ij] would be false for original direct shared-face pairs, and also for source-mark overlap pairs. This regression rejects that omission.

## Local acceptance / attribution / theorem boundaries

Executed locally in Python 3 and SymPy 1.14:
    scripts/check_ym_original_r445_global_marked_coarse_dobrushin_20261122.py
with full original 1024/1536/64/960 source graph; all 64 rational coarse rows, exact 16-step bound, analytic source potential trigonometric inequality, nonzero direct Hessian control PASS. Its Git blob 55423f251f130c6bdaf7f699d4b34fa218d555b6 was read back and byte-matched against the exact local executed source. The numerical presentation 0.5320605746 is ONLY a decimal visualization of an exact rational certified bound.

This fixed L4 two-plaquette arrangement is the chosen original globally affine source, not a theorem for all pairs of differently placed Wilson loops or every possible relative marked support geometry. Translating/rotating configurations under already-established original symmetries may be possible, but is not claimed as an Agda physical-source theorem. The unmarked original 64-coarse-variable theorem and the full F19 marked within-fibre theorem remain distinct already-owned results. No Agda kernel/CI was run.

**Physical endpoint remains OPEN:** The cutoff β(a) for 4D SU(N) continuum theory increases and violates beta≤1/144; this source result is insufficient for weak-coupling CMP119/122 renormalized E/R/B/V marked physical interactions, source-normalized W1 KP-log identity, termwise ABSOLUTE CMP116/W3 connected cluster shell and rooted entropy, fixed physical SI distance/rate, full E1 interacting OS, D1, same-H D2, N1, G1. The TOE #1281 R559, #1291 H05 eight vertices/twelve maps/six faces and zero-aware signed-ternary fibres, and #1217 C3 realization are normalizing/indexed provenance consumers only, not new physical proof authorities. Preserve original compact Wilson/Haar; classical Dobrushin/Föllmer comparison; Bałaban CMP116/119/122; original DASHI native R445/F19/W1 source ownership.
