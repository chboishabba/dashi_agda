# YM P0 — exact continuous SU(2) Haar original Wilson cube connected-tube coefficient

22 November 2026. Existing source owners: YMClaySUNVariablePeriodicGibbsGaugeExact, YMClayOriginalWilsonTwoPlaquetteMarkedSourceExact, YMClayOriginalWilsonAffineMarkedPartitionExact, YMClayOriginalWilsonFiniteHaarMarkedMayerPolymerW1W3NoGo20261122.md. STATUS: source-level finite local strong-coupling coefficient and exact original continuous Haar calculation, NOT cutoff-uniform clustering, true weak-coupling RG or an Agda kernel certificate. Do not build another finite labelled Mayer gas.

## Original full four-dimensional source and marks

Use the TRUE original periodic side-four four-dimensional SU2 Wilson Gibbs density

    dmu_beta(U) = Z_beta^-1 exp(beta * sum_{p in P} t(U_p)) prod_{ell in E} Haar(dU_ell),
    t(U)=ReTr(U)/2.

This has exactly 1024 positive link variables and 1536 plaquettes. A configuration-independent Wilson action shift exp(-beta*1536) cancels under normalization. Pick actual closed gauge-invariant original plaquette trace marks F at the yz face x=0,y=z=w=0 and G at x=1,y=z=w=0. They use disjoint original fine links. The same original affine Z(s,t) from the existing source has connected mixed log coefficient Cov_beta(F,G), not a different measure.

Exhaustive genuine 4D L4 original plaquette-word incidence against the eight marked boundary links gives:

    intersection with boundary: 0 => 1498 faces; 1 => 32; 2 => 4; 4 => 2.

The two 4-overlap plaquettes are exactly F,G; four 2-overlap plaquettes are the four side faces of the unit x/y/z cube; no other original plaquette shares more than one of F's four edges or more than one of G's four edges. Each of the twelve positive original links of the cube occurs in exactly two of its six oriented faces. The four side faces have mod-2 link boundary equal to the mod-2 sum F+G.

## Real continuous SU2 Haar, without centre/Q8 substitution

SU2 is the unit-quaternion S3, q=(q0,q1,q2,q3). Under its continuous normalized Haar,

    E(q_i)=0,    E(q_i q_j)=delta_ij/4.

Expand all six ACTUAL ordered original face trace characters in quaternion components (correct inverse signs for negative links). Each of the twelve cube links appears twice, so each integral uses only that exact second Haar moment. Contracting six integer rank-four face tensors along the twelve shared link indices gives integer 16384 and hence EXACTLY

    I_cube = integral_Haar(SU2^12) product_{six cube faces} t(U_f)
           = 16384 / 4^12
           = 1/1024.

This is a continuous SU2 integral, not a Haar quadrature on finite Q8 and not the Z2 centre. Independent check using SU2 characters: a_d(beta)=I_(d-1)(beta)-I_(d+1)(beta)=2d I_d(beta)/beta. The isolated six-face sphere partition has a convergent character expression sum_{d>=1} prod_f a_d(beta_f)/d^4. Its fundamental d=2 channel has a_2(beta)=beta/2+beta^3/24+..., so the six-face term is beta^6/1024 and a pair of distinct face-source derivatives yields beta^4/1024. The isolated-cube partition is ONLY an independent check of the local moment, not a replacement for the original full 1536-plaquette action.

## Full original Wilson local connected Taylor coefficient: source-level proof outline

Under product SU2 Haar, flipping any independently integrated original link U_ell -> -U_ell leaves Haar invariant and flips every fundamental trace in which that link appears once. Hence a moment of source marks and Wilson action insertions vanishes unless every original link appears an even number of times. Expand the entire full Wilson Boltzmann factor in beta about beta=0, with both F and G present, and subtract E_beta(F)*E_beta(G) to form the genuinely connected covariance.

For fewer than four action plaquettes there is no nontrivial connected centre-even surface bridging both closed mark boundaries: terms inserting marked F and marked G themselves factor into independent private-link moments and cancel in covariance. At fourth order, if neither marked face is selected as an action factor, covering all eight marked boundary links with four faces forces each face to cover two and thus forces exactly the four distinct side plaquettes. If only one of F,G is an action face, three others cannot cover the other mark's four private boundary edges. If both F and G are action faces, the remaining two must match the same original plaquette mask (or marked face repetitions), and these source expectations disconnect after Haar integration over unused private F/G links. Every original L4 plaquette has a distinct four-link mask. Therefore the FIRST connected nonzero term is exactly the unique four-side tube, with four distinct plaquette insertions cancelling the 4! expansion denominator.

The full finite ORIGINAL L4 continuous SU2 Wilson covariance has the source-local asymptotic

    Cov_beta(F,G) = beta^4 / 1024 + O(beta^5)  (beta -> 0+).

In particular, this specific full finite original Wilson gauge-invariant covariance is genuinely nonzero at sufficiently small positive bare beta. This last cumulant-cancellation argument is written mathematically and checked with boundary-incidence constraints; it has NOT been separately elaborated in the Agda kernel or exhaustively computed as a symbolic 1536-variable four-derivative expression. Do not promote it beyond source-level mathematics.

## Local receipt and precise boundary

Executed locally: an independently authored, more extensive script check_ym_original_su2_continuous_haar_cube_leading.py (Python/NumPy/opt_einsum/SymPy, no CI). A corresponding reproducible repository script is scripts/check_ym_original_su2_continuous_haar_cube_leading_20261122.py (commit 9c397044); its code was read back from the repository but its exact fetched bytes were not separately locally executed; do not claim byte-for-byte execution identity. The exact local reference verifies all 1024 original positive links and all 1536 periodic plaquette words; all 12 cube-link incidences; full boundary histogram; source 4-edge mask uniqueness; original SU2 quaternion multiplication tensor contraction 16384/4^12; independent SU2 modified-Bessel fundamental-character expansion and beta^4 coefficient. The code is a focused mathematical reference, not full SU2 product-Haar Monte Carlo, not cutoff-uniform physical weak-coupling data, and not a pinned Agda 2.9 receipt.

## Actual physical maximum cut unchanged

The continuum trajectory has beta(a) increasing as a->0, rather than beta->0. This finite ORIGINAL full Wilson nonzero local coefficient is not the original all-cutoff nontrivial continuum E1 observable, and it supplies NO source-uniform real CMP116/W1/W3 physical shell rate. Newly inspected YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact (on the SAME branch) ALREADY transports all four fine-original coefficients (1,F,G,FG) through the complete R445/F19 64-pair plus 896-spectator fibre, including the generally NONZERO within-fibre covariance c_W. Thus finite fine-mark transport is NO LONGER missing. Actual full-source work must now use that exact four-column F19 receiver inside the genuine CMP119/122 weak-coupling small/large-field renormalized marked activity and its actual global marked KP log jet, and pay cutoff-independent marked connected shell charge; OR prove full original good-conditioned-to-CMP116 response plus large-field tail at fixed physical distance. Then instantiate existing E1 physical limit/positive-time RP/OS, dense same-H D2 spectral exclusion, N1 continuum positive local norm and group-specific G1. The previously proved no-go for raw microscopic Mayer activity at beta>=16 still applies; this result does not evade it.

Attribution: Wilson lattice action, continuous compact SU2 Haar, standard quaternion and Peter-Weyl/strong-coupling expansions, Bałaban CMP116/119/122, Kotecky-Preiss/Fernandez-Procacci, Osterwalder-Seiler/Menotti-Pelissetto and existing DASHI original-source implementations. No proof of the Clay mass gap is claimed.
