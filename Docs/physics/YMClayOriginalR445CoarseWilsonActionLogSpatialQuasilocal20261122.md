# YM P0 — actual original R445 coarse effective log action quasilocality at strong coupling

Date: 22 November 2026. **NEW:** a genuine one-step original-Wilson COARSE-density spatial **mixed finite-difference** bound, source-derived without an independent coarse Gibbs action. This follows the source-native original F19 960-variable fixed-W fibre Dobrushin result in YMClayOriginalWilsonR445F19ConditionalMarkedFibreSpatialBound20261122.md. The result is restricted to strong bare coupling; not original beta(a)->infinity, CMP119/122 renormalized absolute W3, E1 continuum or D2 mass gap.

## Original source ownership, retained intact

On the actual periodic 4D side-four positive Wilson lattice, use the 1,024 original positive SU(N) links and all 1,536 original Wilson plaquette interactions with weight exp(beta sum_p ReTr U_p/N) under original product Haar. The source-derived native R445 construction owns exactly 64 even-site, two-consecutive-positive-link holonomies W_i=U0_i*U1_i, and 896 interacting spectator links. Exact original Haar change of variables U0_i=W_i*V_i^-1, U1_i=V_i gives the TRUE positive induced coarse density

    K0(W) = integral_[SU(N)^64 fibre V x SU(N)^896 S]
             exp(beta sum_original_p t_p(W,V,S)) dH(V) dH(S).

The irrelevant full-original Wilson additive constant exp(-beta*1536) has no effect on coarse differences. This is the existing real original F19 K0 source coefficient, not a new effective measure or independent activity choice. Its same-source 1/F/G/FG extension is already source-written. Agda kernel acceptance pending.

The true fixed-W conditional Wilson integrand is a **960-variable continuous product-Haar Gibbs law** with the original 1536 local plaquettes, each containing four DISTINCT variables, actual 64 fibre rows of degree 36 and 896 spectator rows of degree 18, multiplicity weighted. Classical Dobrushin comparison applies with q(beta)<=36*tanh(beta). For beta<=1/72, q<=1/2. This source theorem was derived in the immediately preceding companion audit; do not rebuild it as a generic polymer gas or separate coarse Wilson plaquette ansatz.

## One original blocked holonomy changes exactly six ORIGINAL plaquettes

Choose an original R445 coarse site/axis pair i, and hold all other W fixed. Compare two coarse holonomy values W_i^0,W_i^1. Only the FIRST original fine positive link U0_i=W_i V_i^-1 changes; U1_i=V_i and all spectator original fine links remain untouched. Thus the original full Wilson log-density changes by

    Delta_i(V,S)
       = beta sum_[p contains U0_i]
            [t_p(W_i^1,V,S) - t_p(W_i^0,V,S)].

The set of original affected plaquettes has EXACTLY six elements. Their conditional-variable support X_i is the union of the corresponding original four-link face variables: the same single fibre V_i plus its 18 original neighbouring conditional variables, hence |X_i|=19. With n_i(a) the number of these six source plaquettes containing conditional variable a, the exact original geometry gives n_i(V_i)=6, n_i(a)=1 at each of the other 18 variables, and sum_a n_i(a)=6*4=24. By normalized SU(N) real trace in [-1,1], the conditional-variable single-site oscillation obeys

    delta_a Delta_i <=4 beta n_i(a),
    sum_a delta_a Delta_i <=96 beta.

No new source mark or arbitrary coarse derivative is selected in this definition.

## Two original coarse holonomy changes: genuine induced action decay

Let i,j be TWO distinct original blocked holonomies, with choices W_i^0/1 and W_j^0/1, such that the original six-plaquette affected sets of U0_i and U0_j are **disjoint**. This is a precise source separation hypothesis: 96 nearby i,j pairs in the L4 original geometry violate it and require a separate local finite bound; they are excluded, not silently assumed distant.

For every conditional fibre configuration (V,S), the FOUR original source log weights obey the exact ADDITIVE mixed-difference identity

    H_11-H_10-H_01+H_00=0,

because no original plaquette contains BOTH changed first links. Define Delta_i=H_10-H_00, Delta_j=H_01-H_00, and exact real interpolation

    H_uv=H_00+u Delta_i+v Delta_j  for 0<=u,v<=1,
    Z_uv=integral exp(H_uv) dH(V,S).

At corners u,v=0/1, Z_uv equals the corresponding actual original Wilson induced K0(W) value. EVERY interpolated plaquette factor is an original finite convex combination of normalized SU(N) Wilson traces, hence remains in [-1,1] per original face. Its potential support is STILL the exact original 960-variable plaquette graph, so all intermediate true positive continuous SU(N) conditional Haar laws obey the SAME uniform classical Dobrushin row bound q<=36*tanh(beta).

Finite-difference/covariance identity, no surrogate:

    [log K0(W_i^1,W_j^1)-log K0(W_i^1,W_j^0)
     -log K0(W_i^0,W_j^1)+log K0(W_i^0,W_j^0)]
       = integral_0^1 integral_0^1
            Cov_(mu_uv)(Delta_i,Delta_j) du dv.

Let d_F19(i,j) be the genuine conditional 960-variable graph distance between the two 19-variable original source support sets X_i and X_j. The generic classical Dobrushin–Föllmer covariance estimate, combined with the exact site-oscillation sums, gives the conservative uniform source-bound

    |Delta_i Delta_j log K0(W)|
       <= (96 beta)^2 * q^d_F19(i,j)/(1-q),
    q=36*tanh(beta)<1.

A factor 1/4 available in common comparison normalizations has deliberately NOT been used: this inequality stays conservative regardless of the comparison convention. Since A0(W)=-log K0(W), its mixed finite-difference absolute value has the same bound. The estimate is UNIFORM over all fixed exterior coarse holonomies W_other, all SU(N) ranks under the normalized trace, and finite original Wilson volumes for which this same local pair/source geometry is defined. This establishes nontrivial first-R445-step COARSE ACTION QUASILOCALITY **within a strong-coupling Wilson regime**; it does not claim the coarse K0 is a finite-range bare Wilson or that its individual connected cluster expansion is bounded absolutely.

At beta<=1/72, use the fully rational overestimate q<=1/2 to get

    |Delta_i Delta_j log K0(W)| <= (32/9) * (1/2)^d_F19(i,j).

Thus for a truly separated pair with d_F19=3, the bound is <=4/9, and with larger separations it falls exponentially in conditional-graph hops. This is a mathematical statement for the actual compact SU(N) Haar integral by comparison, not a numerical SU(N) Haar calculation.

## Global affine marks: restricted, same-source extension

For the existing ORIGINAL globally unique real Wilson plaquette source M_st=(1+sF)(1+tG), two bounded real gauge-invariant plaquette marks F,G have disjoint original fine-link supports and |s|,|t|<=r=9/100. If in addition their original fine-link supports EXCLUDE the two changed FIRST fine links U0_i, U0_j, the source factors are independent of the contrasted external coarse holonomy coordinates and the exact four-corner interpolation above remains valid for K(W;s,t) with the unchanged local marked source terms.

The source-dependent interpolated positive conditional law has q_marked<=36*tanh(beta)+6r<=79/100 for beta<=1/144, as proved in the companion conditional note. Hence a conservative source-preserving extension is

    |Delta_i Delta_j log K(W;s,t)|
       <= (96 beta)^2 q_marked^d_F19/(1-q_marked).

This bound concerns **coarse-holonomy finite differences of the globally marked original log density**, NOT its twice-J differentiated source jet nor an independently labelled per-polymer mark. If either F or G contains one of the two changed first links, their source terms contribute additional endpoint-dependent mixed differences and this restricted proof does not apply without explicit accounting.

## Exact side-four local source validation and TOE geometry

Local executed Python 3/SymPy 1.14 file /mnt/data/check_ym_r445_original_coarse_log_spatial_20261122.py reuses the independently executed detailed original R445/F19 source graph checker, then audits:
- original native L4 1,024 Wilson positive links, 1,536 plaquettes, 64 native W pairs, 960 full interacting conditional variables;
- every first original selected link touches six original plaquettes; every affected face star contains exactly 19 distinct conditional variables, with weighted count one sixfold fibre variable plus 18 singly incident variables;
- of 64-choose-2=2,016 coarse-pair tests, EXACTLY 1,920 have disjoint affected six-plaquette sets and 96 are excluded near pairs;
- for the 1,920 disjoint affected sets, conditional source-star graph-distance histogram: d=0: 480, d=1: 800, d=2: 512, d=3: 128. They are **disjoint as affected PLAQUETTE SETS**, NOT necessarily disjoint conditional-variable supports (d=0 allowed).
- one original distance-three source pair witness is coarse pair ((0,0,0,0),0) versus ((2,2,2,2),0).
- strict site oscillation sum 96 beta, positive interpolated conditional Dobrushin q<=36*tanh(beta), rational beta<=1/72 => q<=1/2 and source mixed log contrast bound <=4/9 at distance three;
- independent exact SymPy two-spin positive source Z(u,v) validates D_uv log Z = Cov of source perturbations and the four-corner logarithmic ratio identity. This is a **symbolic algebra regression**, NOT an original continuous SU(N) Haar quadrature.

Committed compact checker scripts/check_ym_original_r445_coarse_log_interaction_decay_20261122.py was GitHub-read-back; the separately locally executed full diagnostic is NOT asserted byte-identical. No Agda 2.9 kernel or GitHub CI.

## TOE reuse and exact open physical max cut

The actual 64 R445 pair label geometry, original six-plaquette source-star supports, 960-variable interaction graph and all C3/time-mirror SOURCE LABEL symmetries are compatible with TOE #1291's indexed geometry and #1281's normalized R559 source consumption; TOE #1217's physical realization edges remain conjectural/nonpromoting. Six H05 commuting cube faces are not the six original plaquette stars. Spacetime spatial C3 is not the internal gauge Cartan or universal 369 physical C3. For fixed coarse W, time mirror/C3 generally transport W as well; no same-W reflection-positivity claim.

The actual original weak-coupling beta(a)->infinity trajectory lies outside beta<=1/72; physical SI blocking, full CMP119/122 E/R/B/V renormalized marked activities, inherited mixed Hessian and first-score covariance, ABSOLUTE two-support CMP116/W3 termwise shell and large-field control remain untouched. The new theorem does not construct a normalized KP cluster gas or an interacting E1 continuum, same-H dense D2 gap, N1 or G1. No Clay promotion.

Attribution: Wilson/Haar; classical Dobrushin covariance comparison and Föllmer; original Bałaban CMP116/119/122; existing original R445/native Agda and global W1/F19 owners. New contribution is the genuine selected original source six-face finite-contrast interaction bound, not a general new Dobrushin theorem.
