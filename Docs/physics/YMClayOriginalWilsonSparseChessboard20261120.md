# Original Wilson sparse UV deficit bound by site-reflection dissemination

20 November 2026. Analytic derivation using standard chessboard inequality (Fröhlich–Israel–Lieb–Simon; see M. Biskup, Reflection positivity and phase transitions in lattice spin models, arXiv:math-ph/0610025, Theorem 5.8). Original Wilson source and pressure donor: YMClaySU2OriginalWilsonUniformPlaquetteDeficit20261109.md. No new generic probability law. Scope: periodic SU(2), even side L>=4, beta>=16, microscopic lattice only. For the chessboard step use the standard even-torus site-plane theorem for closed cubes with shared boundary variables; if formalizing only dyadic dissemination, restrict L to powers of two. Not an Agda kernel receipt.

## Site-plane source positivity

Reflect in any coordinate site plane and its antipodal plane. The links lying in these two planes are shared boundary variables B. All other links split into disjoint positive/negative halves, exchanged by reflection (orientation reversal acts by group inverse). Each elementary plaquette is wholly on one closed half, or in the shared boundary. Thus the real Wilson trace action is S_B+S_++theta S_+; product Haar disintegrates into B and two independent half-products. For any bounded real half-observable f, integral of f theta(f) equals the positive boundary integral of the square of its unnormalized half integral, divided by the original partition. The analogous bilinear form is symmetric. This supplies coordinate site reflection positivity without a strong-coupling restriction. Closed unit-cube functions can depend on their shared face links. The standard chessboard inequality bounds E product of reflected block functions at distinct tiles by the product of their fully disseminated norms (each norm is the V-th root of the fully disseminated expectation, V=L^4). Reuse the repository's original Wilson RP owners for native formalization; this note gives the source factorization needed for all four directions.

## Reflected geometry, with multiplicities

Choose orientation i<j and one of four transverse parity shifts, giving 24 classes. A unit plaquette in the base unit cube has lower transverse coordinates 0. Reflecting into tile x sends each transverse coordinate k to x_k+(x_k mod 2), plus the chosen parity shift modulo L. In active directions its lower coordinate remains the tile coordinate (up to a translation of the origin). The resulting V tile marks contain V/4 distinct plaquettes, each exactly four times. Each plaquette in this class can be assigned a distinct tile (choose lower transverse faces). Do not use unreflected lower-corner translations as if they were reflection dissemination.

Write d_p=1-ReTr(U_p)/2, D=sum_p d_p, P=6V and C(beta)=8+(2/3)log24+log beta. Existing pressure cap gives Z>=exp(beta P-C P).

## Joint normalized energy moment

For a class containing m marked distinct plaquettes, disseminate f=exp(t beta d_p), 0<=t<=1/4. The fully disseminated product is exp(4t beta sum_{p in class} d_p). Since 4t<=1 and all deficits nonnegative, this cancels at most the selected original action penalty. Its expectation is at most exp(C P) by normalized product Haar mass one and the SAME partition lower bound. Chessboard therefore gives E exp(t beta sum_marked d_p)<=exp(6 C m). For an arbitrary set A of m plaquettes, apply Holder to the 24 classes, using t=24 theta. For 0<=theta<=1/96 this proves

E_beta exp(theta beta sum_{p in A} d_p) <= exp(C(beta) m/4).

No independent exterior conditioning or i.i.d. plaquette assumption. This quantitative joint moment costs log beta per mark, not a beta-independent K; it improves the compactness envelope and suffices for microscopic thresholds with beta epsilon >> log beta. Markov at theta=1/96 yields

P(all p in A have d_p>=epsilon) <= min(1, exp[-m (beta epsilon/96-C(beta)/4)]).

Denote its rate kappa. The same result follows directly by disseminating indicators and selecting the largest color class, when kappa>0.

## Sparse frustrated links and mixed microscopic contours

For any specified m distinct frustrated links R_l<r<6, existing D6>=6-R_l gives at least one incident plaquette with d_p>(6-r)/6. Choose one of six witnesses per link. Each plaquette touches four links, hence every witness assignment has >=ceil(m/4) distinct plaquettes. Union bound over <=6^m assignments gives P(all frustrated)<=min(1, exp[-m(kappa/4-log 6)]) when kappa>0, evaluated at epsilon=(6-r)/6. This is a sparse support estimate, not a density estimate.

For a specified mixed-bad set S of n links (each either frustrated or coherent-and-misaligned), union over partitions. For each partition at least n/2 links are of one type, so the probability for that assignment is <=exp[-n min(kappa/4-log6, -log q/19)/2] with q=min(1,3exp(-beta r/2)), when both rates positive. Thus P(all mixed bad)<=min(1, exp[-n (min(kappa/4-log6,-log q/19)/2-log2)]). The existing degree-14 connected-link animal count 196^(n-1) gives a summable rooted tail when the latter rate exceeds log196. No independence between the coherent and frustrated types used.

## Boundary and remaining work

This closes the analytic microscopic sparse-frustration reduction on the specified reflection-compatible original tori, using the standard chessboard theorem and the existing pressure proof; it does not construct the full renormalized blocked-energy moment or physical-scale CMP116 activity. The logarithmic prefactor is not a uniform exponential moment at fixed theta for beta-normalized fields; the bound does not pay physical-distance clustering, beta trajectory, IR crossover or E1/D2/N1/G1. Native formalization of closed-block chessboard and source incidence remains pending. Numerical regression checks reflected multiplicities, incidence and rate identities, not numerical Haar integration. Attribution: standard reflection-positive chessboard theorem and Wilson/Haar action; DASHI's contribution here is the explicit pressure/geometry/frustration composition.
