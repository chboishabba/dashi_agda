# Clay YM BIDI: site-reflection chessboard cut for sparse original Wilson defects

2026-11-19. Same original SU(2) periodic Wilson product-Haar measure as
YMClaySU2OriginalWilsonUniformPlaquetteDeficit20261109.md and
YMClayOriginalWilsonCoherentConnectedPolymerPacking20261109.md.
Classical chessboard method: Froehlich, Israel, Lieb, Simon, CMP 62 (1978),
and Marek Biskup, arXiv:math-ph/0610025. No Higgs/KK prerequisite.

## Backward endpoint
Reuse YMClayOriginalOSDenseTestAutocorrelationGapCut20261109.md:
one common exponent on a dense nonvacuum test space of the SAME reconstructed
OS H suffices, even with test-dependent prefactors. No new spectral theorem.

## Original finite RP and dissemination cut
Take L=2^k >=4, V=L^4. At each site reflection plane and its opposite,
condition on tangential boundary links B. Each unit plaquette lies wholly
in one closed half or in B. Wilson action splits into a boundary-only part
and two reflected interior parts. Product Haar disintegrates accordingly.
Reflection fixes tangential B, and normalized real trace is invariant
under orientation reversal. Hence real half-supported F has
E[(Theta F)F]=Z^-1 integral exp(boundary action) I_F(B)^2 dH(B)>=0.
This proof concerns site planes on original fine links, not merely the
existing blocked all-word Gram. Need native proof of link/plaquette
partition, orientation and iterated CS dissemination with shared faces.

For unit 4-cube b define B_b(eps): at least one of its 24 plaquette faces
has deficit d_p>=eps, 0<eps<=2. It is reflection invariant under the
block reflections, and every plaquette belongs to exactly four cubes.
On all-block dissemination, sum_p d_p>=eps V/4.
Original partition lower bound Z>=exp(beta*6V-6V*C(beta)),
C(beta)=8+(2/3)ln24+ln beta, beta>=16, therefore gives
P(all blocks bad)<=exp(V*(6C-beta eps/4)).
Apply the classical chessboard estimate to distinct cubes to obtain
P(all specified cubes bad)<=q^n, q=min(1,exp(6C-beta eps/4)).
The analytic conclusion is conditional on the precise chessboard
applicability for the native closed-cube link algebras; no Agda proof
or independent execution claimed.

## Sparse link supports and mixed connected animals
Original six-staple deficit D6(l)=6-t(U_l S_l)>=6-R_l.
If R_l<r, 0<r<6, at least one of its six plaquettes has
d_p >= eps=(6-r)/6. If misaligned t(U_l V_l)<=0 and R_l>0,
D6>=6 so the same conclusion holds; including R_l=0 is harmless.
Thus every member of the union of frustrated and coherent-misaligned
bad links has an incident bad plaquette at threshold eps.

For n distinct marked links choose a witnessing plaquette per link:
at most 6^n assignments. Each plaquette witnesses at most four links,
so at least ceil(n/4) distinct plaquettes. Send each plaquette to the
unit cube anchored at its positive base site. At most six selected
plaquettes map to one base cube. Therefore at least ceil(n/24) distinct
bad cubes. Union bound:
P(all n marked links bad)<=6^n q^ceil(n/24)<=u^n,
u=6 q^(1/24). This is not an independence assumption.
Using the original endpoint-adjacency degree 14 and DFS animal count
196^(n-1), rooted connected bad-link animal of size >=m has probability
<=u*(196u)^(m-1)/(1-196u), when 196u<1.
Sufficient beta condition: beta eps/4 > 6 C(beta)+24 ln(1176).
For fixed eps and beta tending to infinity, holds eventually; along any
such path with lattice spacing a->0, a spanning rooted animal of physical
diameter R requires at least ceil(R/a) links (up to endpoint convention).
Thus the bound beats exp(-c R/a) once 196u<=exp(-c). Polynomial root
multiplicity in a fixed physical region can then be absorbed. This is
only the fixed-threshold defect event; no claim of all UV fluctuations,
shrinking-threshold estimates, or covariance decay.

## Next exact gates
1. Native site reflection partition and repeated Cauchy-Schwarz chessboard
dissemination on closed cubes. Audit all coordinate planes and periodic
dyadic tori, not just the selected side-four time Gram.
2. Prove the 24-face / four-cube incidence and link-witness assignment in
the existing YMClayD1OriginalPlaquetteSupportDecisionExact geometry.
3. Combine with the actual small-field selected RG/CMP116 marked-source
expansion: a covariance connection need not contain any fixed-threshold
bad link. Obtain controlled good-region propagator and mixed polymers;
track beta(a), renormalized physical scales and source moments.
4. E1/N1 interacting continuum, common dense OS autocorrelation exponent,
and G1 compact-simple extension remain independent endpoint gates.
No claim of Clay closure, physical decay, or kernel acceptance.
