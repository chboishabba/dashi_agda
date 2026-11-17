# YM.REAL max cut: dyadic Fourier pairing and all-cutoff Wilson cylinders
17 November 2026. Source-written on existing PR #1444. Mathematical proof
and exact rational execution; NOT an accepted Agda/Bishop/Clay theorem.

## Universal dyadic character pairing (without pi)

For N=2^s and 0<k<N write k=2^t u, u odd, and r=2^(s-t-1).
In Q[z]/(z^(N/2)+1), z^(kr)=(z^(N/2))^u=-1.
Partition j=0,...,N-1 into 2^t blocks each of length 2r; pair
j=b*2r+h with j+r, 0<=h<r. Their character values cancel EXACTLY.
Therefore sum_(j<N) z^(kj)=0 for all nontrivial dyadic frequencies,
and the trivial frequency has sum N. This is an arbitrary-s proof by
factorization and a constructive involutive pairing, NOT extrapolation
from finite tests.

- scripts/check_ym_dyadic_character_bitpair_20261117.py checks actual
  polynomial representatives modulo z^(N/2)+1, not just residues.
  It passed 698027 exact pair cancellations through N=1024.
- YMClayDyadicCharacterPairCancellationExact.agda proves by structural
  induction cancellation of an arbitrary list of adjacent opposite
  terms, and its shifted-phase version using the source phase identity.
  This isolated safe theorem is imported by BalabanRGTOERegression and
  included in the pinned local acceptance script.
- Still open in Agda: prove the primitive Bishop dyadic phase law and
  reindex the original Fin N enumeration into these adjacent pairs.
  Supply positive ordered Bishop half-angle nodes and the product
  cubature moments. No root-finding or classical Machin pi required.

## Universal original six-plane cubic Wilson moments

At L=1 the genuine original plaquettes are link commutators:
H(D)=9/2, H(D^2)=187/8, H(D^3)=6445/48.
At every L>=2, with P=6L^4, prove no three distinct positive
plaquettes have mod-2 boundary XOR zero. Three four-edge boundaries
with XOR zero would require all three pairs to share exactly two
edges. Distinct coordinate planes share <=1 edge. Same-plane
different plaquettes at L>=3 share <=1 edge. For L=2, a pair
shares two edges precisely when the base sites differ along exactly
one in-plane axis. These possible pairs form a four-cycle C4 for
each plane and fixed perpendicular site; no three can pairwise share
two edges. Hence the mod-2 three-plaquette boundary is nonzero.
The original independent-link center-sign involution annihilates
all three-distinct trace products. Therefore mathematically,
for ALL L>=2:
  H(D)=P, H(D^2)=P^2+P/4, H(D^3)=P^3+3P^2/4.
The native all-L Fin torus geometry proof is still open in Agda.

## Strict rational Z enclosure for every finite original cutoff

For rational beta>=0, let B=12 beta L^4 and mu_k=H(D^k).
From T3(beta D)<=exp(-beta D)<=T2(beta D) and e<4,
  max(4^(-ceil B),1-beta mu1+beta^2 mu2/2-beta^3 mu3/6)
  <= Z_L(beta) <=
  min(1,1-beta mu1+beta^2 mu2/2).
The lower bound is strictly positive EVEN WHEN T3<0.
New script check_ym_wilson_all_cutoffs_interval_20261117.py is
exact-rational, uses no simulation, and was run for L=1,2,3,4,10,25.
The argument presupposes the proved mathematical positive one-link
moment functional, NOT a completed Agda original SUN Haar instance.

## A false cross-cutoff target removed

Naive link-selection L=2 -> L=1 at fixed beta is NOT projectively
consistent for interacting Wilson Gibbs measures. Retain the four
positive origin links and test f=ReTr([U0,U1])/2:
both free-Haar expectations are H(f)=1/4, but the first Gibbs
derivative at beta=0 is +25/48 at L=1 and 0 for the L=2 projection.
At L=1, H(fT)=1/3+4/8+1/16=43/48, so Cov(f,D)=-25/48.
At L=2 every original plaquette uses >=2 unselected links, each
having an odd center-sign effect on H(f*t_p), hence all vanish.
scripts/check_ym_naive_cylinder_negative_control_20261117.py
passed 198 exact incidence/rational assertions. This ONLY rules out
this particular naive link-deletion map. A correct RG blocking map
with induced effective action is a separate positive research target.

## Honest remaining gates

All-degree Fourier: mathematical proof and safe finite cancellation
leaf; actual Bishop primitive root and all-degree producer OPEN.
Effective b_n: exact rational concentration and tested Cauchy schedule;
native Bishop inequalities/polynomials OPEN.
Bishop Haar: mathematical completed positive functional from density;
native setoid/Cauchy proof producer OPEN.
SU(2): exact matrix identities and original rational-to-Bishop source
candidates; pinned kernel and full SUN identification OPEN.
Wilson: all-L rational Z enclosure and original gauge trace algebra;
typed Bishop product Haar and real RG cylinder source OPEN.

Attribution: Fejer, Stroud, Pizzetti/Folland, Bishop/Bridges,
Murray/Csimma, Wilson/Balaban and original DASHI theorem owners.
No ESD modifications and no claim of YM.REAL / Clay closure.
