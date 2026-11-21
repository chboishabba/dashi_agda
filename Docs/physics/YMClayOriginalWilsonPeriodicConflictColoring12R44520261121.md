# P0 D1 — original Wilson 12/8-color plaquette-conflict packing and native R445 compatibility

Date: 2026-11-21. **Mathematical finite-lattice improvement** over the 19-greedy packing in [YMClayOriginalWilsonCoherentConnectedPolymerPacking20261109.md](YMClayOriginalWilsonCoherentConnectedPolymerPacking20261109.md). Original source: four-dimensional periodic SU(2) Wilson Gibbs measure, its authentic Haar single-link conditional law and coherent-staple estimate. This does **not** establish the frustrated-staple connected-contour estimate, CMP116 full small/large physical record, continuum limit or Clay gap.

## Concrete exact graph, without changing the Wilson source

For any L>=3 let E_L=(Z/LZ)^4 x {0,1,2,3} be the set of positive oriented original Wilson links. A plaquette indexed by x and mu<nu contains exactly these **positive-link variables**, with orientation signs in the holonomy immaterial to the conflict relation:

```
(mu,x), (nu,x), (mu,x+e_nu), (nu,x+e_mu).
```

Two links conflict iff they occur in a common original plaquette. Prior source gave degree <=18 and therefore a greedy independent-set extraction |T|>=ceil(|S|/19).

**Stronger uniform 12-coloring:** For odd L, define c_L(j)=j mod 2 for 0<=j<L-1, and c_L(L-1)=2. This is a proper 3-coloring of the cyclic coordinate graph C_L: consecutive coordinates have different colors, including the wrap (L-1)->0. For even L take c_L(j)=j mod 2, a proper 2-coloring. Put k(L)=3 for odd L and 2 for even L. Color a positively oriented link (mu,x) by

```
color_L(mu,x) = (mu, (sum_{nu != mu} c_L(x_nu)) mod k(L)).
```

There are 4k(L) colors: 12 for all odd L, 8 for all even L. Every original plaquette has four **pairwise distinct colors**. Links of distinct mu have distinct first coordinates. The two mu-links differ by one step in a **transverse** nu-coordinate, which changes c_L mod k(L); the same holds with mu/nu exchanged. Thus each color class contains no two links belonging to any common plaquette. This is an all-L proof, not inference from finite enumeration.

For every finite set S of *distinct* original links, the largest color class T = S intersect color^{-1}(a) satisfies

```
|T| >= ceil(|S| / (4*k(L))) >= ceil(|S|/12).
```

The even-L bound is ceil(|S|/8). This source-native deterministic coloring replaces, not assumes, the older degree-18 greedy extraction; it creates no new probability measure.

## Actual original SU(2) Wilson conditional factorization

For an arbitrary color class T, every Wilson plaquette contains at most one T-link. Conditional on **all** original links in E_L\T, the exact original Wilson action is a sum of one-link terms in the T-links. Haar factorization therefore gives the **actual normalized product of original one-link conditional laws**, with no independence assumption on unfrozen links. Because the six staples for a T-link avoid every other T-link, the coherent-staple events A_l(r) and directions V_l are measurable in the conditioned complement.

Reuse the existing source one-link bound, with 0<r<=6 and beta>0,

```
q_(beta,r) = min(1, 3 exp(-beta*r/2)),
P(B_l | E_L\T) 1_{A_l(r)} <= q_(beta,r) 1_{A_l(r)}.
```

If all links in S are coherent-and-misaligned, in particular all links of T are. Conditioning then yields the genuinely original Gibbs bound

```
P_{mu_beta}( intersection_{l in S} (B_l and A_l(r)) )
  <= q_(beta,r)^ceil(|S|/kappa_L),
kappa_L = 8 (L even), 12 (L odd).
```

This improves exponent 1/19 to 1/12 *uniformly* over all original changing cutoffs L>=3; for even L, to 1/8.

## New two-channel mixed-contour inequality: adaptive coherent-class selection (no binomial entropy)

Let S be **any fixed original set of n distinct positive Wilson links**, let B_l be the original one-link misalignment event, A_l(r)={R_l>=r} the coherent-staple event, and let N_fru(S)=sum_{l in S} 1_{R_l<r}. For every integer 0<=h<=n and K=4*k(L) (=8 for even L and 12 for odd L), set m=ceil((n-h)/K). On the **original fully interacting Wilson probability law**:

```
P_mu( all_{l in S} B_l )
  <= P_mu( N_fru(S)>h ) + K*q_(beta,r)^ceil((n-h)/K).
```

**Proof from the exact same Wilson conditional, no new independent-link assumption.** Fix the K geometric color classes S_i; their partition is deterministic, not data-dependent. If N_fru(S)<=h, at least n-h links are coherent, so at least one class S_i contains >=m coherent links. Let C_i be that class-coherence-count event. Each R_l and A_l(r) for l in S_i depend only on links *outside S_i*, because there are no plaquettes containing two S_i-links. Hence C_i is measurable when conditioning on all outside bonds. The original full Wilson conditional of the S_i bonds is a product of authentic one-link Haar Gibbs laws. On C_i, all-B occurrence in S_i has conditional probability at most q_(beta,r)^(number of coherent links in S_i) <= q_(beta,r)^m, while the unconstrained frustrated links contribute factors <=1. Union over the **K fixed classes**, not over choose(n,h) coherent subsets:

```
{all B in S} intersect {N_fru(S)<=h}
  subset union_{i=1}^K ( C_i intersect {all B in S_i} ).
```

Integrate these conditional bounds and add P(N_fru>h). The factor is K (8/12), **not the binomial coefficient choose(n,h)**. This is a valid bridge for arbitrarily mixed coherent/frustrated original Wilson contours; the original coherent-only bound above is sharper when all of S is known coherent, so keep both lemmas.

**Revised minimal physical input D1-FRU-01b:** an original-source *fixed-contour sparse-frustration count tail*, e.g. for a selected fraction 0<theta<1

```
P_mu(N_fru(S)>floor(theta*|S|)) <= C_f * rho_f^|S|
```

with C_f and rho_f independent of original UV cutoff, volume and contour, and quantitative rates strong enough to beat the existing rooted-animal growth of 196. Then the exact mixed-contour inequality provides an all-B connected-animal tail as soon as both 196*rho_f<1 and 196*q_(beta,r)^((1-theta)/K)<1 (with finite rounding handled explicitly). This is an IF/THEN statement: the **fixed-contour sparse-frustration probability bound has not been proved**. In particular, original extensive-density pressure estimates cannot be substituted. Nor is an all-B misalignment contour *itself* yet the actual marked W1/W3 covariance cluster weight or a full Gibbs small/large decomposition; both source identities remain open.

The local exact-rational test additionally checks adaptive coherent-class extraction across 100 random marked-set sizes for L=3,4,5,6, with frustration patterns and exact q-power monotonicity. The mathematical proof above applies to arbitrary finite L>=3 and arbitrary S, and reuses the original Wilson source one-link conditional.

## Connected coherent-bad animals: rate and explicit threshold

The original endpoint-adjacency degree <=14 and root-animal count <=14^{2(n-1)} = 196^{n-1} are unchanged. Put kappa=kappa_L, a_kappa=196*q_(beta,r)^(1/kappa). When a_kappa<1,

```
P(exists connected coherent-and-misaligned S containing root,
  |S|>=m)
  <= (q_(beta,r)^(1/kappa) / (1-a_kappa)) * a_kappa^(m-1).
```

A sufficient strict condition (beta*r > 0 and q=3 exp(-beta*r/2)) is

```
beta*r > 2*(kappa*log(196) + log(3)).
```

Numerically: for kappa=19 (old): 202.76558; kappa=12 (all L): 128.87198; kappa=8 (even L): 86.64706. This is a **bare beta-r threshold for the coherent-only contour**, not a physical-units clustering rate, an original full Gibbs large-field bound, or a UV/IR Wilson continuum theorem. The entropy factor 196 was not improved; only independent-set extraction was.

## BIDI into original R445/E1/F19 selected source

For original n=3, L=4 side-four fine Wilson bonds, a native side-two coarse positive bond in orientation mu consists of two actual fine positive links beginning at x=2c and x+e_mu (c in (Z/2Z)^4). Both starts have zero transverse parity, so both links have color (mu,0). There are 16 coarse starts, 2 phases and 4 orientations: the original **128 selected fine bonds** occupy exactly four of the eight orientation-specific colors, 32 links each.

Hence all 32 selected original links in each one orientation are plaquette-disjoint, despite adjacent same-orientation two-link pairs. The 896 residual bonds remain **in the conditioning and in the original Wilson Gibbs weight**; no bare n=1 coarse replacement is made. Cross-orientation marked links are not independent, since they can share an original plaquette. The event and corresponding conditional estimate must still be matched to the **actual** R445/F19 coarse Wilson tests before W1/W3 source application. This geometry is a refinement of the original selection/conditional-factorization interface, not a replacement for D1's full-Wilson analytic hypotheses.

## Exact remaining P0 physical payment (unchanged)

1. **D1-FRU-01b:** source-derived probability/activity suppression for specific **sparse connected frustrated/mixed** original Wilson contours in a fixed physical-block metric. The coherent-only event above does not cover a path alternating coherent and frustrated links. Existing extensive frustrated-density pressure bounds cannot control a sparse path of O(L) defects in O(L^4) volume.
2. **D1-FRU-02 / W1/W3:** actual selected original CMP119/122/116 marked-J source dictionary, full Wilson small+large decomposition, nonvacuous admissible physical remote supports, absolute connected cluster charge and cutoff/volume-uniform q<1 in **physical** units. Reuse `YMClayD1OriginalFullWilsonSmallLargeFieldExact.OriginalSmallLargePhysicalSource` and `BalabanLiteralTwoWilsonCMP116ConnectingTailExact.TwoWilsonCMP116PhysicalShellPayment`; do not duplicate covariance or shell theorems.
3. **E1/D2/N1/G1:** original interacting continuum/OS, dense same-H nonvacuum spectral gap, noncollapse and every compact simple group remain open.

## Verification / trust

The companion `scripts/check_ym_original_wilson_periodic_conflict_coloring_20261121.py` was executed **locally** with SymPy. It exhaustively enumerated all original positive-link plaquette incidences for L=3,...,11, checked all four plaquette colors distinct and checked arbitrary sampled marked subsets/pigeonhole, proved exact-rational q-power improvements for n=1,...,249, and independently checked native n=3 side-four 128 selected links partition into four orientation classes (32 each) with all 896 spectators retained. The mathematical all-L proof is above. The regression is **not an Agda 2.9 kernel receipt** and does not test continuous Haar, original SU(2) Wilson probabilities or D1 physical estimates.

Attribution: original SU(2) Wilson Gibbs/Haar and prior one-link conditional/animal bound retain their original repository and literature owners; the explicit 4k periodic transverse-color packing and R445 geometry connection are a new finite combinatorial refinement. Do not present them as a completed 4D YM mass-gap or CMP116 physical-source proof.
