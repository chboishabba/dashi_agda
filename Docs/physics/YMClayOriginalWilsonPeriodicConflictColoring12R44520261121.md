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

with C_f and rho_f independent of original UV cutoff, volume and contour, and quantitative rates strong enough to beat the existing rooted-animal growth of 196. Then the exact mixed-contour inequality provides an all-B connected-animal tail as soon as both 196*rho_f<1 and 196*q_(beta,r)^((1-theta)/K)<1 (with finite rounding handled explicitly). This is an IF/THEN statement for the color-only argument. **Correction from the #1444 source audit:** the older original chessboard analyses of 19 and 20 November already give *conditional microscopic fixed-contour sparse-frustration* bounds from site-reflection RP, pressure and a verified applicability of the closed-cube chessboard inequality. They are not native Agda kernel proofs and not cutoff-uniform renormalized physical W3 clustering. The next payment is the original source RP/chessboard dictionary and physical-scale/W1/W3 transport, not invention of a first microscopic contour estimate. In particular, original extensive-density pressure estimates cannot be substituted. Nor is an all-B misalignment contour *itself* yet the actual marked W1/W3 covariance cluster weight or a full Gibbs small/large decomposition; both source identities remain open.

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

## Pre-existing stronger chessboard donor; precise comparison and attribution correction (21 November)

The further #1444 audit found source-owner documents that **predate** this new 12/8-color refinement:

- `Docs/physics/YMClayOriginalWilsonSparseChessboardBidi20261119.md`: original even periodic SU(2) Wilson source, site-plane reflection positivity (conditional native closed-cube dissemination), all-bad mixed-link plaquette witnesses and root-animal estimate. The bound for each fixed original S of n bad links is `P(all bad on S) <= u_cb^n`, `u_cb=6 exp(C(beta)/4-beta*epsilon/96)`, where `C(beta)=8+(2/3)log24+log beta`, `epsilon=(6-r)/6`. It uses the genuine Wilson partition pressure donor and **does not assume independent plaquettes**.
- `Docs/physics/YMClayOriginalWilsonSparseChessboard20261120.md`: a second original site-reflection/plaquette-dissemination derivation; at the same r and epsilon it has the weaker conservative rate `u_plaq=6 exp(C(beta)/16-beta*epsilon/384)`. Its microscopic sparse-frustrated and mixed contour bounds are already source-mathematical results **conditional on native chessboard applicability**.

Comparison is for their reported formulae, **not** claims of independently accepted native RP/chessboard or a physical full-covariance theorem. For r=3 (epsilon=1/2), the pre-existing direct cube witness reaches `196*u_cb<1` at beta approximately 2212.81, the second conservative plaquette moment route at beta approximately 6335.55. The *coherent-only* new color criterion requires beta*r>86.64706 for even L (or >128.87198 uniformly), i.e. beta>28.88 on even L when r=3, but that is a **different restricted event** and cannot be compared as a full bad-contour rate.

The new fixed-class adaptive mixed inequality is a complementary bridge, not an original discovery of sparse-frustration control. Where the 19–20 November 2026 chessboard estimates are applicable and strong, use that **pre-existing full-bad donor directly**. The action-level probability of fixed-threshold original bad-link contours is still not the CMP116 differentiable two-Wilson *cluster activity* or a bound in fixed **physical** units. To go from the strongest actual original microscopic Wilson source to D1's `OriginalSmallLargePhysicalSource`, certify (i) source site-reflection/closed-cube dissemination for its specific Wilson link algebra, (ii) any cross-scale/dyadic limit and running beta calibration, (iii) same-J small/large marked cluster decomposition/charge and (iv) common physical rate. Never mark the microscopic chessboard donor itself missing again.

**Primary mathematical attribution:** Osterwalder–Seiler Wilson lattice gauge positivity, Menotti–Pelissetto site-plane extension, standard reflection-positive chessboard estimate (Biskup), existing original pressure and #1444 Wilson sparse-contour compositions. DASHI's additional finite contribution here is explicit 12/8 plaquette conflict coloring, native R445 orientation-class identification and adaptive fixed-class two-channel inequality. No proof of the original 4D Clay existence/mass gap.

## Exact remaining P0 physical payment (unchanged)

1. **D1-FRU-01b:** source-derived probability/activity suppression for specific **sparse connected frustrated/mixed** original Wilson contours in a fixed physical-block metric. The coherent-only event above does not cover a path alternating coherent and frustrated links. Existing extensive frustrated-density pressure bounds cannot control a sparse path of O(L) defects in O(L^4) volume.
2. **D1-FRU-02 / W1/W3:** actual selected original CMP119/122/116 marked-J source dictionary, full Wilson small+large decomposition, nonvacuous admissible physical remote supports, absolute connected cluster charge and cutoff/volume-uniform q<1 in **physical** units. Reuse `YMClayD1OriginalFullWilsonSmallLargeFieldExact.OriginalSmallLargePhysicalSource` and `BalabanLiteralTwoWilsonCMP116ConnectingTailExact.TwoWilsonCMP116PhysicalShellPayment`; do not duplicate covariance or shell theorems.
3. **E1/D2/N1/G1:** original interacting continuum/OS, dense same-H nonvacuum spectral gap, noncollapse and every compact simple group remain open.

## Verification / trust

The companion `scripts/check_ym_original_wilson_periodic_conflict_coloring_20261121.py` was executed **locally** with SymPy. It exhaustively enumerated all original positive-link plaquette incidences for L=3,...,11, checked all four plaquette colors distinct and checked arbitrary sampled marked subsets/pigeonhole, proved exact-rational q-power improvements for n=1,...,249, and independently checked native n=3 side-four 128 selected links partition into four orientation classes (32 each) with all 896 spectators retained. The mathematical all-L proof is above. The regression is **not an Agda 2.9 kernel receipt** and does not test continuous Haar, original SU(2) Wilson probabilities or D1 physical estimates.

Attribution: original SU(2) Wilson Gibbs/Haar and prior one-link conditional/animal bound retain their original repository and literature owners; the explicit 4k periodic transverse-color packing and R445 geometry connection are a new finite combinatorial refinement. Do not present them as a completed 4D YM mass-gap or CMP116 physical-source proof.

## 22 November 2026 — original four-axis chessboard face and R445 BIDI correction

The previously attributed #1444 20-Nov chessboard source had a **literal transverse face-map error**, now corrected at its owning source in commit [76802c60](https://github.com/chboishabba/dashi_agda/commit/76802c60ff135ed5083f9b06b59bb387852fd403). For a tile x and transverse class parity s in {0,1}, the face at coordinate x_k must be at

`x_k + ((s - x_k) mod 2) mod L`,

not `x_k + (x_k mod 2) + s`. For odd x_k and s=1 the old formula selects x_k+2, outside the unit cube. The corrected coordinate is always x_k or x_k+1. Over all 6 plaquette orientations and 4 transverse parity shifts, the corrected 24 classes have exactly V/4 distinct plaquettes each, disseminated four times from V tile marks. Independent exact L=4,6,8 enumeration found 3,072 / 15,552 / 49,152 off-cube transverse positions using the old formula and zero using the corrected formula.

A second **original literal Wilson source geometry** test, [check_ym_original_wilson_four_axis_chessboard_bidi_20261122.py](../../scripts/check_ym_original_wilson_four_axis_chessboard_bidi_20261122.py), covers site reflections in every direction and at two representative site planes at L=4 and L=6: reflected positive bonds and inverse orientations, real-trace Wilson plaquette words modulo cyclic reordering/inversion, exact positive/negative/boundary halfspace decomposition, and no plaquette containing bonds from both open halves. For original side-four R445 it also checks all 64 native two-link products transform in the correct order/inverse and that the 128 selected and 896 spectator original bonds are separately preserved.

**Trust:** corresponding independent Python exact-integer tests were executed locally. The newly committed GitHub script was source-written and read back; it has NOT been independently executed as that exact checkout. The test is finite geometry, not a Haar/chessboard probability computation or Agda 2.9 kernel acceptance. The *complete iterative chessboard Cauchy–Schwarz applicability* with the original boundary-link observable algebra, original W1/W3 marked-cluster charge, cutoff running-beta and physical-scale calibration, continuum E1/OS, same-H D2 and N1/G1 remain open. The pre-existing November 19/20 microscopic sparse contour estimate is conditionally reusable after the corrected source dictionary; this geometric fix does not promote it to a full 4D Wilson covariance estimate.
