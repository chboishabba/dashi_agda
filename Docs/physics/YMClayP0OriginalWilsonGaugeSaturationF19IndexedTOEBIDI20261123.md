# YM P0 geometric-forward correction — full original gauge-orbit saturation of finite marked Wilson/F19 regression

23 November 2026. **Exact original native-link/plaquette geometry PASS; stronger gauge-covariant source fibre constructed as a finite Z2 saturation. Physical continuous SU(N), CMP119/122 T, W3/OS remain OPEN.**

## Source precedence and exact master/PR comparison

Checked live: master commit e8150243 (one later change, an unrelated NS roadmap update, since PR base 116cd7de); original Wilson #1536 at 496dff13 before this correction; original advanced conditional CMP119 owner #1444, genuine RP donor #1535; TOE #1281 (R559), #1291 (H05 cube), #1217 (369/C3 spine), RH #1533 Singer source. Preserve all original SU(N) Wilson/Haar/positive link/marks, R445/F19, source YM theorem-owner and TOE signed-zero chart proofs. No new group/Haar theory or false identity between spatial C3 and SU(N)'s internal centre.

Prior exact 10-live-link, 1014-fixed-link L4 Z2 centre subgroup checker `check_ym_p0_original_wilson_marked_ordered_t_20261123.py` correctly evaluates the ORIGINAL full 1536-plaquette action and four same-source 1/F/G/FG coefficients with nonzero fibre covariances. **Correction:** its 1024-point cylinder is NOT closed under the full local centre gauge group. It is an exact restricted field slice, not a gauge-invariant Gibbs theory. Do not claim its four conditional W covariances are already gauge-invariant conditional physical observables.

## True original gauge-transform geometry

For an original gauge function g on all 256 sites and oriented fine positive link U_mu(x), the genuine endpoint transformation is

```
U'_mu(x) = g(x) U_mu(x) g(x+e_mu)^(-1).
```

For every original native even-origin two-link path (U0,V) with midpoint y=x+e_mu and endpoint z=x+2e_mu, the actual noncommutative R445/F19 product satisfies

```
W'=U0' V' = g(x) [U0 V] g(z)^(-1),
V'=g(y) V g(z)^(-1).
```

The intermediate-site g(y) cancels **only** in W, not in the fine pair or generic original fine Wilson mark. The global original Gibbs action and both *closed* marked Wilson plaquettes remain gauge-invariant; K(W;s,t) transforms covariantly with its W argument under the coarse endpoint site gauge. This is the correct *geometric* square; a naked signed P3^9 chart, scalar mark product, fixed W gauge assumption, or k-as-physical-time substitution is insufficient. Use the existing `YMClaySUNNativeBlockedPositiveHolonomyExact`, `YMClayR445OriginalNativeParityPairWeldExact`, `YMClayY369OriginalSingerWilsonFourMarkSourceWeldExact` and original source gauge-fibre BIDI carriers. No duplicate Agda proof needed.

A concrete original local Z2 gauge pulse g(F)=-I at F=(0,0,0,0), identity elsewhere, flips precisely the 8 source-star fine links: **one** of the previous 10 active variables and **seven** frozen fine links. In the full 1024-link field this same gauge pulse preserves all **1536** original positive Wilson plaquette trace values and both original y-z F/G plaquette marks, and changes **eight** of the 64 native blocked W. This is an exact geometry-and-construction negative control, not an error in the original direct staged Haar integral algebra.

## Gauge-invariant finite centre-subgroup repair, without 2^255 enumeration

Original 4D torus link graph is connected, so its local Z2^256 gauge group has precisely the diagonal constant Z2 kernel; each fine-link field orbit has 2^255 elements. Delete the 10 live-link set from the original full 1024 positive-link graph. The **1014-link frozen complement is still connected** on all 256 sites, directly checked by exhaustive original-edge BFS. If two original ten-link-representative fields were gauge-related, their relative gauge gradient would vanish on the entire frozen complement. Connectivity forces that gradient globally constant, hence it acts trivially. Thus all 2^10 original representatives are in distinct gauge orbits, giving the exact full-original-source gauge saturation

```
|C|=2^10,  |G_eff|=2^255,  |G.C|=2^265.
```

The full original Wilson plaquette weight and closed F,G marks are constant on each orbit. **Consequently, orbit-uniform gauge saturation multiplies all four original global moments 1/F/G/FG by exactly the same 2^255 and leaves all normalized total source responses (including mixed derivative) unchanged.** This is a well-defined finite Z2 gauge-invariant SUBENSEMBLE of the original centre subgroup Wilson theory, not the entire 2^1024 Z2 link-Haar theory or continuous SU(N) Haar.

### Coarse gauge-fibre count (keep W orbit, do not freeze W)

Delete just the two marked z-axis coarse W links from the native 64-link, 16-site side-two R445 coarse graph. Its remaining 62 coarse edges are connected on all 16 original coarse gauge sites (independently checked). Therefore the four former coarse W representatives label **four distinct** coarse gauge orbits of size 2^15 each. Each gauge-saturated coarse W has exactly 2^8 original representative fine-fibre/spectator assignments times 2^240 fine-site gauge lifts, hence 2^248 fine configurations:

```
4 * 2^15 * 2^248 = 2^265.
```

This distinction is crucial: **the original four per-W conditional covariances are values in the chosen source gauge slice, not values at each gauge-transformed W without further pushforward.** The global normalized source moments remain invariant. A physical CMP119/122 constrained T must specify the gauge-fixed or gauge-covariant coarse field and its Haar/FP/Jacobian map, not identify fixed representative W with its full coarse orbit.



### Positive coarse-orbit BIDI: conditional source jet survives AFTER real gauge pushforward

The preceding prohibition is against assigning fixed-W values to relabelled W **without construction**. This construction is now paid for the finite Z2 centre-gauge saturation. Independently row-reducing the actual original 16-site/64-directed-bond coarse gauge incidence map over F2 gives rank **15**, and each of the four selected two-bit W representatives is in a separate coset of its image. The explicit 62-frozen-coarse-bond connectivity is the matching constructive proof, not a numerical rank assumption.

For each original representative coarse W0, every W' in its 2^15-member original coarse-site gauge orbit has exactly 2^240 fine-site gauge lifts per original 10-link cylinder assignment (kernel of fine effective Z2^255 -> coarse effective Z2^15). Since there are 2^8 original assignments per W0, each W' has 2^248 saturated fine configurations. For **each** source column alpha in {1,F,G,FG}, Wilson action and closed Wilson marks are invariant along the original gauge orbit, so the precise *unnormalized* transport is

```
K_alpha^sat(W') = 2^240 * K_alpha^slice(W0)   (raw finite counting).
K_alpha^sat(W')/2^248 = K_alpha^slice(W0)/2^8.
```

Therefore the conditional normalized F/G means, FG moment, covariance `K0*KFG-KF*KG` divided by `K0^2`, and the full finite two-mark mixed-log jet are exactly constant along each **properly transported coarse W gauge orbit**. The original four representative conditional covariances are valid **after** this proved gauge-orbit pushforward; they must not be read at an arbitrary W outside the four saturated orbits, nor as CMP119 physical T data. This is the geometric-forward positive statement required to complement the negative gauge-closure control. The new GF2 rank/coset and 2^240 counting assertions pass in the source checker. Neither the full 2^1024 Z2 Gibbs law nor full SU(N) Haar/local RG is inferred.

## Verified source tests

- [Original real Wilson action, direct vs staged finite four-mark F19](../../scripts/check_ym_p0_original_wilson_marked_ordered_t_20261123.py): local exact rational PASS on actual full 1536-plaquette action, restricted centre subgroup, four original W representatives.
- [New full-gauge source orbit and coarse fibre](../../scripts/check_ym_p0_original_gauge_orbit_20261123.py): original 1024-link/1536-face gauge action PASS, exact 64 blocked path endpoint law, 8-link gauge-star negative control, both connected complements, and constructive 2^265/2^248 source counts. Source-equivalent local Python 3 execution PASS; GitHub source readback and Agda kernel/CI are separate trust grades.

### Pareto next step / fail-closed source boundaries

**P0.T geometry:** reuse the existing complete native original SU(N) product-Haar and 1/F/G/FG F19 operators, index both fine and coarse *gauge action* (including midpoint and spectator gauge degrees) and preserve the selected CMP119 Omega/Lambda/S histories and residual with S internal to T. Attach the already-existing actual CMP122 Eq.(1.71) R/gauge/FP/constrained localized operation **on the same source measure**; the finite Z2 gauge saturation is a precise negative-control/calibration, not the physical source proof.

**P0.W3:** prove positive physical-distance uniform cutoff/volume *absolute* two-mark native connected-shell estimates for that one source, not a signed Wilson covariance or a gauge-orbit count. **P0.OS:** source noncollapsed continuum and same-H dense gauge-invariant reconstruction; E1/D1/D2/N1/G1 remain open. Never promote finite Singer-k indexing or six H05 cube faces to a physical compact gauge-group mass gap.

Attribution: Wilson/Haar, Bałaban CMP98/109/116/119/122 and classical lattice-gauge endpoint covariance, existing original DASHI SU(N)/R445/F19, signed-zero/TOE H05 and RH Singer construction owners. No Agda kernel, CI or Clay completion claim.
