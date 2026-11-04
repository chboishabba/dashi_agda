# Ricci-flat prior-art correction + continuous C3 braid max-cut (2026-10-23)

## Corrected Ricci-flat prior art
Existing repo already contains `DASHI/Geometry/CalabiYauPhysicalProducerCutset.agda`, with a `RicciFlatMetricAuthority` requiring Ricci-flat metric and uniqueness receipts; `DASHI/Geometry/CalabiYauAnalysisAndPhysicalUseBoundary.agda`; `DASHI/Geometry/QuinticThreefoldCandidate.agda`; `DASHI/Physics/Closure/GRPDEParityBoundary.agda`; `DASHI/Geometry/LorentzianLeviCivitaConditional.agda` and other vacuum-Einstein carriers. These are not new this round and are not identical mathematical objects to KK Brinkmann vacuum pp-waves. The CY module's Ricci-flat condition is an authority with string receipts, *not* automatically an explicitly computed metric or completed compactification. Previous PR #1239 descriptions should never suggest Ricci-flatness was discovered here.

## Actual new C3 continuous result
`scripts/check_c3_continuous_affine_mirror_clearance.py` extends the already-proved sampled orbit to each continuous real affine parameter u∈[0,1] between adjacent time steps, using exact rational endpoints:
```
gamma_j(k+u) = (1-u) P[(k+4j) mod 12] + u P[(k+4j+1) mod 12]
```
For all real u by affine-polynomial identity, `gamma_j(k+6+u)=Mx gamma_j(k+u)` and `gamma_j(k+4+u)=gamma_(j+1 mod 3)(k+u)`. Exact rational minimisation of pairwise squared distances on each of 12 edges × 3 strand pairs gives **minimum squared clearance 1**; hence no strand collision on the full continuous piecewise-linear 12-segment motion. The independent equivalent arithmetic in this round also computed the exact minimum 1. This does *not* yet prove topological Borromean closed-braid classification, lift to 3D, normal framing, or O(2)/Pin-to-KK connection identity.

## Residual high alpha
1. Construct continuous transverse nonzero normal frame along each PL line, smooth regularisation and prove clearance under perturbations. Treat corner points carefully: interpolant has no unique tangent there.
2. Extend C2 mirror and C3 strand permutation to normal-frame gluing with explicit transition cocycle and signed integer winding lifts.
3. Prove an *optional* bundle morphism from framed braid local O(2) normal bundle to KK circle bundle with preserved connection/holonomy, only when a separate geometric producer is supplied.
4. Derive general 5D->4D curved-base KK tensor field equations from the metric and boundary variation. Existing KK Ricci-flat local pp-wave family supplies nontrivial regressions, not a universal theorem.
5. Determine whether existing CY Ricci-flat *compact* metric producers yield actual higher-dimensional fibre geometries, SU3 isometries, and consistent matter spectra before proposing colour or Monster physical identification.

## Acceptance
```
python3 scripts/check_c3_continuous_affine_mirror_clearance.py
```
Script is source-committed; independent equivalent integer/rational clearance computation gave min²=1. No exact-head checkout/Agda kernel receipt. Preserve credits for existing CY/vacuum owners.
