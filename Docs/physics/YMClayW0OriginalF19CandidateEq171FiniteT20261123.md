# YM W0 — actual original Wilson/F19 finite Haar mass enters the existing Eq.(1.71) T interface (23 Nov 2026)

## Source reuse; new finite candidate, not the physical CMP119 Eq.(1.71) assertion

[New Agda source-written owner](../../DASHI/Physics/YangMills/YMClayW0OriginalF19CandidateEquation171TExact.agda): instead of another domain AST or an assumed Eq171 equality field, instantiate the EXISTING `BalabanCMP122Equation171TOperationSemanticsExact.CMP122Equation171TOperationSemantics` interface with the existing continuous original one-link SU(N) Haar candidate supplied by the original F19 fibre theory.

Imports/reuses `YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact`, `YMClaySUNWeightedDisjointPairFibreReparamExact`, `YMClayOriginalWilsonF19ConcreteWeightExact`, original full Haar/Fubini and the existing Eq171 interface. Fixes the exact original L4 source, 64 noncommutative ordered fine link pairs and 896 interacting spectator links, a fixed Wilson beta, and the same original fine physical Wilson weight. This is NOT a new SU(N) Haar existence proof: `OneLinkProductHaar`, its bilateral invariance, and its linear functional laws remain explicitly provided certified structures.

At each fixed 64-link coarse holonomy W, for any fine integrand h:
```
spectatorMarginal(h)(pairs) = ∫_(896 spectator links) h(pairs,spectators) dH
candidateT(h)(W) = ∫_(64 original pair fibre V at fixed W) spectatorMarginal(h)(WV^-1,V) dH
```
The new `sourceConstrainedHaarT` is exactly `Fibre.actualAllPairsFibreIntegral`, and `candidateF19Mass` is *definitionally* the already established `Original.originalF19CoefficientDensity`. The `originalF19CandidateEquation171` record supplies an actual `equation171ConstrainedIntegral` and `sourceTOperationMass`, with `equation171DefinesTOperationMass = refl`; unlike the earlier conditional Eq171 source records this is an inhabitant of the **generic Eq171 semantic interface** on the **original source integration**, not a free mathematical equality field. The record's `equation171ExponentialDensity` field is instantiated with the integrated h; for marked h this is generally not a single exponential, so the record is a candidate structural T adapter only.

The existing F19 all-arbitrary-integrand theorem proves
[
int_{	ext{original sorted fine 1024 links}}h,dH^{1024}
=int_{	ext{coarse }W}mathrm{candidateT}(h)(W),dH^{64}.
]
The full-original-canonical unsorting is already in separate original permutation theorems. `physicalFineZEqualsCoarseCandidateT`, `physicalFineFEqualsCoarseCandidateT`, `physicalFineGEqualsCoarseCandidateT`, `physicalFineFGEqualsCoarseCandidateT` explicitly specialize this same-source equality to the physical original Wilson weight multiplied by `1,F,G,FG`, respectively. The FG term is transported *inside* the same fixed-coarse T, rather than multiplying independently averaged marks.

This advances W0 from an abstract possibility to a typed **source-inhabited original-Wilson finite candidate** occupying the generic Eq171 carrier. It does not imply the historically selected localized Bałaban T has this whole-volume fibre or trivial domain, that any original CMP119 `sourceTAt` field is now instantiated, or that this family has the Eq.(1.71) exponential action with all source gauge/FP/Jacobian and characteristic factors.

## Original geometry and missing physical equality precisely separated

CMP119's actual source extract, `Docs/support/reference/balaban-source-extracts/cmp119-rg-lattice-gauge-i.txt` pp.254–258:
- outer admissible Omega/Lambda nested domain sequences, source determining set B and background minimizer U_B(V);
- S_j internal to T_k (NOT a duplicated outer sequence);
- local large-region connected component factorization, with disjointness needed;
- ordered T^(j) integration over region intersections and constrained delta/gauge-fixing, modified by R;
- Eq.(2.23) sourced E/R/B/Wilson/vacuum action.

Existing P10/P11 ownership/halo, BalabanCubeEdgeDomains, P3 blockMap/coarseMatches, Eq171 localized T, CMP119 ordered-factor algebra, beta history, and Eq171 weighted approximation are the preferred donor import graph.

The new single-cutoff all-64-pair F19 candidate is a **boundary value/sanity check** for the desired localized physical step: a genuine source-local T realization must reproduce the corresponding original four marked Wilson moments upon the source's admissible sums, conditioned intermediate-state integrations and residual insertion. It cannot simply rename the all-fibre integral "Bałaban's T^(j)". In particular, no justification yet shows `Omega, Lambda, S` and source partitions/collars, FP/gauge fixing, source delta constraints, scale-by-scale field supports, selected beta(a) and E/R/B normalization coincide with this finite candidate.

## Verification/acceptance

Source-written Agda; GitHub contents readback performed. Local kernel/transitive import acceptance remains pending. The equalities rely on existing original F19 all-integrand Haar proof terms, and any `machineChecked` metadata in imported modules does NOT substitute for a pinned Agda kernel receipt. No new numerical/analytic estimate, original CMP119 physical T identification, W3 cutoff-uniform absolute rooted shell, OS reconstruction or Clay gap claim.

Attribution: original Wilson/Haar, Bałaban CMP119/CMP122, and DASHI original F19/finite-real T owners.
