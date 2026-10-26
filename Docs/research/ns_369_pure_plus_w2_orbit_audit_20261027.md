# NS 369 × R734/R735 pure-helicity W2: exact physical orbit and role boundary

**Date:** 27 October 2026. **Owner:** existing R734/R735 and 369 physical Fourier carriers. **Status:** exact finite physical Fourier calculation, locally tested; source-written Agda cross-cycle theorem; no checked Agda proof of W2, high-high Gram coercivity, or Clay A/B.

## Same-source original roots and 369 archaeology

The repository already has several **distinct** constructions involving “369.” Preserve their actual theorem ownership instead of treating a common number or triadic analogy as a proof:

1. `DASHI/Physics/Closure/NSTriadKN369HighHighGramBridgeReceipt.agda` with `docs/ns_triad_kn_369_high_high_gram_bridge.md`: organizes finite high-high triad/sign/profile classes for the live **Gram Rayleigh/min–max** target `lambda_min(K_N(A)) >= c/N`. The actual uniform lower bound is expressly still open. The source note excludes a bare proxy, Schur and ACL shortcut.
2. `NSTriadKNPeriodicFourierTernaryTorusFibreBidiRound530Exact` and `NSTriadKNPeriodicTorusBase369NormalizationRound531Exact`: a **coordinate-sign** quotient of a periodic Fourier lattice mode into the finite ternary `{-1,0,1}³` carrier and its periodic adjacency. This **forgets norms**, exact component magnitudes, amplitudes, phase and helical polarization. It is NOT a claim that the torus manifold is a 27-element set, nor a lattice/continuum measure bridge.
3. `NSCross369OrientationBridgeExact`: original literal Complex3 cross/curl orientation representation. It distinguishes proper from improper coordinate transformations and explicitly disallows confusing `Complex3` with cyclic group `C3`. **New source-written theorem** `cyclic369CrossEquivariant` proves the literal cross commutes with the three-axis cyclic permutation, and `cyclic369ThirdPowerIdentity` records its order three. Both are definitional source equalities in the original NS cross carrier; **not independently kernel typechecked**.
4. `NSTriadKNPackageAToSameSolutionSerrinRound369Exact`: **another** “Round369,” a source-written conditional transport from a paid Package A physical mixed-helicity budget to the *same limiting solution* in the Round103/Serrin continuation consumer. It does NOT produce Package A, signed W2, the original R406 physical identity, or any unrestricted smooth extension.
5. `NSTriadKNTorusEuclideanR406MeasureBridgeBoundaryRound528Exact` and `NSTriadKNBase369TeslaMonsterR406CrossDomainBidiRound532Exact` explicitly retain the unsolved continuum spectral-measure, cutoff and exact R406 signed-cross transportation requirements. Neither reflection symmetry nor finite 27-orbit classes supply those estimates.

**Original mathematical provenance:** Fabian Waleffe, *The nature of triad interactions in homogeneous turbulence*, Physics of Fluids A **4** (1992) 350–363, DOI 10.1063/1.858309 (first-link source); this formalizes the eight helical triadic classes and energy/helicity transfers, not any DASHI global proof. Independently, Biferale and Titi, *On the Global Regularity of a Helical-decimated Version of the 3D Navier–Stokes Equations*, 2013, arXiv:1303.1215, proves a different, **helicity-decimated** equation, not the unforced full dynamics. Modern 2026 `Gürcan–Manfredini–Morel` arXiv:2609.20710 studies triad-triplet affinity and inviscid-limit coherent solutions; **technique donor only**. Recent preprints claiming unrestricted Navier–Stokes regularity cannot be counted as accepted proof without independent mathematical validation. Retain first-link attribution under existing `IbrahimSnowballParetoFrontierExact` source policy.

## Original physical six-mode counterexample is stable under 369 cyclic orientation

The EXACT original R734/R735 normalized-helical positive-sector datum:
```
p=(1,0,0),  q=(0,1,2),  k=p+q=(1,1,2)
seed_p=(0,1,1), seed_q=(1,0,0), seed_k=(1,-1,0)
u_hat(m)=H+_m seed_m, u_hat(-m)=conj(u_hat(m))
H+_m = (P_m + i m×/|m|)/2
```
at literal sharp Fourier cutoff `N=2`. The ACTUAL full
Galerkin Leray-projected nonlinear force gives
```
X_dyadic(0) = 8
D_dyadic(0) = 36
P_dyadic^NL(0) = [5+sqrt(5)-sqrt(30)]/10 > 3/20 > 0
M_(+,-)(0) = 0
```
Therefore scaling by amplitude 512 yields positive **initial physical critical growth** in the original dyadic observable despite zero initial mixed-helicity work. This rules out the universal R734 augmented W2 positive-margin inequality in the physical real-helical Galerkin interpretation, on a short initial interval. It does not rule out finite smooth existence, change the abstract Agda conditional compiler's logical correctness, or prove Clay A/B.

Define `R(x,y,z)=(y,z,x)`. The cyclic proper rotation has determinant +1, preserves cross/Leray and normalized **positive** curl helicity, and preserves the sharp cube `||m||infty<=2` and the literal dyadic critical weight `2^ceil(log2||m||infty)`. Repeating the *complete projected Fourier calculation* for `R^j`, j=0,1,2, yields exactly:
```
(X_dyadic, D_dyadic, P_dyadic^NL)
= (8,36,[5+sqrt(5)-sqrt(30)]/10)
```
on all three distinct ternary sign-triad signatures. All three remain initially pure H+, with same zero mixed W1 carrier. Scalar amplitude multiplication leaves the 369 finite wavevector sign/profile/adjacency class unchanged, but nonlinear production scales cubically and viscous damping quadratically. Thus **finite amplitude-blind sign classification cannot by itself rescue the universally false W2 payment**.

Extending the independent physical test over **all six coordinate permutations** shows one further fact: the Fourier sign-profile quotient has only **three distinct** signatures across the six arrangements. Each sign signature is shared by one proper permutation and one improper permutation. The latter swaps positive/negative curl helicity because curl is a pseudovector (orientation changes sign), even though the actual critically weighted production is unchanged by the reflected full NS equation. So the **same 369 sign chart is compatible with opposite physical helicity**, unless the separate orientation/parity datum is carried alongside it. This is a precise first-class reason to reuse `NSCross369OrientationBridgeExact` together with R531 rather than identifying sign fibre with a full helical sign class.

## Gram and continuation nonpromotion

The 369 Gram owner is allowed to classify finite dangerous triad cells, including these counterexample triples. It **has not yet identified its actual K_N(A) Rayleigh form on this field**, and its own support note insists the uniform `c/N` spectral floor remains open. No claim that the present source has disproved that distinct Gram theorem is made.

The *separate* Round369 same-solution Serrin compiler remains a valid conditional consumer only if a truly cutoff-uniform physical critical budget is supplied. The false original universal W2 leaf does not supply such a budget, and no symmetry class automatically fills that gap. The signed critical decomposition already established in R92/R102 should be retained:
```
X_dyadic = H_signed + 2 Hminus_mass + R_weight_defect.
P_dyadic^NL = 2 d(Hminus_mass)/dt|NL + d(R_weight_defect)/dt|NL.
```
This identifies the surviving analytical task: a same-solution estimate simultaneously controlling the negative-helicity exchange and dyadic weight defect, with explicit amplitude scaling, original mode cutoff, real-time integration and genuine viscosity margin.

## Reproducibility and source state

`tests/test_ns_369_pure_plus_w2_orbit.py`: six locally executed exact SymPy tests passed in a matching standalone implementation (three proper cyclic rotations; three distinct ternary profiles; amplitude/rational W2 sign; improper helicity flip; lost metric information; all six permutations collapsing to three sign classes with opposite helicity). Full-source PR-head tests and Agda kernel compilation have **not** been run.

`NSCross369OrientationBridgeExact.agda` has two new source-written polymorphic definitional proofs but no independent checked-head typecheck receipt. The existing R369 Gram/continuation owners and historical authors are unchanged. Original mathematical roots cited above remain credited; these physical counterexample orbit/regression joins are DASHI's independent calculations.

**Pareto next:** (1) verify physical real/complex projectors and high-high Gram actual operator same-object on the exact 369 finite cell; (2) prove a **valid** signed critical energy estimate with both negative helicity exchange and dyadic defect, or produce a separate true critical continuation mechanism; (3) use Round369 only after the uniform physical budget is paid, then finish B7/R406/A1–A3 as applicable. No boolean closure or Clay promotion from coordinate symmetry alone.
