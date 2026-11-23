# Clay YM P0.T — original Wilson action in the ordered two-mark F19 conditional source

> **23 Nov geometry correction:** The ten-link Z2 field cylinder is **not closed under local source gauge transformations**: one original site pulse flips eight native fine bonds (one live, seven frozen). The full original Wilson action and marks are gauge invariant, but the restricted ensemble itself is not. [The exact source-gauge-orbit repair](YMClayP0OriginalWilsonGaugeSaturationF19IndexedTOEBIDI20261123.md) proves the 1014-frozen-bond complement connected, builds a finite *gauge-invariant centre-subgroup saturation* of 2^265 states, and keeps the globally normalized 1/F/G/FG responses unchanged. The four old fixed-W conditional covariances are **gauge-slice data**; transformed coarse W requires covariant conditional pushforward. This does **not** produce full SU(N) Haar or physical CMP119 T/W3/OS.

**23 November 2026. Local exact arithmetic PASS. Physical CMP119/122 selected T and W3/OS remain OPEN.**

## Pre-existing theorem ownership

Reuse original `YMClayW0OriginalF19CandidateEquation171TExact.agda` (actual continuous-SU(N)-Haar generic Eq.1.71 candidate and first-pair T localization), `YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact.agda` (all 1/F/G/FG fine Wilson moments), `YMClayR445OriginalAxialBondParityInjectiveExact.agda` (64 source native R445 pairs), `BalabanCMP119Equation218FactorizedFunctionalDensityExact.agda` (domain/sequence/ordered T/residual compiler), and `BalabanCMP119Equation171WeightedStepApproximationExact.agda` (conditional physical per-step identification).

The older `check_ym_w0_original_pair_local_T_q8_20261123.py` used a nonfactorizing illustrative positive weight, not the original Wilson action. The current check exercises the original action itself on a precisely limited finite source subgroup slice.

## Exact original 1536-plaquette test

[Source checker](../../scripts/check_ym_p0_original_wilson_marked_ordered_t_20261123.py).

Native 4D periodic side-four source: 256 gauge sites, 1024 positive fine bonds, and all **1536 six-plane positive plaquettes**. Original R445 even-origin axial pairs: 64 ordered coarse holonomies W=U0 U1, 128 selected fine links and 896 remaining spectator links. Both globally unique fine Wilson trace marks are original y-z plaquettes rooted at (0,0,0,0) and (0,0,0,2).

The exact diagnostic varies **10** fine links in the **centre subgroup Z2={+I,-I} of SU(2)**: 4 links from two disjoint original even-origin y-axis R445 pairs, and 6 genuine coupled spectator links. The other 1014 fine links are fixed at identity, including the other 62 native coarse blocks and the other 890 spectator links. For each of the 1024 assignments the FULL original 1536-plaquette Wilson action is evaluated, including all plaquettes with zero active support. A frustrated centre plaquette has deficit J=2; choosing beta=log(2)/2 yields exactly rational unnormalized weight 2^{-n_bad}. The original selected trace marks F,G take values +/-1.

At each of the four retained W=(W_F,W_G), enumerate first the original conditional fine fibre V_F, then V_G, and finally all six active interacting spectators. The stage count per W is 2*2*64=256. For each source column **1,F,G,FG**, the staged sum equals the independently enumerated original fine Wilson sum at that W, and the normalized Z2-Haar identity holds after dividing by 256 inside each coarse fibre and 4 for outer W (versus 1024 for direct sum). Original F and G remain INSIDE the common source integrand.

For the original affine marks K(W;s,t)=K0+s KF+t KG+st KFG, the exact mixed source-log Hessian is
```
  d_s d_t log K = (K0*KFG-KF*KG) / K(W;s,t)^2.
```
The checker verifies this at 9 rational real source pairs in {-9/100,0,9/100}^2 for each W and the total source, with positive denominators. All four conditional source mixed covariances are NONZERO: W=(0,0) +0.000077069748; W=(0,1),(1,0) +0.0300052164; W=(1,1) -0.0366985862. The total mixed covariance is +0.00459472905664. An exact law-of-total-covariance identity accounts separately for mean conditional-fibre covariance and between-W covariance. The negative conditional contribution is a direct warning against replacing original FG by independently integrated original F and G, or confusing the signed mixed response with an absolute positive CMP116 connecting-shell budget.

## What this pays / does not pay

**Paid:** exact original-action, correctly normalized **finite subgroup slice** stage-versus-flat T consistency for all physical fine-mark source columns; nonzero, mixed-sign conditional covariance on the SAME original Wilson plaquette action. This is a stronger physical-action regression for the already-existing F19 structural first-pair theorem; it adds no duplicate formal T carrier.

**Not paid:** full unfrozen SU(N) Gibbs integration, continuous Haar/gauge/FP Jacobian, actual CMP119 Omega/Lambda/S admissible domains with S internal to T, Eq.1.71 R operation/background, source E/R/B/V and running beta(a), same-source **physical** marked-step identity, termwise ABSOLUTE native rooted-shell charges uniform in physical cutoff/volume, noncollapsed interacting R4 OS and a same-H positive gap. The centre-subgroup slice must not be used as an estimate for any of those.

**Verification:** source-equivalent local finite exact arithmetic PASS; committed script GitHub readback is a separate check, Agda kernel and GitHub CI were not run. Existing Wilson/Haar, Bałaban CMP119/122/116, and original DASHI theorem authors retain ownership.
