# YM P0 W0 — actual original F19 first-pair localized T composition (23 November 2026)

## Mathematically constructive result

In response to the demand to perform the physical T equality rather than keep restating it, we found that **one real local SU(N) Haar pair-integration step** is already definable and exactly provable from original F19. We extended the existing `YMClayW0OriginalF19CandidateEquation171TExact.agda` rather than invent another T interface.

Let the original first selected fine pair be `(U_0,V_0)` with the actual noncommutative coarse block `W_0=U_0 V_0`; the original fixed-W change of variable is `U_0=W_0 V_0^{-1}`. Leave all remaining 63 ordered pairs and all 896 Wilson spectator links inside the continuation, with **no factorization** of the Gibbs density or marked observable. Define

```
T_first(W_0,W_tail)[h] =
  ∫_(SU(N) Haar on V_0) [
    T_63(W_tail)[h((W_0 V_0^-1,V_0), remaining pairs)]
  ] dH(V_0).
```

`sourceFirstPairTStep` is this operation in the **original F19** fibre algebra, and the new Agda term
`sourceF19FirstPairLocalizationExact ... = refl` states

```
sourceConstrainedHaarT (W_0 :: W_tail) h
       = sourceFirstPairTStep W_0 W_tail h
```

because the original source `Fibre.actualAllPairsFibreIntegral` is **defined recursively in exactly this order**. This is an equality for EVERY fine-pair integrand and therefore, after spectators remain inside the integrand, for the actual original 1024-link Wilson physical density and all 1/F/G/FG marks. `sourceF19MarkedFirstPairLocalizationExact` explicitly composes the same equality with the 896-spectator marginal. There is no new Haar law or spatial-domain hypothesis in this proof.

The already existing `Fibre.actualAllPairsFibreIntegral` recursion therefore supplies a corresponding 64-step full ordered conditional SU(N) Haar integration over the original selected pairs, using one common, coupled fine weight. This is an authentic **original F19** local-fibre-step identity, not just the earlier two-state transfer example.

## Independent exact finite noncommutative check

[Q8 regression](../../scripts/check_ym_w0_original_pair_local_T_q8_20261123.py) was independently reproduced locally using the order-eight unit quaternion subgroup of SU(2), 64 two-coarse-link configurations, 512 fine fibres for each (two independent pair V variables plus spectator), all 1/F/G/FG coefficients, and a positive **nonfactorizing** illustrative weight coupled across pairs/spectator. The staged first-pair->remaining-pair->spectator evaluation agrees exactly with the flat enumeration in 64/64 configurations; associativity and noncommutativity also checked. No claim the illustrative weight is the Wilson lattice plaquette action, nor that finite Q8 equals continuous SU(N) Haar or a physical CMP119 localized T.

## Correct geometry and remaining source equality

CMP119 1988, pp. 254–258, Eq. (2.18) sums admissible Omega/Lambda histories with S_j summation **inside** T_k. Eq. (2.19) factors genuinely disjoint large-field components; Eq. (2.20)/(2.22) composes scale-dependent localized T^(j) integrations on specific domain intersections, with delta constraints, gauge fixing, R-changed characteristics and boundary B. The source-selected minimal background U_B(V), normalization and E/R/B action are not definitionally the F19 coarse W map.

**Important limit:** our actual F19 first-PAIR localization is NOT automatically Bałaban's first RG *scale/localization-domain* step. A pair of fine bonds is not necessarily a source connected large-field domain, and the full 64-pair operation need not equal any individual `T^(j)(X)`. Identifying these requires a physically selected source geometry/function-space map. In fact **an unrestricted pointwise equality between a single proper local T and the full F19 operator would generally be false**; source comparison must concatenate the original ordered steps, interior conditioning, disjoint component products, admissible history sums and source residuals.

The right **remaining concrete source theorem** is now:

1. Select original CMP119 Omega/Lambda/S histories and the exact coarse-determining map B on original 4D Wilson links; show which **existing original F19 pair/spectator conditional steps** correspond to each selected source-local integration and which fields remain in the continuation.
2. Identify sourced integration constraints / characteristic/delta/FP/Jacobian and local Wilson E/R/B/vacuum factors with that *same* original fixed-density marked integrand. S_j is internal T and never double counted.
3. Assemble the physically sourced ordered domain/component/history operation and show its output **on 1,F,G,FG** equals the F19 local conditional mass, with normalization. The proof cannot be replaced by an abstract `sourceApplicationIsEquation171Mass` record field.
4. Derive absolute marked W3 and a cutoff-independent scale rate on the reconstructed same-source physical Hilbert space.

## Acceptance

The Q8 exact group/arithmetic regression was independently executed locally. GitHub Agda readback was confirmed; no Agda compiler installed or pinned kernel receipt obtained. The new Agda equalities are source-written structural `refl` reductions using the original conditional Haar recurrence, not verified kernel facts. The source still imports legacy `RealAnalysisAxioms` and Haar laws as certified assumptions. No physical CMP119 all-domain RG/localized T identity, no continuum or Yang–Mills mass-gap theorem is claimed.

Attribution original Haar/Wilson, Bałaban 1988 CMP119/1989 CMP122, existing DASHI F19/R445/P3/Gate4 authors.
