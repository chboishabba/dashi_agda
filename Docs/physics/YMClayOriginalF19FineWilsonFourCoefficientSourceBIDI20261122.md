# YM P0 — original F19 fine-Wilson four-coefficient source BIDI

Date 22 November 2026. Scope: original finite 4D SU(N) Wilson Gibbs and R445 native 64 ordered fine-link pairs / 896 interacting spectators. **This is not a new polymer gas, RG rate or Clay theorem.**

## Prior source owners already built

The repository already has: \`YMClayOriginalWilsonAffineMarkedPartitionExact\` and \`YMClayOriginalWilsonFiniteTwoSourceJetExact\` (original full Wilson affine source and mixed log jet); \`YMClayOriginalWilsonCanonicalMarkedReindexExact\`, \`YMClayOriginalWilsonPairSpectatorDecoderExact\`, \`YMClayNativePairsSpectatorsFubiniExact\`, \`YMClaySUNWeightedDisjointPairFibreReparamExact\`, and \`YMClayOriginalWilsonPhysicalF19PartitionExact\` (all-link weighted Wilson Haar, full 128 selected and 896 spectator transport); and **\`YMClaySUNOriginal64Pair896MarkedEffectiveSourceExact\` plus \`YMClayOriginalWilsonF19ConcreteWeightExact\` (complete original F19 TWO-source transport when both marks depend only on the 64 blocked coarse links)**. The last theorem is already written, not a missing construction.

Existing W1/W3 consumers \`BalabanLiteralTwoWilsonSourceFirstNormalizedJetExact\`, \`BalabanLiteralTwoWilsonSourceFirstJetLocalizationExact\` and \`BalabanLiteralTwoWilsonCMP116ConnectingTailExact\` are conditional on the true original source renormalized KP activity and absolute marked shell charge.

## New exact finite fine-mark source correspondence

Let the same original positive Wilson weight be w(P,S), where P is the original ordered vector of 64 pairs (U_j,V_j), S all 896 original spectators. Use existing exact F19 noncommutative Haar reparametrization W_j=U_j V_j and V_j as fibre, U_j=W_j V_j^{-1}. For arbitrary bounded gauge-invariant fine Wilson word marks F(P,S), G(P,S), define under the **same original fibre Haar integrals**:

    K0(W) = ∫_{64 fibres,896 spectators} w,
    KF(W) = ∫ w F,    KG(W) = ∫ w G,    KFG(W) = ∫ w F G.

The ORIGINAL marked partition identity is

    Z_fine(s,t) = ∫_{64 coarse Haar} [K0+s KF+t KG+st KFG].

All four original original-Wilson moment coefficients transfer exactly; the normalized mixed log derivative at (0,0) is the SAME original full-Wilson covariance. Do not independently construct an effective measure or forget spectators.

When K0(W)>0, set f=KF/K0, g=KG/K0 and c=KFG/K0-fg. The exact effective affine source is

    K0[(1+s f)(1+t g)+st c].

The **fibre-connected c** generally does not vanish. For pre-existing F19 **coarse-only** marks F(W),G(W), their common fibre integration pulls them out and c=0, so the established source theorem is recovered as a special case. The normalized exact total-covariance identity is

    Cov_original(F,G) =
      Cov_coarse( E[F|W], E[G|W] )
      + E_coarse[ Cov(F,G|W) ].

The new source owner \`DASHI/Physics/YangMills/YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact.agda\` defines original fine integrand, effective moment density, and originalPhysicalF19Z/F/G/FG + normalizedFG. Its proof reuses existing \`selectedSideFour64Pair896SpectatorChange\` and \`originalInterleavedIntegralIsCoarseFibre\` for four arbitrary fine-Wilson source coefficients. **Source-written, Agda kernel not run.** No original W1/KP activity is magically instantiated by this arithmetic.

## Independent full-original-action finite regression

\`scripts/check_ym_original_f19_fine_mark_fibre_20261122.py\`: use all **1536 original periodic L4 Wilson plaquette words** and exact actual R445 all-link selection (128 selected=64 pairs; 896 spectators). Keep THREE full selected axial pairs plus nine neighbouring spectator links active, the other **1009** original links fixed to identity. Precisely 66 of 1536 original plaquettes depend on this live subset. Give the 15 live link matrices SU2-centre values ±I, β=ln 2; full original Wilson action remains present on this **conditional discrete slice** (not the original continuous SU2 Haar law).

Compute four original weighted moments 1,F,G,FG for two opposite-face fine Wilson plaquette words using both (a) **32768 direct fine-link assignments** and (b) **32768 original R445 three-pair fibre/spectator assignments**, organized in eight fixed-coarse sectors, with all 9 live spectators integrated. Every coefficient matches exactly on 8/8 sectors and the original normalized affine mixed log jet matches. The source fibre c(W) is NONZERO in all eight sectors, proving the naive replacement KFG=KF KG/K0 loses a real original fine-Wilson mixed contribution. For *coarse-only* test marks c=0 as required by the existing original F19 theorem.

Illustrative conditional test numbers: original covariance ≈1.439311238264995e−5; between coarse means ≈3.7163971343613782e−6; within fibre ≈1.0676715248288572e−5, accounting for ≈74.1793% of the finite test covariance. **No continuum correlation length or physical SU2 Haar covariance inferred.** The fuller locally executed Fraction/SymPy independent checker passed; committed compact script was read back, not independently executed bytewise; the new Agda owner has no kernel receipt. No GitHub CI.

## Physical remaining max-cut

The fine-fibre four-coefficient BIDI is source algebra; it does **not** construct a renormalized polymer activity or an all-cutoff estimate. Carry the original two unique affine insertion labels and the **nonzero fine-fibre st connected coefficient** through SAME-original CMP119/122 RG small/large-field construction. Show source-first renormalized polymer cluster logarithm reconstructs the same full Wilson mixed jet, rather than fitting a surrogate gas. Then pay actual W1 pointwise source localization and W3 \`chargeSumBelowPhysicalRootedShell\` at uniform physical separation/cutoff/volume. Alternate route: quantitatively compare true original good-conditioned Gibbs covariance and literal CMP116 small-field J plus existing original chessboard large-field error. Full E1 interacting R4 OS continuum, D1 full all-cutoff covariance, D2 dense same-H nonvacuum mass gap, N1 and G1 remain OPEN.

Attribution: original Wilson/Haar, Bałaban CMP109/116/119/122, Kotecký–Preiss/Fernández–Procacci, and existing DASHI original native F19/W1/W3 source owners.
