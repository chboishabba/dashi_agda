# YM P0 — exact original finite Wilson Haar → labelled marked Mayer polymers; KP physical no-go

22 November 2026. New finite same-source decomposition, plus a rigorous warning against treating it as the existing convergent physical W1/W3 Kotecky–Preiss gas. Attribution: Wilson gauge action and compact Haar, classical Mayer/cluster polymer decomposition, Kotecky–Preiss/Fernandez–Procacci, Bałaban CMP116/119/122, and the existing DASHI original P06/Step-V and W1/W3 compilers. The source argument is an ordinary finite combinatorial Haar identity, not a novel continuum theorem.

## Exact full original finite source theorem (arbitrary finite periodic SU(N) Wilson lattice)

Take the native original four-dimensional periodic finite lattice, all original oriented plaquettes P(L), and **all original links**, with independent normalized product Haar reference law H_L. In particular the R445 L=4 instance retains all 1024 fine links (128 selected and 896 spectators), not only the selected coarse sample. Let t_p(U) be the actual normalized real oriented plaquette Wilson trace and β>0 the original coupling. Fix two bounded gauge-invariant **closed** Wilson loop/plaquette marks F(U),G(U) with literal original link supports S_F,S_G.

The original unnormalized affine-marked Wilson generating function is, modulo the configuration-independent usual Wilson-action additive constant,

    Z_L(s,t) =
      integral_{H_L} [ prod_{p in P(L)} exp(β t_p(U)) ]
          (1+s F(U))(1+t G(U)).

The normalized expectation source used by the existing affine Wilson W1 owner is Z_L(s,t)/Z_L(0,0). In particular the mixed log derivative at (0,0) is the original **full** Wilson connected covariance, without a source-specific surrogate measure.

Set f_p(U)=exp(β t_p(U))-1. Introduce one finite set of UNIQUE factor labels E=P(L) disjoint union {Lmark,Rmark} and literal functions

    phi_p=f_p, phi_Lmark=s F, phi_Rmark=t G.

Use supports of actual original link variables in each phi_e. For any nonempty label subset C⊆E which is connected in the undirected graph e~e' iff their original link supports overlap, define one **labelled connected polymer** and its activity

    z_C(s,t) = integral_{product Haar on union_{e in C} supp(e)}
                    prod_{e in C} phi_e(U).

Compatibility of two distinct labelled connected polymers means their original link supports are disjoint. Since the original measure is PRODUCT Haar over the actual fine links, for any subset A of distinct factor labels the Haar integral of prod_{e in A} phi_e factors into the products of z_C over its unique link-overlap connected components C. Therefore, exactly and at every FINITE cutoff/volume,

    Z_L(s,t)
      = sum_{pairwise compatible F of labelled connected polymers}
             prod_{C in F} z_C(s,t),

with the empty family contributing 1. The bijection is explicit: original factor-label subset ↔ unique connected-component polymer family. There is NO independent source polydisc, conditional convergence assumption, abstract activity/shell identification or deletion of spectators in this identity.

**Critical source detail:** the two global Wilson marks are their OWN labelled hyperedges, not independent multipliers applied blindly to each polymer. If a polymer includes both marks its activity carries st; alternatively source effects can be mediated by incompatibility among connected/marked polymers in the full gas. Each mark label is available at most once. This fixes the prior cross-polymer counterexample structurally, at the price of introducing the literal finite high-temperature/Mayer activity (which is *not* proven small).

The exact source polynomial Z_L(s,t) has only monomials 1,s,t,st. For any β with Z_L(0,0)>0, its mixed normalized log jet at zero is Cov_{original Wilson}(F,G). This is a source-level finite W1 identification with the newly defined labelled Mayer gas, not yet the existing **KoteckyPreissTwoWeightData** or its source-first normalized cluster enumeration.

## Exhaustive native 4D Wilson cube regression

The locally executed and byte-verified Git regression scripts/check_ym_original_wilson_cube_mayer_marked_polymer_20261122.py uses six actual oriented plaquette words surrounding a unit 0-1-2 cube embedded in the original four-dimensional side-four lattice. There are 12 distinct original links, each occurring on exactly two plaquette faces. F and G are Wilson plaquette real-trace characters on OPPOSITE cube faces and have disjoint literal link supports.

The base integration is a full product Haar sum over SU2 CENTER subgroup {+I,-I} on those twelve independent links, NOT the original continuous SU2 Haar measure. β=log 2 ensures each 2^(trace) and each labelled activity is an exact rational. For the centre link characters χ_p=±1,

    f_p=2^(χ_p)-1=1/4+(3/4)χ_p.

All 256 subsets of six plaquette labels and two unique global mark labels admit canonical overlapping-link components; they yield 244 distinct nonempty connected labelled polymer subsets. The connected-activity gas's four exact marked partition coefficients (1,s,t,st) agree with independently enumerating all 2^12=4096 original link-Haar assignments:

    (Z, Z_F, Z_G, Z_FG)
        =(8177,5295,5295,3825)/2048.

The six face masks obey exactly one nontrivial Z2 Bianchi relation, XOR_{six faces} mask=0. Hence, for tau=tanh β, the opposite-face **connected** original Gibbs response is exactly

    Cov(F,G) = tau^4 (1-tau^2)^2 / (1+tau^6)^2.

At β=log 2, tau=3/5 and Cov(F,G)=3240000/66863329 >0, despite the **disjoint** original link supports of the two marked plaquettes. Independent SymPy differentiation of log[Z+s Z_F+t Z_G+st Z_FG] gives this exact covariance. This is the correct finite source-connected effect, not an independent-polymer product or a physical distance estimate.

## Exact full SU2 HAAR microscopic-activity obstruction

The existing source first physical-polymer producers require, among other genuine obligations, a terminal baseActivityBelowOneSixteenth field (BalabanLiteralTwoWilsonSourceFirstKPDataExact and BalabanLiteralTwoWilsonAffineMarkedActivityExact, FP.rhoBase=1/16). The naive microscopic plaquette Mayer activity above does NOT universally satisfy it.

On the center subgroup at β=log 2, one isolated plaquette has exact Haar-integrated singleton activity z_{p}=1/4 >1/16. This is a finite warning, but the stronger obstruction is on the true original **continuous SU(2) product Haar**. The holonomy of a single original plaquette is exactly SU2-Haar-distributed under reference product Haar. Let t_p=cos θ, with SU2 Haar θ-density (2/π)sin² θ for 0≤θ≤π. The positive trace cap has exact measure

    c = P_Haar(t_p >= 1/2)
      = 1/3 - sqrt(3)/(4*pi) > 1/6.

For the literal unrenormalized singleton polymer,

    z_{p}(β) = E_Haar[e^(β t_p)-1]
             >= c*e^(β/2)-1
             > e^(β/2)/6 - 1.

This tends to infinity with β. In particular for β≥16 the activity exceeds 1/16 by a large margin. A configuration-independent Wilson-action constant e^(-β) per plaquette is irrelevant to normalized Wilson expectations, but choosing a rescaling convention to force small activities requires a NEW exact partition normalization/observable identification and cannot change this direct f_p activity bound.

**No-go scope is narrow but decisive:** direct identification of these *unrenormalized microscopic* original Wilson Mayer polymers with the existing physical KP data claiming baseActivity≤1/16 is impossible in the weak-coupling β-growing regime. This does NOT rule out a correctly renormalized polymer expansion, a multiscale good/large-field construction, or a different source-preserving low-temperature/vortex polymer. It does rule out crediting the finite labelled-component identity as a solved physical W3 summability argument.

## Target existing producers and real maximum cut

Existing authoritative owners to reuse:

- BalabanP06CanonicalAnimalConstantExact and BalabanCMP116R429ConnectedDomainCountingRound440Exact: rooted animal counts, connected support trace and canonical decoder once actual original physical model support is identified;
- BalabanClayGate4OscillationAnimalInfluenceExact and BalabanStepVCanonicalAnimalMarginExact: physical renormalized activity and entropy ratio comparison once actual large-field Gibbs estimate is supplied;
- BalabanLiteralTwoWilsonAffineSourceBoundExact and BalabanLiteralTwoWilsonAffineMarkedActivityExact: the rational affine 9/100 source radius and 6/5 inflation compiler, not a theorem on a global mark being per-polymer separable;
- BalabanLiteralTwoWilsonPhysicalPolymerIdentificationExact, BalabanLiteralTwoWilsonSourceFirstKPDataExact and BalabanLiteralTwoWilsonSourceFirstNormalizedJetExact: actual terminal **renormalized** same Wilson source polymer activities, literal normalized cluster-log mixed jet and source first identification;
- BalabanLiteralTwoWilsonSourceFirstJetLocalizationExact and BalabanLiteralTwoWilsonCMP116ConnectingTailExact: original W3 pointwise locality and **chargeSumBelowPhysicalRootedShell**, currently conditional;
- YMClayD1OriginalFullWilsonSmallLargeFieldExact: original full SU2/SUN Wilson D1 small+large covariance compiler; true original analytic physics record not inhabited.

Precise next source attachment: carry the TWO UNIQUE original affine insertion labels through original Wilson small/large-field/R445 coarse fibre integration and CMP119/122 block activities. Show the resulting renormalized activities and clusters reproduce the SAME full Wilson normalized mixed log jet and preserve provenance (original cutoff, full spectators, physical supports, no reweighting or omission). Then prove a genuinely source-derived renormalized small-field KP/FP or equivalent cluster estimate with **cutoff-independent physical** chargeSumBelowPhysicalRootedShell. In parallel bound actual good-conditioned original Gibbs response vs CMP116 chosen small-field J (not assumed equal) and large-field error by the already original Wilson chessboard estimates. Only afterward use existing W1/W3/D1/E1/D2 compilers.

Status:

- TRUE arbitrary finite SU(N) original product-Haar marked labelled Mayer partition **algebraic identity** from finite expansion and disjoint support Fubini.
- LOCAL_REFERENCE_PASS: 256 source label subset partitions, 244 connected activities, 4096 center-subgroup Haar link assignments, Bianchi and mixed log jet, and exact full-SU2 Haar single-face cap integral. Git blob byte-verified to executed script.
- RIGOROUS NEGATIVE: plain microscopic singleton activity does not meet terminal 1/16 KP smallness for β≥16 in true SU2 Haar.
- NOT shown: SU2 full-lattice numerical Haar quadrature, Agda 2.9 kernel, source-renormalized CMP116 KP physical activities, W3 absolute physical-shell rate, E1 R4 OS continuum, D2 same-H nonvacuum spectral gap, N1 noncollapse, G1 group closure or Clay solution.

No GitHub CI; all finite calculations run locally with Python Fraction and SymPy. Original source and prior authors retain attribution.
