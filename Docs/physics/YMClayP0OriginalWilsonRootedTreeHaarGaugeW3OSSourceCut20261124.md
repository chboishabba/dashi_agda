# YM P0 — exact original Wilson rooted-tree Haar gauge quotient and W3/same-H source cut (24 November 2026)

**Result: mathematical original-source gauge normalization is paid; physical Bałaban CMP119/122 background-gauge identification, original absolute W3 and interacting continuum same-H mass gap remain OPEN.** Local SymPy 1.14.0, no Agda/Lean kernel, CI or Clay completion.

## 1. Source and existing owners: do not rewrite them

Original 4D Wilson SU(N) link/action/gauge at arbitrary finite periodic size is already owned by \`YMClaySUNVariablePeriodicGibbsGaugeExact\`. The original side-four F19 64 ordered noncommutative coarse pairs and 896 interacting spectators, all four unique global source columns and their normalized Haar disintegration already belong to \`YMClayOriginalWilsonPhysicalF19PartitionExact\`, \`YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact\`, \`YMClaySUNWeightedDisjointPairFibreReparamExact\`, \`YMClayW0OriginalF19CandidateEquation171TExact\`. Original native 2-link gauge covariance and finite Q8 orbit saturation are in \`YMClayP0OriginalWilsonGaugeSaturationF19IndexedTOEBIDI20261123.md\`. The periodic tree **index** and off-tree coordinate labels already exist in \`BalabanClayGate4PeriodicTreeGaugeCoordinatesExact\`. The tree-to-Bałaban **background gauge slice** transition is already a separate *conditional analytic* interface \`BalabanClayGate4TreeBackgroundSliceTransitionExact\`—do not identify them.

Use existing physical CMP119 source E/R/B/V state, Eq.(2.18)–(2.22) actual Omega/Lambda/S admissible sequences, Eq.(1.71) source operation with background gauge, nonlinear Q_B and FP/ghost/Jacobian, R constraints, marked-step/density convergence and \`BalabanLiteralTwoWilsonCMP116ConnectingTailExact\`/R573-R576/W3 consumers. This result constructs an actual normalized **rooted lattice tree-gauge** change of variables for the original Wilson measure; it is NOT a new Bałaban T, FP theorem for the background gauge, W3 estimate or spectral theorem.

## 2. Rooted maximal-tree theorem for every compact group

Let graph (V,E) be any finite connected oriented graph, select root o and a spanning tree T. Let G be a compact group with normalized bi-invariant Haar probability dH. Use the original lattice site gauge law

    U^g_(u,v) = g_u U_(u,v) g_v^(-1).

Fix g_o=1. For each child v with parent p, recursively define

    g_v = g_p U_(p,v)       if original link orientation is p -> v,
    g_v = g_p U_(v,p)^(-1)  if original link orientation is v -> p.

Then the *unique rooted* gauge transform U^g is identically 1 on every tree edge. On off-tree edges e=(u,v) let X_e=g_u U_e g_v^(-1). The map

    (U_e)_(all E) <-> ((g_v)_(v != o),(X_e)_(e not in T))

is a bijection, with inverse

    U_e = g_u^(-1) X_e g_v, with X_e=1 on tree edges.

Because the parent-tree recursion is triangular in the original tree links, and each off-tree source link is independently replaced by left/right multiplication with fixed g endpoints, **normalized product Haar** disintegrates exactly:

    ∫_(G^E) f(U) dH^E(U)
     = ∫_(G^(|V|-1)) ∫_(G^(|E|-|V|+1))
             f(reconstruct(g,X)) dH^(off)(X) dH^(tree-g)(g).

For any Borel integrable **gauge-invariant** f, f(reconstruct(g,X))=f(X_tree=1,X_off), hence

    ∫_(G^E) f(U)dH^E
      = ∫_(G^(E\T)) f(tree=1,X_off)dH^(E\T).

The Haar measure factor is **exactly one** with normalized Haar. This is a group-measure statement, NOT a claim that the Euclidean local Faddeev-Popov determinant of Bałaban's *different nonlinear background gauge* is one. The rooted tree gauge is complete and has no residual rooted ambiguity; a constant gauge rotation at the root still acts on the off-tree variables by simultaneous conjugation when global gauge is not fixed.

This theorem works for every finite periodic lattice size and every compact G; it uses group multiplication and normalized Haar alone, not the original 2023/2026 SU2 Q8 finite subgroup calculation.

## 3. Full original Wilson source, 1/F/G/FG equality for every beta

At any original finite periodic 4D cutoff, take the ACTUAL full positive Wilson action S(U)=Σ_(all 6 L^4 original plaquettes)(1-ReTr P/N), and two authentic original gauge-invariant closed-plaquette deficits F and G. For arbitrary real beta≥0 and global real/complex marks s,t, the SAME original finite-source affine polynomial is

    K(s,t)=∫_G^E exp[-beta S(U)] (1+s F(U))(1+t G(U)) dH^E(U).

Since S, F, G, FG are individually gauge invariant, apply the tree theorem to EACH of the four original columns. Their original 1/F/G/FG masses, the common normalization, finite Wilson pressure, connected mixed log Hessian (where K≠0), and any other gauge-invariant Wilson loop expectation are EXACTLY unchanged:

    K_full(s,t) = K_rooted_tree(s,t) identically for all s,t,
    ∂s ∂t log K_full = ∂s ∂t log K_tree where K≠0.

Thus the **tree-gauge normalization contribution to the W0→W1 four-column error ledger is exactly zero**; no four-column eps0/epsF/epsG/epsFG is required for THIS gauge change. This does *not* imply an epsilon=0 comparison to actual CMP119/122 Eq.(1.71), whose background selection, constraints and R modifications remain unverified.

The true original R445 F19 pair W=U_0 V of links x→x+e and x+e→x+2e transforms

    W' = h_x W h_(x+2e)^(-1),
    V' = h_(x+e) V h_(x+2e)^(-1),
    U'_0 = W' (V')^(-1).

This is a commuting source/gauge diagram for all 64 original pairs, with all 896 spectators retained. **A fixed coarse W is NOT gauge invariant**; use the covariant conditional-family pushforward, not the false statement that individual K(W) is invariant at the same W coordinate. The global four columns are invariant after original coarse Haar integration.

For original side four L=4, |V|=256, |E|=1024, |T|=255 and |E\T|=769. The 64 original R445 pairs select 128 links, leaving 896 original interacting spectators; tree/off-tree and F19 pair/spectator are DIFFERENT partitions and must not be conflated.

## 4. Exact local acceptance (native original action + independent Haar quotient)

The locally executed, GitHub-byte-matched [source checker](../../scripts/check_ym_p0_original_wilson_tree_gauge_haar_and_os_20261124.py) uses exact SU2 quaternion Q8 matrices only as a NONCOMMUTING regression of the general group argument. It directly evaluates all 1536 genuine original side-four Wilson plaquette words for twelve seeded full 1024-link configurations, validates rooted gauge fixing and its inverse, checks all 64 R445 pair/midpoint covariance maps, and tests the ORIGINAL selected two y-z deficit marks at x=(0,0,0,0) and x=(0,0,0,2) after gauge transformation.

An independently exhaustive three-site four-edge double-loop Q8 gauge model checks the measure identity on ALL 8^4=4096 link assignments versus 8^2=64 tree-reduced values. Its positive, interacting 1/F/G/FG source moments are

    (K0,KF,KG,KFG) = (157/1024,31/256,31/256,53/512).

All four columns match exactly and the normalized mixed covariance is **1266/24649 ≠0**, so the test excludes accidental FG factorization. This SMALL-GRAPH control is not the original L4 action, and Q8 finite counting is not continuous SU(N) Haar. It verifies noncommutative orientation/inverse/counting; the general Haar proof is the separate triangular group argument.

**25,792/25,792 exact assertion groups PASS** on Python+SymPy 1.14.0, broken down as: 4 group, 8 graph, 72 rooted-gauge, 18,432 actual full plaquette gauge-covariance, 3,072 original R445 F19, 4,198 finite-group Haar quotient plus termwise Mayer checks, 6 independent OS finite-matrix negative-control checks. Git object **68fa75114f0ddccb686acb688b5a5a451da11515**, verified byte-identical to the executed local script. No kernel, CI or numerical continuous-Haar quadrature was invoked.


## 4a. Termwise original Wilson Mayer/W3 bare-source transport (stronger than a signed log)

Every *individual* original plaquette-factor label p is gauge invariant: for bare Wilson trace t_p(U)=ReTr(P_p(U))/N, the Mayer factor f_p(U)=exp(beta_p*t_p(U))-1 is a class function of its own original plaquette word. For **every** finite labelled subset S of actual original plaquettes, and every A∈{1,F,G,FG} built from the two globally unique original Wilson marks, define the genuine original-source coefficient

    z_(S,A)^full = ∫_(G^E) A(U) ∏_(p∈S) f_p(U) dH^E(U).

The rooted-tree theorem applies **separately to EACH** such product, not just to the complete four-column partition: \`z_(S,A)^full = z_(S,A)^tree\`. Thus any FINITE selected original factor-activity family \`C\` obeys exactly

    Σ_(S∈C) |z_(S,A)^full| = Σ_(S∈C) |z_(S,A)^tree|.

No triangle inequality loss, cancellation, changed link supports or gauge-volume normalization occurs at this step. Whenever a finite labelled Ursell/log coefficient is assembled algebraically from the same original z_(S,A) inputs, its value also commutes with rooted-tree gauge fixing, provided the exact same factor-incompatibility labels and normalization are retained. This is an **exact original bare Wilson Mayer representation identity**, not an absolute upper bound for that sum and NOT an identification of Bałaban's distinct R-modified, gauge-fixed CMP116 activities with these bare plaquette factors. On the genuine CMP119/122 renormalized W3 lane, the original-source activity map, absolute domination and physical rooted shell remain OPEN.

The independent full-enumeration Q8 two-loop negative-control fixture additionally verifies **32/32 exact source-matched individual coefficient equalities**: all 2^3 bare Wilson Mayer interaction subsets times each of 1,F,G,FG under normalized 4096-configuration full Haar versus normalized 64-configuration rooted-gauge Haar. This increases local acceptance from 25,760 to **25,792**, with committed script blob **68fa75114f0ddccb686acb688b5a5a451da11515** byte-identical to the new executed file. The abstract compact-Haar theorem is independent of Q8.

### Current master-only W3 source donors, not missing theoretical producers

Actual current \`master\` already holds \`Docs/physics/YMClayOriginalWilsonMarkedMayerAbsoluteEntropyCut20261123.md\` (one labelled factor-connected 4D Wilson Mayer activity family and rooted-tree combinatorial majorant; **explicitly not the full Ursell log W3**), \`Docs/physics/YMClayOriginalSUNW3SingleOmittedPlaquetteCensus20261123.md\` (one-outside-plaquette Haar-leaf invisibility, original intermediate time-one mark variance and collective cube-flip counterexample), and \`Docs/physics/YMClayOriginalSUNW3CubeFlipTwelveCouplingExact20261123.md\` (24 actual distinct original twelve-interaction connected multivariate derivatives, 98,304 parity checks). These are provenance-backed *master donor files*, absent from the inspected #1536 head but already in its target \`master\`: **do not duplicate or blindly cherry-pick**. They strengthen the bare original W3 source, yet supply neither full homogeneous running-beta Ursell absolute sum nor the literal CMP119/CMP116 physical rooted charge. Current original real affine strong-coupling marked W1 Dobrushin also already exists on master for beta≤1/72 with a row bound 13/25; it does not survive a beta(a)→∞ weak-coupling trajectory by that same estimate.

## 5. Same-H reverse spectral theorem: no universal vector prefactor needed

The existing \`BalabanClayDenseCoreSpectralGapExact\` and \`YMPaper3RowCToDenseCoreGapAdapterExact\` already own the abstract spectral/dense-core consumer. The following is the precise *classical spectral-theorem* sufficient condition, useful for reducing the physical marked-W3 target and explicitly **not** a new interacting OS source.

Let the *actual same reconstructed OS Hilbert space* have nonnegative self-adjoint H with vacuum Ω; let D⊂Ω^⊥ be a linear dense centered core. If one fixed positive physical m satisfies

    for every v∈D,  <v,e^(-tH)v> <= C_v exp(-m t), all real t>=0,

where each C_v<∞ may depend on v, then H on Ω^⊥ has no spectrum below m. For ε∈(0,m), let P_ε be the spectral projection onto [0,m-ε]. Positivity gives

    exp[-(m-ε)t] ||P_ε v||²
      <= <v,e^(-tH)v> <= C_v exp[-mt].

Taking t→∞ gives P_ε v=0 for each dense core vector, hence P_ε=0 throughout Ω^⊥ by boundedness, then ε→0 yields the spectral gap. A *uniform-over-v constant* is not required by this last spectral step; a **common exponent m**, physical-time meaning, one reconstructed H, and density ARE required.

Exact finite-matrix negative control in the same local checker: H=diag(0,1/3,2/3), Ω=e0 and a selected fast state e2 decays like exp(-2t/3), but unseen e1 decays exp(-t/3), defeating proposed m=1/2 until the core includes e1. This is not a Wilson Hamiltonian. Source-precedence: \`YMOriginalD2FullSectorBidiDetection20261121.md\` already contains the selected-observable insufficiency; the present spectral argument refines the needed **prefactor quantifiers**, not the source gap.

## 6. Exact remaining mathematical lemmas and producer→consumer routes

| Gate | Precise mathematical payment | Owner / status |
|---|---|---|
| **T0** | finite original all-G rooted tree measure identity and global 1/F/G/FG exactness | this note + existing original Wilson/F19; **MATHEMATICALLY PAID, SYMPY native controls PASS**, Agda kernel not run |
| **T1** | source-chosen Bałaban CMP98/109 nonlinear Q_B, Omega/Lambda/S scale history and actual fixed physical beta(a) | existing CMP98/109, CMP119 Section2/P10/P11 owners; **OPEN** |
| **T2** | original rooted tree gauge ↔ Bałaban's selected background/FP/ghost/Jacobian, source R-modified localized Eq171 constrained T, preserving actual native action and complete E/R/B/V | \`BalabanClayGate4TreeBackgroundSliceTransitionExact\`, Eq171 physical realization/Gate4; **OPEN** |
| **T3** | genuine CMP119 2.18-2.22 ordered source histories/residual produce same normalized original 1/F/G/FG functional, or all four physical source-relative errors including differentiated residual | existing \`BalabanCMP119Equation218FactorizedFunctionalDensityExact\`, marked approximation compiler, original candidate Eq171; **OPEN** |
| **W1** | exact full-original marked mixed-log has zero **tree-gauge** error | this note; **PAID (gauge change only)** |
| **W2** | actual CMP116/R573 Wilson-to-polymer sourced connected-cluster identity with BOTH global marks, S internal T | existing W1/W3 source-first consumers; **OPEN** |
| **W3** | termwise ABSOLUTE original source-connected weights, rooted shell entropy/large-field budget with uniform physical rate and prefactor for running beta(a), all cutoffs and volumes | CMP116 R416/R444, R573/R574/R576/R556; **OPEN** |
| **OS1** | original interacting infinite-volume/refined R4 Schwinger family, reflection positivity, tightness/noncollapse on one physical sector | original E1 and #1535 finite reflection donors; **OPEN** |
| **OS2** | actual same H_OS strongly continuous physical-time semigroup, dense centered gauge-invariant local-word core, all-core common-exponent clustering | R551/R552, Paper3 dense-core same-object adapter; **OPEN** |
| **OS3** | physical fixed-SI m>0 and dense-core projection argument on SAME H_OS | classical theorem above and existing \`BalabanClayDenseCoreSpectralGapExact\`; **conditional consumer proven; physical source OPEN** |

**Do not promote:** T0 does NOT pay T2/T3; global four-moment equality does NOT dominate a termwise absolute CMP116 activity; a finite noncommutative Q8 measure does NOT prove a continuous non-Abelian RG step; a selected Wilson word, one finite transfer gap, or an assigned eigenvalue does NOT pay the dense same-H OS continuum gap. Clay E1/D1/D2/N1/G1 remains OPEN. Source attribution Wilson/Haar, Bałaban CMP98/99/109/116/119/122, Osterwalder–Schrader, spectral theorem and existing DASHI proof owners.
