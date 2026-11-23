## 6 November 2026 correction — the FINITE analytic-J identity is NOT a new Clay leaf

The previously reported "formal jet -> actual analytic mixed derivative" should not be presented as an independent, unproved *mathematical* theorem for bounded finite original Wilson marks. The rigorous finite continuous-compact-Haar proof was already written in [YMClayR320BoundedMarkedSourceLemma20261106.md](../physics/YMClayR320BoundedMarkedSourceLemma20261106.md): for each finite original Wilson Gibbs law and bounded local marks F,G, M(s,t)=E_mu exp(sF+tG) is holomorphic on a uniform nonzero neighbourhood, and (d_s d_t log M)(0,0)=E_mu(FG)-E_mu(F)E_mu(G). For |F|,|G|<=2, |s|+|t|<log(2)/2 is sufficient. Uniform *analyticity* is not uniform *spatial clustering*.

**New genuine same-source finite integration proof:** `YMClayOriginalWilsonAffineMarkedPartitionExact.agda`, with `originalAffinePartitionIsExactNumeratorPolynomial`, directly constructs the ORIGINAL unnormalized Wilson product-Haar marked integral
`Z_aff(s,t)=int exp(-S)(1+sF)(1+tG) dH`
and proves equality to `Z_0+s N(F)+t N(G)+st N(FG)` using the EXISTING integration/numerator linearity theorems. The two source marks are the actual Wilson observables, not a second J oracle. Consequently the affine and exponential source have the same first and mixed derivatives at zero by elementary bounded analytic differentiation. The existing `YMClayOriginalWilsonFiniteTwoSourceJetExact`, `BalabanObservableIndexedT5SourceMeaningRound403Exact`, `NormalizedTwoSourceConnectedCumulantExact` and `BalabanCMP116SelectedJCommonDomainRound327Exact` already own the coefficient, covariance, observable-index and common-domain compilers. **Status:** original integral polynomial equality SOURCE-WRITTEN, not Agda-kernel-accepted; bounded exponential derivative analytic theorem proved in source-facing mathematical dossier, not yet a native Bishop/Agda differentiability proof.

**Do not retain finite derivative calculus as a new independent physical gap.** The next source-specific mathematical obligation is different: identify the COMPLETE renormalized CMP119/CMP122 effective density and exact selected marked insertion with the actual original Wilson source at each scale (including E/R/B/V, boundary/ghost normalization), then instantiate CMP116's published *localized* mixed-source estimate on those precise original supports, with a cutoff- and volume-uniform physically calibrated distance/rate. An arbitrary compact plaquette has a bounded analytic source; that alone says nothing about decay between two distant plaquettes. Existing R342/R344/R467/R482 and literal two-Wilson quarter-dyadic authors compile the subsequent bound/gap only after those physical estimates and limit semantics are supplied.

**Remaining maximal physical cut:**
- `Y.01/R445`: original Wilson positive-Haar/Gibbs source ↔ actual CMP119/CMP122 complete E/R/B/V/ghost/background density and RG pushforward, including reflection-compatible crossing R-terms, all changing cutoffs/volumes.
- `Y.02/R320`: select the original two local/loop insertions as admissible CMP116 analytic marks of *that same renormalized density* with exact root/support and source-time calibration. The generic finite mixed derivative is ALREADY accounted for.
- `Y.03/T5`: pay original cutoff/volume-uniform connected rooted-shell response, quantitative physical RG drift/defect tails and the same expectation limits; reflection positivity through the physical R-operation.
- `Y.04/R333/Clay`: reconstruct one noncollapsed four-dimensional Euclidean/OS theory with same H, dense local physical sector, strict positive gap in real units, nontriviality and the externally prescribed compact simple gauge-group scope.

No independent abstract J calculus, generic new KP/RG proof or artificial coarse Wilson measure is an admissible replacement.

---

## 2026-11-06 follow-on: finite original Wilson two-source jet (Y.01/Y.02)

**Golden source:** `DASHI/Physics/YangMills/YMClayOriginalWilsonFiniteTwoSourceJetExact.agda`, in parent [PR #1444](https://github.com/chboishabba/dashi_agda/pull/1444). **Independent exact reference:** `scripts/check_ym_original_wilson_two_source_jet_reference.py`. Canonical TOE import, dedicated physical root `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda`, and targeted Agda CI now name the two finite source owners. The physical root is deliberately not `--safe`, because the legacy real/Haar analytic authorities are a transitive proof boundary. No Agda kernel or transitive trust receipt has been observed.

| Exact ID | Source term | Status and remaining physical payment |
| --- | --- | --- |
| `Y.FIN.01` | `originalWilsonDensityIsSelectedWilson`, `originalWilsonPartitionIsSelectedProductHaar`, `originalWilsonFiniteIntegrationLaws`, `originalWilsonUnitNumeratorIsPartition`, `originalWilsonInsertionNumeratorAdd`, `originalWilsonExpectationOfUnitIsOne` | Source-written: literal changing-cutoff SU(N) Wilson/Gibbs density and partition are anchored to the *same* previously constructed finite product-Haar measure; finite numerator additivity and unit partition follow from existing cylinder algebra. The unit-normalization proof additionally takes an explicit positive-denominator division-cancellation law; one-link compact Borel Haar realization is still an explicit input. |
| `Y.FIN.02` | `originalWilsonMomentAlgebra`, `originalWilsonNormalizedJet`, `originalWilsonLiteralJetDirections` | Source-written: define the formal two-source coefficients directly from one original finite Wilson normalized expectation; no independent moment/covariance object. The *analytic derivative* of the actual continuous-Haar source functional is not inferred. |
| `Y.FIN.03` | `originalWilsonMixedJetIsSameFiniteCovariance`, `originalWilsonMixedJetIsOriginalConnectedCumulant` | Source-written: literal finite formal mixed-log jet equals the same Wilson connected covariance by the original cumulant compiler. Kernel acceptance pending. |
| `Y.FIN.04` | `check_ym_original_wilson_two_source_jet_reference.py` | Exact rational BIDI reference: 19,683 exhaustive three-state cases and six simultaneous relabelings; changed-measure negative control rejected. This is not an SU(N) Haar integration or Agda check. |

| `Y.FIN.05` | `YMClayOriginalWilsonR445R320TwoSourceSameFamilyExact.originalVariableN3IsNativeR445FineMeasure`, `originalN3CumulantIsNativeBlockedFineCovariance`, `originalN3LiteralMixedLogJetIsNativeBlockedCovariance`, `originalN3LiteralMixedLogJetIsActualR320PushforwardCovariance` | Source-written: at actual side-four n=3 the variable-cutoff Wilson measure is definitionally the original R445 1024-link fine Gibbs law. Both source marks pull back along the original non-Abelian native block; the finite jet equals the actual *weighted* R445→R320 pushforward covariance. No bare-coarse Wilson-law assertion or analytic CMP116 source bound. Kernel pending. |

**Revised original physical max-cut (do not promote from Y.FIN):** `Y.01` identify the entire real Wilson/gauge-fixed E/R/B/V/ghost/counterterm source with the selected CMP119/122 density/physical T-operation at every renormalization scale, not just the original finite Wilson action. `Y.02` prove that selected positive-time gauge-invariant local/loop insertions are admissible CMP119/116 analytic J directions, identify the genuine differentiated `log Z` with this formal jet, and preserve root/distance/normalization. `Y.03` derive *actual* cutoff/volume-uniform source decay, RG/continuum tails and reflection-compatible limits. `Y.04` construct the same limiting OS Hilbert/Hamiltonian and quantitative nontriviality/Clay scope. Reuse the CMP119/122/116, R344/R467/R482, Bishop/T5 and original Wilson–Gibbs owners rather than copying them.

**Acceptance:** new formal theorem = `SOURCE_PENDING_AGDA`; reference arithmetic = `VERIFIED_REFERENCE`; original CMP116 source applicability and physical estimates = `OPEN_PHYSICAL`. CI is a checker command, not a green receipt. Parallel-checker exact-head execution and transitive axiom audit remain required.

---


## 6 November — canonical R344 shared marked CMP116 half-rate direct weld

The *existing* `BalabanCMP116SharedMarkedDirectCalibrationRound344Exact` proves the shared-Hessian shell's conditional geometric $\frac14 C_H 2^{-d}$ bound, with selected physical source distance/time and (C_H≤1) as proof inputs. Two new terms `sameOriginalSharedMarkedHalfRateFiniteDecay`, `sameOriginalSharedMarkedHalfRateYieldsGap` (R344→R342→R467→R482) are source-written in `YMClayCMP119122116SelectedProducerWeldExact.agda`, Agda unverified. The actual original Wilson-Haar marked J applicability, uniform physical rate and OS limit are not derived from a name match. Exact four-cut Y.01–Y.04 is in `Docs/physics/YMClayCMP119116122OriginalSameSourceMaxCut20261106.md`. Source contract audit now 12 donor owners / 6 bridge proof terms.


---

## 6 Nov source-first CMP119/116/122 BIDI max-cut

[Full exact source-owner audit and physical BIDI falsifiers](../physics/YMClayCMP119116122OriginalSameSourceMaxCut20261106.md). An original selected finite beta history + CMP119 localized density now produces in one source-written Agda bridge both exact beta coupling and source-native CMP109/116 effective potential. A literal selected R342 source similarly generates finite R467 physical-envelope covariance and R482 rate-based positive gap, so there is no requirement to separately re-prove source KP, normalized expectation derivatives, arbitrary energy-positivity token, or R454/R455 historical detours. New file `YMClayCMP119122116SelectedProducerWeldExact.agda`, static source contract `scripts/check_ym_cmp119116122_same_source_contract.py`; compiler receipt pending.

**BIDI physical acceptance:** FWD 119→122→116 on original Wilson density, local inserted J, physical time source; BWD 116→same original action/beta and original Haar; CMP122 crossing reflection Gram PSD (pointwise exponential source bound is not enough); original T5 noncollapsed continuum/OS same H and all-G. Four indivisible original witness cuts Y.01–Y.04 are mapped into the active phased deliverables. Existing source theorems still require their hypotheses, but these must not be counted as independently missing *generic proofs*.

---

## 6 November 2026 — same-original-Wilson constructive 4D continuum steelman / BIDI max-cut

**Primary theorem proposal:** [YMClayConstructive4DContinuumSteelman20261106.md](../physics/YMClayConstructive4DContinuumSteelman20261106.md). It explicitly derives the hypothetical nontrivial 4D continuum from ONE original compact-simple-G Wilson family, not six unrelated records, and proposes source-specific bounds for same-observable UV Cauchy limits, IR/crossing tails, literal CMP116 mixed-J decay, OS reconstruction and non-Gaussian survival. The existing R443/R445/R320/R333 owners are reused; unification #1460 remains downstream.

**New golden producer:** `DASHI/Physics/YangMills/YMClayRGLossBudgetToNonGaussianExact.agda` (source-written, **Agda kernel pending**): `finiteRGLoss`, `referenceChargeBelowCurrentPlusLoss`, `referenceRGUniformNoncollapse` from a reference `eta+B≤c0` and actual `c_n≤c_{n+1}+δ_n`, `sum_{k<n}δ_k≤B`; `asOriginalT5Nontriviality` instantiates the EXISTING T5 uniform fourth-cumulant lower theorem with this **derived** finite bound; `continuumRGChargeIsNonzero` imports existing T5 nonzero result. This does not construct the original source-specific charge/limit, and cannot assign a fictitious fourth-cumulant sign.

**Physical RG insight to test, not assert:** after actual 4D marginal and source renormalization, an original Wilson/CMP119/122 one-step residual may obey `δ_n≤A/((n+1)(n+2))+C 2^{-(n+1)}+h_n`, `Σ h_n≤H`; this gives `q≤q0+A+C+H<1` via the *existing* `YMClayPhysicalRGDriftToUniformInfluenceExact`, while bare O(g²) harmonic sums diverge. The actual Ward cancellation/marginal subtraction and full large-field/marked-J source error remain to be proved.

**Executed independent exact rational BIDI controls** (all illustrative, NOT physical): 192-step RG noncollapse, 64 exhaustive bounded charge configurations and 5 negative cases; 4×4 transfer Hankel Gram PSD, 128-step noncollapse and 7 false-positive negative controls; the UV rational n^-2+geometric+holes sum checked at depths 1,2,4,8,16,64,256,512, with a divergent harmonic control. The fixture `q0=1/4, A=1/16, C=1/32, H=1/64` gives `q=23/64`; NO Wilson measurement or Agda acceptance is inferred. New scripts `check_ym_rg_noncollapse_steelman.py`, `check_ym_clay_continuum_bidi_controls.py`, `check_ym_marginal_subtracted_uv_tail.py` committed and targeted by CI. Golden TOE root imports the new Agda module.

**Exact deliverable IDs (do not rename; promote only with physical proof receipts):**
- `CLAY4.F1`
- `CLAY4.A1`
- `CLAY4.A2`
- `CLAY4.A3`
- `CLAY4.B1`
- `CLAY4.C1`
- `CLAY4.C2`
- `CLAY4.D1`
- `CLAY4.D2`
- `CLAY4.D3`
- `CLAY4.E1`
- `CLAY4.E2`
- `CLAY4.E3`

**Status:** `CLAY4.D2` source-written mathematical compiler, Agda pending; `CLAY4.D3` derived conditional transport to T5, Agda pending; `CLAY4.F1` source-written original closed 1024-label candidates, kernel pending. `CLAY4.A1/A2/A3/B1/C1/C2/D1/E1/E2/E3` are physical same-source analytic or semantic construction work, NOT realized original continuum theorems. No CLAY endpoint acceptance claimed.

**Highest alpha execution order:** original one-step marked source/Dyadic Cauchy `A1/A2` and two-marked physical CMP116 shell `B1/C1/C2` in parallel, then one fixed-scale nonGaussian `D1/D2/D3`, exact original RP/OS/E(4) `E1/E2` and per-G `E3`; native `F1` kernel independently. Fail on unproved physical input rather than selecting a toy model.

---

## 2026-11-06 — YM proof-source / RG budget supplement

See [phase-specific exact update](YMClayExecutionPhasesDeliverablesExactLemmas20261106.md). F1 three original 1024-link equality proof attempts source-written, **no Agda receipt**. New original physical-cube RG arithmetic derives q=q0+B, with 128-step exact rational reference but actual continuous SU(N)/CMP116/OS physical coefficients and compact-group coverage OPEN. Files: `YMClayNativeClosedThreeEqualitiesCandidateExact.agda`, `YMClayPhysicalRGDriftToUniformInfluenceExact.agda`, `YMClayRGDriftOriginalGibbsInstantiationExact.agda` and `scripts/check_ym_rg_drift_budget_reference.py`. #1460 remains separate physical observer/KK lane; no child import. Full source contracts in `Docs/physics/YMClayPhysicalCubeDobrushinCMP116Transport20261106.md`.

---


---

## 6 Nov 2026 — replacing weak bare-link Dobrushin with fixed physical cube

The precise high-alpha analytic strategy, source crosswalk and dimensional donor separation now live in [YMClayPhysicalCubeDobrushinCMP116Transport20261106.md](../physics/YMClayPhysicalCubeDobrushinCMP116Transport20261106.md). The prior (18\tanh(12\beta)) single-link estimate is merely a very conservative sufficient high-temperature criterion, irrelevant to weak-coupling continuum. The actual new target is a **uniform strict Dobrushin–Shlosman/Perron block conditional coefficient** at fixed physical `ell` for the original selected R445 Wilson-Gibbs pushforward, or a directly selected CMP116 rooted-polymer envelope for R467. The existing `BalabanClayUniformPerronContractionExact` already proves stagewise finite diameters do not imply uniform contraction. The exact q→m transport then feeds existing R479 and T5 same-H OS consumers, requiring full continuum/OS/nontrivial all-group physical data. Finite Gibbs compiler added, physical q not established.

---

# 6 November execution/steelman addendum

The canonical active phase/deliverables table is [YMClayExecutionPhasesDeliverablesExactLemmas20261106.md](YMClayExecutionPhasesDeliverablesExactLemmas20261106.md). Phase F1 has moved from an unstructured large closed-conversion attempt to source-written structural membership/bubble/sort proof, leaving the two exact native target-selectability certificates and one length equality as next gates. The generic sorter theorem requires `AllSelectable`, which is a genuine proof premise; do not hide this as a closed C3 or blocking vector identity. Local 5,914+2×1024 selection-trace checks are finite Python reference, not Agda acceptance. R443 physical continuous Haar, selected CMP119 action, R445 uniform RG, R320 CMP116, R333 OS and Clay remain analytically unpaid.

---

# Yang–Mills physical max-cut: exact lemma atlas, steelman and bidirectional audit

**Snapshot:** 4 November 2026. Independent four-dimensional Yang–Mills/Clay PR #1444 only. The TSVF/(3,1)/KK worker owns #1460 and is **not** an upstream premise for Clay Yang–Mills. The authoritative current 66-row producer ledger is `Docs/roadmaps/YMClayCurrentExactLemmaLedger20261103.md`. The original 219-field inventory remains byte-preserved. Every claim below is either an existing source-owned theorem/candidate, a precise outstanding type, or a deliberately labelled *candidate mathematical statement*. No open physical result is promoted to proved. **Agda kernel acceptance is pending on all new sources.**

## 0. Two critical semantic facts discovered by the exact source audit

**(a) The 219 field names are not 219 propositions.** Every one of the original 219 Agda fields is literally declared `name : Set`. A value of such a field chooses a type but does **not** provide a proof of the type. Both original owner blobs have been independently checked field by field: 219/219 matches. This is a source-complete named *cutset inventory*, not a proof-grade exact-lemma collection. No source owner or producer ID can be counted as discharging an individual field without a **chosen, externally meaningful proposition, literal type equality, proof, same-object map, and verified transitive trust**. The safe source `YMClayProofRelevantFieldAnchoringSafeExact.agda` constructs an empty chosen type as a negative control and provides anchored *bidirectional transport* ONLY for a fixed physical predicate and a proof.

**Concrete original-source countermodel:** §YMClayOriginalCMP109NamedSetNoPromotionExact.agda§ imports the actual original §CMP109Round6Cutset§ and constructs a legitimate instance selecting the empty §NoProof§ type for all five original named fields. Its §actualOriginalCMP109CannotUniformlyProveChosenHolonomy§ rejects any proposed universal proof of the chosen holonomy type; §originalCMP109HolonomyProofGivenPhysicalAnchoring§ transports only a proved predicate with exact same-§Y§ type equality. This is not a generic field-name analogy: the five original declarations are used verbatim. Agda kernel acceptance remains pending.

**(b) The final Clay contract is parametric.** `YangMillsClayProblemContractExact.ClayYangMillsSolution` is indexed by an *arbitrary* `ClayProblemVocabulary`, whose pre/post/invariant witness families are freely chosen `... → Set`. `YMClayParametricVocabularyNoClayPromotionExact.agda` supplies a trivial vocabulary with a record inhabitant but no physics; hence a *parametric* endpoint record is not automatically an externally valid Jaffe–Witten solution. The Round78 compiler is a valid relative type-theoretic sufficiency map on one `LiteralYangMillsConstruction Y`, but its **15 carrier sets, 34 semantic predicates, 13 data fields** and Clay 8/9/11 requirements must be anchored to the authoritative physical objects/definitions. It is illegitimate to discharge those predicates by choosing them all to be inhabited trivially.

This requires three new independent, still-open gates:
- **SEM.P01** — For each selected original field: chosen same-`Y` physical proposition, exact equality to the original chosen type, and kernel-accepted witness or proof-relevant redundancy implication.
- **SEM.P02** — Independently establish that the actual 15 carriers and 34 semantic predicates describe compact simple groups, Euclidean ℝ⁴, real QFT observables, accepted OS/Wightman axioms, physical positivity/scale, and the genuine spectral-gap predicate (not arbitrarily interpreted `Set`).
- **SEM.P03** — Construct verified *sufficiency edges* from the physically anchored needed fields into the five Round78 inputs. A converse (every physically valid Clay solution must use our RG route) is **not** a requirement and is unproved.

The machine-readable **219-row forward/reverse candidate-gate index** `Docs/roadmaps/YMClay219ProofRelevantBidirectionalAudit20261104.json` pins exact source record/field/line/blob, 66 gate producers and every unproved physical statement. The root countermodels are new source modules; nothing is marked Clay completed.

## 5 November 2026 R443 same-original weighted C3 and all-group bidi continuation

**New R443.F09 physical-source implication, not an unproved action theorem:** `YMClayOriginalWilsonC3WeightedHaarTransferExact` defines the weight **literally** as `Variable.periodicSUNGibbsDensity theory traceData exponential 3 betaFine (Codec.decodeOriginalBonds Torus.four links)` on original `Vec Link 1024`. Given the already isolated `Sort.constructedNativeC3CanonicalLabelGoal` and a **separate pointwise equality on that very weight** `ActualOriginalC3GibbsActionInvariant`, it derives:
[
\mathcal N_{\rm fine}(F\circ C_3)=\mathcal N_{\rm fine}(F),\qquad
\mathbb E_{\rm fine}(F\circ C_3)=\mathbb E_{\rm fine}(F)
]
by the original `Product.productHaarPermutationInvariant` plus **original 1,024-link** `Congruence.productIntegralCongruent`, with the same partition and chosen division. The source also now proves direct definitional identification of the **actual selected** `Constructed.actualPeriodicProductMeasure` finite Wilson–Gibbs cylinder numerator with the original 1,024-vector numerator, and derives the original physical partition/normalized-expectation equality using `mulOneʳ` and **all-link** Haar congruence; no auxiliary Gibbs measure or independent partition enters. This is a useful conditional result: the two hard leaves are kernel-accepting the native C3 label equality and **proving the literal CMP119 E/R/B/V physical action C3 covariance**. The latter is not established by unweighted C3/Haar permutation, by an arbitrary gauge symmetry, or by an SU(2) rational Wilson-only reference. Reuse existing `YMClaySide4SpatialC3WilsonNaturalityExact`, `YMClaySide4RationalSU2C3WilsonTraceExact`, `CMP119FlatSide4SpatialC3FieldCovarianceExact` and `YMClaySUNVariablePeriodicGibbsGaugeExact` with their correct carrier boundaries rather than substituting a new action.

**Independent executed exact 4D Q8 reference:** `scripts/check_ym_original_c3_weighted_wilson_q8.py` tested 32 random original (4^4\times4=1024)-bond fields; Wilson plaquette action invariant under the literal time-fixed spatial (C_3), local gauge action invariant, and (C_3^3=\mathrm{id}). All 32 deliberately spatially anisotropic plane-weighted Wilson actions violated (C_3) invariance. These checks concern **the finite pure Wilson action for Q8**, not the full selected real CMP119 terms, compact Borel SU(N) Haar, Agda acceptance or continuum physics.

**New SEM.P02 no-vacuum scope theorem:** `YMClayCompactSimpleScopeBidiNoVacuitySafeExact` source-writes a genuine `--safe` empty-group universal-proof counterexample, requires an actual externally chosen compact-simple group witness, and proves **both** transports
[
(\forall i\in I,\ P_I(i))\Longleftrightarrow(\forall g\in G_{\rm ext},\ P_{\rm ext}(g))
]
ONLY when a checked group-index equivalence (G_{\rm ext}\leftrightarrow I) and pointwise *physical predicate equality* are supplied. Those semantic witnesses are not constructed. **SU(N) alone is not the full class of compact simple Lie groups**, so one SU(2)/SU(N) result never automatically fills the external all-group Clay scope.

**Updated source/trust counts:** 67 distinct producer rows after R443.F09 (66 previous), 219 unchanged bare-`Set` source field declarations, 521 strictly candidate search links and zero newly kernel-audited field witnesses. Exact-head Agda unavailable; no clean kernel receipt. R445 physical weighted source decoder, cutoff-uniform R320 and same-OS R333 gap remain OPEN. These new modules are SOURCE-WRITTEN, not source-proved in a compiler.

## 1. What the selected final compiler actually requires

The literal source term is `BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact.literalClaySolutionFromTopDownThree` with exactly **one** same construction `Y` and FIVE inputs, not just "three" unchecked objects:

| Literal Agda input | Exact interpretation | Status |
|---|---|---|
| `Five.LiteralClayStructuralBase Y` | Actual compact simple gauge group family, actual 4D Euclidean target, correct parametrisation | OPEN physical / SEM |
| `UVToContinuumYM Y` | Same physical finite-cutoff RG and continuum Schwinger family | OPEN R443/R445 |
| `SameHamiltonianPhysicalMassGap Y` | Strict positive physical gap of the same OS Hamiltonian | OPEN R320/R333 or direct spectral |
| `SameFamilyLocalFieldsOPEStressWard Y` | Curvature local fields, OPE, Ward stress tensor on **that** continuum Y | OPEN CLAY.P01/P02 |
| `StandardSameHGaussianNontrivialityConsequence Y` | Source proof that selected gap and selected fields exclude a noninteracting/Gaussian theory | CONDITIONAL / requires actual same-H physics |

The source constructor gives a parametric `ClayYangMillsSolution (Top.literalClayVocabulary Y)` **if** those five types are inhabited. This is forward sufficiency, **not** (i) inhabitation, (ii) an externally anchored interpretation, (iii) the converse implication, or (iv) a proof that the 219 historical named cutset choices are necessary for other possible physical solutions.

## 2. R443: exact mathematical and kernel-facing leaves

### F-C3: selected original 1024-label permutation, 1 closed theorem

Existing source producers: `YMClayNativeC3SingleVectorPermutationCertificateExact`, `YMClayNativeC3AdjacentSortProgramExact`, `YMClayFiniteNativeAdjacentWordInverseExact`.

1. **R443-C3-01**: Kernel-accept the original bond equality decision and canonical distinct complete 1024-bond enumeration, consistent with `Codec.decodeOriginalBonds 4`.
2. **R443-C3-02**: Prove generic stable bubble-to-front `originalSortToTarget` correctness for **distinct complete lists with the same membership**, rather than relying on enormous normalization; prove its original `LinkPermutation` action and inverse law in the *same* codec.
3. **R443-C3-03**: Use C3 inverse/order-three to show the original target vector is exactly a reordering of original canonical bond labels; then discharge **ONE closed** `constructedNativeC3CanonicalLabelGoal`.
4. **R443-C3-04**: Apply the existing single-vector-to-all-vectors theorem to the actual original group-valued field and existing product-Haar symmetry. Weighted C3 invariance additionally needs same **physical Wilson/CMP119 action** invariance, not only the unweighted Haar permutation.

The independent original 46,592-adjacent-swap Q8/native reference is **not** a kernel proof. A proof-relevant generic sort theorem may be cheaper and more robust than huge `refl`.

### P-Haar: real compact group and measure (R443.P01–P05)

5. **R443-H01**: Exact chosen compact **matrix** group SU(N) with all required compact simple G scope, finite dimensions, determinant, topology, Borel sets, correct real/Bishop backend and trace/adjoint identification on the same original link carrier.
6. **R443-H02**: Genuine regular normalised Haar probability `H_G` on each chosen compact group, with left/right invariance, measurability and integrable test algebra (e.g. continuous/bounded cylindrical Wilson functions), **not** a functional on arbitrary real-valued maps stipulated by an uninstantiated interface.
7. **R443-H03**: Product Haar, Fubini/reindex/strict positivity on selected nonnegative continuous cylinder and weighted Gibbs tests; same-original finite volume/plaquette density and partition `0 < Z_{a,L} < ∞`, with measurable denominators.
8. **R443-H04**: Original CMP119 six-plane trace, E/R/B/V nonlinear action, source constants, prescribed boundary/counterterm structure and actual one-step physical real-action correspondence. C3 covariance must act on this same literal density.
9. **R443-H05**: Explicit selected source data transports the **one-link abstract Haar interface** and integral algebra of F13–F22 into the constructed continuous test class, proving that every integrand used is in the class.

**Steelman:** compact Haar existence is classical, so its abstract mathematical existence should not be counted as a newly open Clay research theorem. The **actual Agda constructive/carrier/measurable-integrand weld** and the nonperturbative physical Gibbs estimates remain unpaid. Do not import a theorem about *another group*, another real carrier, or all-function fake integration by name alone.

## 3. R445: from finite weighted density to actual physical all-scale continuum

### F-Decoder: precisely two remaining closed selected finite equalities

Sources: `YMClayNativeSideFourPairSpectatorSortProgramExact`, `YMClayNativeSideFourPairDistinctCertificateExact`, `YMClaySUNWeightedDisjointPairFibreReparamExact`.

10. **R445-D01**: Kernel-accept the actual 64 coarse positive bonds, 128 original selected distinct ordered fine bonds and 896 actual complementary original bonds, including original cyclic coordinate endpoints.
11. **R445-D02**: Kernel-accept `originalPairSpectatorLengthGoal`: selected pair+complement enumeration has original length **1024**.
12. **R445-D03**: Kernel-accept `originalPairSpectatorCanonicalLabelGoal`: the constructed native `LinkPermutation 1024` takes the original codec's label vector to that exact pair+spectator vector. This must use the SAME `Codec.decodeOriginalBonds 4`, not merely a list of integers.
13. **R445-D04**: Prove the original product Haar integral under the selected full bond-field/Vec decoder equals the reindexed nested 64-pair+896-spectator integral **for every selected physical Wilson–Gibbs integrand**.

### F-Density: actual original Gibbs to derived density, not bare Wilson

14. **R445-W01**: Identify the exact original 1024-link `w_{a,L}(U)=exp[-S^{CMP119}_{a,L}(U)]` (and real scalar/exponential backend) with the weighted integrand of F19 after D04, including all 896 spectator couplings. No drop of spectators from a **weighted** measure.
15. **R445-W02**: Prove source-matched equality of the **physical** Gibbs blocked-cylinder functional and the derived actual coarse Haar effective density for a **separating, integrable class** of cylinder tests F:
   
   \[
   \mathbb E_{\mu_{a,L}}[F\circ B]
     =\frac{\int_{G^{E_{\rm coarse}}}F(W)\,\rho_{a,L}^{\rm eff}(W)\,dH(W)}
                  {\int_{G^{E_{\rm coarse}}}\rho_{a,L}^{\rm eff}(W)\,dH(W)}.
   \]
   
   Independent F17–F22 already offer a **conditional finite** change-of-variables formula, strict positivity and scalar normalization; W01/W02 are the unproved physical same-object instantiation.
16. **R445-W03**: Show this defines the actual coarse pushforward Borel measure (equality on determining cylinder class), consistent fine conditional disintegration/reopening, measurable positivity and normalisation. On a finite discrete carrier, equality of all indicator tests is reversible; constants alone are not.
17. **R445-W04**: Define the *actual* effective action `S_eff=-log ρ_eff` where positive, control its gauge/OS transformations, locality/nonlocal tails and counterterms. Do not equate `S_eff` to the bare Wilson plaquette action: integrating coupled fine links generically creates new interactions.

### P-RG, P-Limit: actual changing cutoff/volume and bounds

18. **R445-R01**: All-M,L original periodic endpoint/holonomy compatibility, source-matched cylinder consistency and reflection-compatible blocked-link maps (R445.P01–P03), with **full Gram reflection positivity** not merely positive weights.
19. **R445-R02**: Physical spacings `a_n→0`, volumes `V_n→∞`, tuned same generated bare coupling `β(a_n)` and same generated action, including UV asymptotic-freedom constants (R445.P05).
20. **R445-R03**: Uniform physical source measures' coercivity, tails/moments and observables' tightness, including entropy, geometry and surface/volume constants **independent of cutoff and required volume** (R445.P06).
21. **R445-R04**: Strong source-native RG map and quantitative contraction/Cauchy estimate compatible with reflection, gauge and effective counterterms; cylinder/projective consistency, gauge-invariant observables and correct operator renormalisation (R445.P07).
22. **R445-R05**: Tight finite and thermodynamic limits; unique/separating continuum Schwinger distributions, translation/O(4) covariance and OS axioms **on R⁴**, with no sequence/blocking-choice dependence where required (R445.P08).
23. **R445-R06**: Nontrivial physical limiting local observables, appropriate nonzero higher connected correlations / interaction witness, not merely a generic named fourth-cumulant Set (R445.P09). This also supplies part of T78-C and the external Clay problem.

**Steelman:** seek an all-scale proof of W02 and uniform RG estimates on the **actual** chosen YM source, not arbitrary exact finite entropy or symbolic density identities. The actual 4D continuum limit and uniform control are the main nonperturbative discovery debt.

## 4. R320 direct CMP116 source-native route and bidirectional gap interface

24. **R320-B1a**: Construct literal selected physical marked source insertions F,G (two independent J coordinates) in the *same* Wilson–Gibbs family, with common complex/real local analyticity domain and sufficient dominated differentiation (R320.P01–P02).
25. **R320-B1b**: Establish source-matched derivative-to-covariance:
   
   \[
      D_FD_G\log Z_{a,L}(J)\big|_{J=0}
        =\mathrm{Cov}_{\mu_{a,L}}(F,G)
   \]
   
   with normalization/contact terms correctly accounted, not an unrelated covariance theorem.
26. **R320-B1c**: Instantiate the existing CMP116 polymer/DFS/rooted-shell infrastructure on *those same differentiated sources*, with actual analytic radius, support and physical constants (R320.P03).
27. **R320-B1d**: Prove a **cutoff- and volume-uniform**, *physically scaled*, positive exponential envelope:
   
   \[
    |\mathrm{Cov}_{a,L}(F_x,G_y)|
      \le C_{F,G}\exp[-m_{\rm phys}|x-y|],
      \qquad m_{\rm phys}>0,
   \]
   
   on the relevant local operator family, including selected differentiation/source correspondence (R320.P04–P05). Constants cannot degrade as `a→0` or `V→∞`.
28. **R320-B2**: Identify the actual R279 differentiated finite snapshot and R280 `QuantitativeCorrelationDecayTrajectory` evaluation with the same original R445-derived covariance *for all required sources*, rather than merely similar formulas.
29. **R320-B3**: Transport that same correlation object through R445's *one* physical continuum-limit map (no new measure), preserving the physical envelope.
30. **R320-B4**: Construct the O(4) same-object transport from spatial local/smeared subgap-mode observables to temporal OS spectral correlations of the **same Hamiltonian**, with valid operator domains/units and density needed for the argument.
31. **R320-B5**: Instantiate the existing slow-versus-fast spectral contradiction with the actual OS null quotient, semigroup `e^{-\tau H/\hbar}` and physical local operator family; derive a positive rate if this clustering route is chosen (R320.P06).

**Pareto/bidi:** the direct source-native CMP116 B1–B5 path is *sufficient under stated conditions*, not necessarily the only route: a direct same-H spectral-gap proof can bypass this route, but must pay its own positivity, spectral and cutoff-uniformity hypotheses. The converse "one chosen observable clusters ⇒ full Hamiltonian gap" is false without a sufficiently rich/cyclic local family and justified spectral/O(4) identification.

## 5. R333 and Clay: exact physical OS, same H and nontriviality

32. **R333-OS1**: Prove RP for the actual selected finite Wilson/CMP119 action on its gauge carrier, including boundary/counterterm components. For all supported positive-time tests `F_i` and complex coefficients:
   
   \[
      \sum_{i,j}\overline{c_i}c_j
         \,\mathbb E_{\mu_{a,L}}[\Theta F_i\,F_j]\ge 0.
   \]
   
   Reusing Osterwalder–Seiler's standard Wilson theorem is valid only after **the entire selected source satisfies the hypotheses**. Positive pointwise Gibbs density is not enough (R333.P01).
33. **R333-OS2**: Reflection-compatible all-scale blocking and RP-preserving thermodynamic/UV limit for the *same full Gram forms*, with test-class closure, OS bounds and gauge constraints (R333.P02).
34. **R333-OS3**: One noncollapsed OS null quotient and completed physical Hilbert space, vacuum, strongly continuous contraction semigroup and positive self-adjoint OS Hamiltonian on a common dense core, with physical time/energy units (R333.P03).
35. **R333-OS4**: Identify the selected Wilson transfer operator, original action's Hamiltonian variation and continuum temporal generator with **that same H**, including domains/cores and renormalized scale. Do NOT equate `e^{-\tau H/\hbar}` with the unitary `e^{-itH/\hbar}` at real positive times (R333.P04).
36. **R333-GAP1**: Establish a **uniform strictly positive gap in physical units** on the nonvacuum subspace, either via B1–B5 dense clustering and spectral transport or via a direct selected same-H lower spectral bound (R333.P05).
37. **R333-GAP2**: Prove the spectral bound survives thermodynamic and UV convergence for that same H with no subgap spectral pollution, correct vacuum multiplicity and physical energy calibration (R333.P06).
38. **R333-LOCAL**: Construct the local gauge-invariant field algebra, nonzero excitations, O(4)/Wightman locality/spectrum, renormalized OPE/stress/Ward package on the *same* theory, with non-Gaussian interacting witness (R333.P07 / CLAY.P01–P02).
39. **CLAY-ALL-G**: Uniformly provide an accepted theory and positive finite physical gap for **every prescribed compact simple G** (not just SU(2)), with correct quantum group-family instantiation; inhabit all five selected T78 roles on the same physical Y, prove SEM.P02/03 and independently compare to external Jaffe–Witten. Only THEN can an actual Clay-completion statement be considered.

## 6. Steelman/bidirectional implication table (no false iff)

| Proposed direction | Validity and missing hypotheses | Reverse direction / counterexample |
|---|---|---|
| Actual physical selected field proposition + proof + *exact type anchoring* → verified named field | Constructive transport provided by `YMClayProofRelevantFieldAnchoringSafeExact`, KERNEL PENDING | Bare field `Set` → proof: **FALSE** (empty-type countermodel) |
| Five T78 source-selected proof inputs → parametric `ClayYangMillsSolution` | Already source compiler, **conditional on actual chosen physical Y and valid semantics** | Parametric solution → external Clay: **FALSE** for freely chosen vocabulary; trivial vocabulary countermodel |
| Native C3 original label permutation + Haar → *unweighted* integration invariance | Valid if original Haar/reindex kernel are established | Unweighted Haar invariance → weighted CMP119 Gibbs invariance: **FALSE** without selected physical action covariance |
| Actual fine weighted fibre disintegration → coarse pushforward measure | Valid on determining selected measurable cylinder class + same original decoder, original physical Haar | Agreement of only constants or finitely many probes → measure equality: **FALSE** |
| Pointwise strictly positive Gibbs weights → integrable normalized measure | Needs genuine Haar/test class, partition finite positive | Positive weights → full OS reflection positivity: **FALSE** (explicit 2×2 reflection Gram with negative quadratic form) |
| Strict positive cutoff-level gaps → strict continuum gap | Needs physical units, common selected H and **uniform** lower spectral bound/no pollution | Pointwise gap per cutoff → uniform continuum gap: **FALSE**, e.g. \(\Delta_n=1/n\) |
| Full same-H physical mass gap + OS locality/vacuum → clustering for local fields | Standard direction under relevant spectral/local assumptions, documented by Jaffe–Witten | One selected observable exponential clustering → full same-H gap: **FALSE**, possible unseen low-energy modes |
| Uniform dense-family physical clustering + correct O(4) time transfer → OS spectral gap | Candidate sufficient route, must prove cyclicity/domain/unit and spectral contradiction on the same H | Gap → source-native CMP116 specific differentiated polymer proof: **NOT NECESSARY** |
| Compact SU(2) theorem → all compact simple G | Only with independently proved, uniform *all-group* transport and correct group parameters | Single-group result → universal Clay group scope: **FALSE** |
| Clay theorem exists → our preferred R443/R445/R320 route | No theorem establishes necessity of this *particular* proof tactic | Do **not** add an equivalence/iff to a sufficient compiler |

Executable exact-rational negative controls in `scripts/check_ym_physical_bidi_nonpromotion_exact.py`:
1. strictly positive, symmetric 2×2 joint weights with negative reflected Gram form;
2. positive finite gaps \(\Delta_n=1/n\) lacking a common bound;
3. a single observable with \(e^{-t}\) decay while hidden modes have eigenvalues \(1/n\);
4. identical constant expectation but unequal two-state distributions;
5. true C3 label permutation without weighted-action invariance;
6. one group certified while another group remains unchecked.

These six logical/finitary counterexamples passed independently; they do not assert any real-world Yang–Mills counterexample or solve an analytic problem.

## 7. Pareto maximisation and the strict next cuts

**First, proof trust/semantics (indispensable):** resolve SEM.P01–P03, verify all newly source-written Agda on the exact PR head; audit original `RealAnalysisAxioms` postulates and provenance. A purely abstract or arbitrarily chosen predicate must never be counted as physical completion.

**Immediate finite exact cut:**
- Prove *generic* original permutation sorter correctness under distinct/membership hypotheses, or kernel-accept the three explicit closed C3/R445 canonical equalities. Prefer proof-relevant reusable algorithm correctness to multiple 46k/41k giant reductions.
- Link `Product.LinkPermutation` reordering and original 1024-bond `Codec.decodeOriginalBonds 4` to the actual selected Gibbs density and F19 **derived weighted** effective action, with a genuinely constructed measurable SU(N) Haar input.
- Do not duplicate abstract pushforward/reopening or the F13–F22 weighted algebra.

**Physical theorem discovery cut:** find source-native, quantitatively uniform R445 large-field/RG/reflection/limit bounds and physical R320 mixed-J/CMP116 rooted-shell estimates. Their universal positive numerical constants and source domains are **not derivable from finite bookkeeping alone**. R333 physical OS same-H gap is either downstream of sufficiently strong selected clustering or an independent direct spectral construction. Neither a direct conceptual route nor the preferred source-native route has been fully established.

**Clay endpoint:** fix real physical semantics, construct and verify selected local QFT fields/OS/H/gap for all required groups, and independently meet the external problem. The official problem remains open. No unconditional solution can be obtained by adding another abstract record or proving a purely finite permutation.

## 8. Exact current status

- 219 exact source declarations located and verified **all bare Set placeholders**; zero physical field witnesses audited or promoted.
- 66 canonical producer rows after adding SEM.P01–P03; R443 and R445 finite source modules provide many substantial conditional constructions, but their kernel receipts remain pending.
- 521 forward gate-hint edges, with exact reverse lookup; **all are search hints**, none a proved field-to-producer implication.
- One Round78 sufficiency compiler with 5 input roles, zero physical source inhabitants supplied by this audit; **no proven converse**.
- Source-written safe field no-promotion and parametric endpoint countermodel, with explicit anchored transport; these too need Agda kernel acceptance.
- Original 219 submission source files and #1460 unification files unchanged; new source audit/steelman/bidi work stays on YM #1444.

**Interpretation:** we know a precise hierarchy of short-term proof terms and conditional sufficient physical theorems; we do **not** know an exhaustive provably minimal set of physical analytic lemmas for a solved four-dimensional YM existence/mass-gap problem. The strongest forward answer is a **sufficient proof programme with explicit blockers**. The correct backward answer is *not* an iff: some preferred RG tactics are optional, and several seductive reverse implications have exact counterexamples.
