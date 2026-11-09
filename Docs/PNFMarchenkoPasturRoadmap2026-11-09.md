# PNF / Marchenko–Pastur theorem and evidence roadmap
Date: 2026-11-09
Branch: `pnf-mp-maxcut-2026-11-09`
Scope: the S&P-500 spectral-noise reel, prior PNF spectral work, and the dashiTRADE comparison.
Status: implementation in progress; no claim of Agda kernel acceptance without a checker run.

## 0. Source and attribution discipline

The attached reel says: eigenvalues of finite-history stock correlation matrices spread around the iid null, large market/sector modes can exceed the null, and most apparent sample correlations may be noise-compatible. This is an account of the *financial example*, not empirical evidence for a PNF ontology.

Existing DASHI sources:
- `DASHI/Information/PNFSpectralGeometry.agda`: typed atom identifiers vs activation/covariance/spectral roles; covariance/spectrum/band/filter interfaces.
- `DASHI/Information/PNFSpectralGeometryTests.agda`: elementary role tests.
- `Docs/PNFSpectralCovarianceGeometry.md`: roadmap and explicit outstanding numerical backend.
- `DASHI/Information/PNFMarchenkoPasturFiniteExact.agda` (this branch): finite Gram positivity theorem assuming real finite-sum order laws; deterministic MP edge formula receipt; PNF promotion evidence requirements; 120/200 cross-product identity.

dashiTRADE comparison: `scripts/phase07_eigen_boundary_check.py` uses action/transaction-cost boundary evidence, not matrix eigenvalues. These must never be conflated. Existing cross-asset forensics is inconclusive about some local warning states.

## 1. Statements now justified (and precise boundaries)

**T1 (finite Gram positivity).** For a quadratic form literally equal to a finite sum of squares over an ordered scalar carrier with nonnegative squares and finite-sum closure, the form is nonnegative. This is an algebraic theorem; it does not independently show that an arbitrary PNF covariance was constructed as this Gram form.

**T2 (rank upper bound, mathematical target).** A centred n×p matrix has rank at most min(p,n−1). The centred covariance has at least max(0,p−n+1) zero eigenvalues. This is standard finite linear algebra; it is NOT proved in the new module.

**T3 (MP weak-limit, mathematical target).** For the specified iid isotropic matrix ensemble, as p/n→γ>0, the empirical eigenvalue distribution of (1/n)XᵀX converges to the MP law. Edge eigenvalue convergence needs stronger hypotheses than weak convergence alone. This theorem is NOT yet formalised here.

**T4 (candidate vs interpretation).** An out-of-band mode is a candidate relative to its chosen null. It does NOT by itself establish a semantically valid, causal, stable or source-supported predicate relation. The new promotion record enforces explicit receipts as data, but does not automatically prove the PNF world model supplies them.

**T5 (finite data caveat).** For p=120,n=200, γ=0.6, unit variance MP edges are approximately 0.0508067 and 3.1491933. Earlier 2.7500 upper-edge reports are not equal to the unit-variance edge. Reconstruct the original calibration rather than silently replacing it.

**T6 (external planning-label warning).** Values 74.5526, 18.8350, 5.5865 are recorded in `DASHI/Unified/FleetFormalGapTargetTOEExact.agda` as *external planning labels* for Balaban RG, NS BM2 and Quantum Mereology. The source explicitly denies theorem-authority promotion. Their sum is 98.9741, but treating them as the top three eigenvalues of a shared p=120 correlation matrix (and assigning 82.4784% of its trace) is ONLY a counterfactual arithmetic illustration. No shared covariance matrix or trace receipt is established. `DASHI/Interop/PNFSpectralNumericABICore.agda` additionally defines `PNFSpectralNumericABIPromotion → ⊥`: numerical ABI materialization is candidate-only and cannot itself authorise promotion.

## 2. Phases, exact remaining declarations and deliverables

### Phase A — exact finite carrier [P0 maximum cut]

A1 `finiteGramPositiveSemidefinite`: IMPLEMENTED as theorem conditional on finite-sum laws; kernel check PENDING.
A2 `sampleCovarianceIsGramQuadratic`: FINITE SAME-OPERATOR QUADRATIC IDENTITY AUTHORED (kernel unverified). `PNFCovarianceQuadraticIdentityExact.scaledCovarianceQuadraticEqualsScaledGramQuadratic` and `covarianceOperatorPositiveSemidefinite` bridge to existing PSD authority. Selected source means, n−1 inverse and input receipt still OPEN. Earlier note: `PNFCentredCovarianceExact` now constructs centred finite rows from the same input matrix and source-specific column means; `scaledCovariance` and `scaledGramQuadratic` reuse that centred matrix with the same explicit scale. Still OPEN: actual mean=sum/n and scale=1/(n−1), a same-operator quadratic identity, and source-owned data receipt. Previously: `PNFFiniteGramPositiveExact.gramQuadratic` is an explicitly finite sum of squares, and `finiteMatrixGramPositiveSemidefinite` derives its nonnegativity by actual finite-sum induction using the stated positive-cone laws. The equality with the same source-normalized centred sample covariance matrix remains OPEN. Construct actual finite centred activation matrix and show the covariance quadratic equals sum of squares divided by n−1, with positive scale.
A3 `sampleCovarianceSymmetric`: WRITTEN FOR CENTRED SCALED FINITE MATRIX, KERNEL UNVERIFIED. `PNFCentredCovarianceExact.scaledCovarianceSymmetric` composes finite Gram symmetry with scalar multiplication. Previously: `PNFFiniteCovarianceEconomicsExact.sampleGramSymmetric` proves symmetry of the unscaled finite row Gram matrix using the canonical finite-sum and ring machinery; centring/source scaling remains OPEN. Derive symmetry from that actual construction, rather than supplying it as a field.
A4 `sampleCovarianceRankBound`: OPEN. Choose existing in-repo finite linear algebra, prove rank(C)≤min(p,n−1) for the *same centred matrix*.
A5 `sampleCovarianceForcedZeroMultiplicity`: OPEN. Derive max(0,p−n+1) zero eigenvalues from A4 and an actual spectral theorem.
A6 `correlationDiagonalAndTrace`: OPEN. Connect standardisation to Cᵢᵢ=1 and tr(C)=p, with nonconstant column assumptions.
Deliverable: exact finite PNF numerical carrier + sound proof certificates + real 200×120 replay.

### Phase B — Marchenko–Pastur distribution [P1]

B1 `mpAspectRatioAndVarianceWellFormed`: OPEN. Positive dimensions, nonnegative variance, nonnegative sqrtAspect and sqrtAspect²=γ.
B2 `marchenkoPasturEdges`: SPECIFIED in `MPFiniteCalibration`, equality fields supplied by backend; not independently proved.
B3 `marchenkoPasturBandOrdered`: OPEN as unconditional algebra lemma. Current `edgeOrdered` is a supplied witness.
B4 `marchenkoPasturZeroAtom`: OPEN. Mass (1−1/γ) when γ>1, otherwise 0; boundary γ=1.
B5 `marchenkoPasturDensityNormalised`: OPEN. Density + atom integrates to one.
B6 `marchenkoPasturMomentFormula`: OPEN. Finite combinatorial moment expression including special cases.
B7 `marchenkoPasturStieltjesEquation`: OPEN. Specify transform sign/branch convention; prove quadratic.
B8 `marchenkoPasturTransforms`: OPEN. R- and S-transform only after B7 and nonzero-domain qualifications.
B9 `marchenkoPasturWeakLimit`: OPEN. Select actual probability spaces, random matrix ensemble and mode of convergence; do not substitute a declaration of an arbitrary `Set`.
B10 `marchenkoPasturExtremeEigenvalueBounds`: OPEN. Distinct edge theorem with its own moment/tail hypotheses.
Deliverable: reusable parameterised probability measure, density/moments/transforms, weak-limit theorem with transparent assumptions.

### Phase C — numerical PNF bridge [P1–P2]

C1 `pnfWindowActivationEquality`: OPEN. Exact same-source rows/columns, handling missing data, source groups and provenance.
C2 `pnfNullAssumptionsAssessed`: OPEN. Determine why iid MP is/is not appropriate, including sparsity and hierarchy constraints.
C3 `pnfEmpiricalNullCalibrated`: OPEN. Column marginal, grouped, temporal and structural null controls; record what each preserves.
C4 `pnfEigenDecompositionVerified`: OPEN. Actual numerical decomposition, residual errors, deterministic reconstruction and conventions.
C5 `nonnegativeSpectralFilterPreservesPSD`: OPEN as reconstruction-specific theorem; A1 alone does not prove it.
C6 `cleanedCorrelationHasUnitDiagonal`: OPEN. PSD filtering does not necessarily preserve unit diagonal.
C7 `pnfStableSpectralSubspace`: OPEN. Measure invariant subspace/projector stability across samples, not only signs of individual eigenvectors.
C8 `pnfMPNullAdmission`: OPEN. Admit a candidate only relative to an explicitly fitted null with finite-sample uncertainty.
C9 `mpOutlierIsCandidateOnly`: partly encoded by `PNFModePromotion` receipt fields; actual PNF consumer non-bypass proof OPEN.
Deliverable: replayable timestamped spectral diagnostics with source and null receipts.

### Phase D — empirical test and worldview interpretation [P2]

D1 `historicalPNFReplaySameSource`: OPEN. Recover 319,211 items / 1,931 fibres and the selected 200×120 activation sample, including exact normalisation and null model; historical reports are NOT proof.
D2 `historicalUpperEdgeCalibrationReconciled`: OPEN. Explain historic 2.7500 against unit-scale 3.1491933 (or correct the source).
D3 `historicalEigenvalueTraceConsistency`: OPEN. First identify the actual eigenvalue-generating data product, if any; planning labels are not automatically matrix eigenvalues. Then check all eigenvalues and trace=120 only if it is truly a 120-column correlation matrix.
D4 `sourcePreservingNullNegativeControls`: OPEN. Hold representation source and temporal constraints fixed while testing residual structure.
D5 `PNFSemanticPromotionReceipt`: OPEN. Reuse canonical `PNFSpectralNumericABICore` candidate-only, rebuildability and non-promotion owners. Independent source/semantic/stability warrants must enter *outside* the forbidden numeric-ABI promotion boundary; no eigenvalue-only promotion.
Deliverable: PNF claims table separating theorem, data observation, null-relative candidate and admitted semantic claim.

### Phase E — dashiTRADE reuse, only after PNF calibration [P3]

E1 `spectralEvidenceDoesNotBypassNashiPolicy`: OPEN. Spectral data only upstream observational evidence.
E2 `sameWindowNoLookahead`: OPEN. Forecast splits, provenance and no future calibration.
E3 `spectralRiskEstimateOutOfSample`: OPEN. Test cleaned covariance in risk estimation independently of signal.
E4 `spectralFeatureAddsNetSurplus`: OPEN. Compare action ledger, cost, turnover, drawdown and horizon perturbations on matched data.
Deliverable: optional risk/regime consumer, not a claimed trading edge.

## 3. Dependency maximum cut

A2→A3,A4,A6; A4+finite spectral backend→A5.
B1→B3→B4,B5; B5→B6/B7; probabilistic source→B9; stronger assumptions→B10.
A2+A6+B1+B5+B9+C1→C2,C3,C8; A2+C4→C5,C6.
C1+C3+C4+C7+C8→D1–D5; only subsequently D5→E1–E4.

Practical next cut: kernel-check the new finite module; implement exact finite sum/matrix and source-bound covariance; replay the original PNF matrix with recorded normalization. Avoid jumping to full MP weak convergence before these direct PNF gates.

## 4. Non-claims

- MP does not establish that bulk modes are semantic nonsense.
- Outliers do not prove concepts, causal relationships, or stable latent ontology.
- External Fleet planning labels must not be silently reclassified as a common PNF correlation-matrix spectrum.
- An eigenvalue-only threshold is not a finite-sample hypothesis-test p-value.
- S&P 500 correlation behaviour is not evidence that PNF has the same ensemble law.
- dashiTRADE's 'eigen-event' classification is an action boundary, not literally a covariance eigenmode.
- The new finite Agda file has not been accepted by Agda 2.9 in this environment.

## 5. Economic strand retained from the supplied S&P 500 reel

### Exact transcript assertions, not expanded claims
The reel (00:00–00:55) asserts: (ECO-S1) most patterns in S&P 500 sample correlations fail its noise test; (ECO-S2) with an independent-stock idealized null, population correlations are identity and finite history spreads sample eigenvalues; (ECO-S3) shuffling stock-specific dates destroys cross-correlations and brings the spectrum to an MP-like noise curve; (ECO-S4) a few sector modes and a much larger market principal component exceed the noise edge; (ECO-S5) modes within the edge cannot be separated from null noise by that test; (ECO-S6) quants often clip noise-compatible eigenvalues to an average; and (ECO-S7) reducing correlation and lengthening history tends to collapse the observed spectrum toward one. These are the reel's explanatory assertions, not independent quantitative results validated by this PR.

### Phase F — economics / quantitative-finance research [P1–P3; independent of PNF semantic promotion]

F1 `stockReturnsCorrelationSameWindow`: OPEN. Explicit asset universe, return convention, missing observations, corporate actions, survival bias, and chronology.
F2 `equicorrelationPopulationSpectrum`: PARTIAL. The exact market-eigenvalue equality `marketEigenvalueClosedForm` and `equiMarketEigenClosedForm` are now written, yielding 1+(p−1)ρ for p=suc k. Residual eigenvalue 1−ρ is proven as an eigenvector identity for sum-zero vectors, conditional only on the existing exact ring carrier. Multiplicity p−1, orthogonality and PSD parameter range are still OPEN (kernel unverified). Previously: `PNFFiniteCovarianceEconomicsExact` supplies `equiOperator`, `equiZeroSumEigen`, `equiMarketEigen`, `sumConstantOne`, and `equiZeroCorrelationIsIdentity` (Agda kernel check PENDING). Remaining: simplify (1−ρ)+ρp to 1+(p−1)ρ with a correct finite-dimensional scalar injection; establish residual eigenspace dimension p−1, orthogonal eigenspace decomposition, and PSD condition −1/(p−1)≤ρ≤1 for p>1. Derive for p assets with common off-diagonal correlation r the eigenvalues 1+(p−1)r and 1−r (multiplicity p−1), including PSD constraints and correct r→0 and p/T→0 interpretations. This provides exact algebraic meaning to the reel's final 'drop correlation' illustration, without confusing finite-sample MP with population spectra.
F3 `independentReturnsNullSpectralCalibration`: OPEN. Compare iid MP, time-shuffled, block-shuffled and volatility-preserving controls; distinguish sample-vs-population statements and edge uncertainty.
F4 `marketAndSectorModeIdentification`: OPEN. Determine whether empirical outliers map to broad market/sector exposures using independent sector labels and factor-model diagnostics, not merely large eigenvalues.
F5 `economicCovarianceCleaningPreservesPSD`: OPEN. With a nonnegative spectral filter prove PSD of the reconstructed covariance; verify re-scaling/diagonal restoration where correlation matrices are required.
F6 `cleaningImprovesOutOfSampleRiskForecast`: OPEN. Walk-forward covariance forecast versus raw sample, diagonal, shrinkage and factor-model benchmarks. Report realized portfolio variance, calibration, turnover and stability.
F7 `portfolioRiskAndDiversificationBridge`: OPEN. Verify wᵀΣw risk, market-factor exposure, residual/sector exposure, effective diversification, and uncertainty of estimated minimum-variance weights.
F8 `covariancePrecisionRegularisation`: OPEN. Establish invertibility/eigenvalue-floor requirements for covariance inversion; measure sensitivity of optimization to small eigenvalues, weight constraints and estimation error.
F9 `riskVersusAlphaNonpromotion`: OPEN. A better risk estimator or eigenvalue outlier is not a return-predictive trading strategy; no claim of economic net surplus without held-out execution evidence.
F10 `sameLedgerDashiTradeComparison`: OPEN. Compare unchanged Nashi policy with cleaned-covariance risk controller and MP market/sector regime feature; preserve support gates and action cost ledger, test friction, regimes and no-lookahead.
F11 `temporalRegimeNonstationarity`: OPEN. Test changing covariance, rolling estimation horizon, regime-dependent factor loadings, and instability of MP calibration under dependence/heteroskedasticity.

**Economic deliverables:** (i) a replayable returns-and-spectrum experiment matching the reel's S&P 500 claim if the original data, period and universe can be independently recovered; otherwise a separate, explicitly labelled independent example; (ii) MP-versus-permutation null diagnostics; (iii) PSD/correlation-cleaning receipts; (iv) walk-forward risk-forecast and portfolio allocation comparisons; (v) costed dashiTRADE ablation with no signal/promotion shortcuts.

### Cross-domain comparison and non-identity
Same matrix mathematics may be reused, but stock returns, PNF predicate activations and signed-residual graph/Laplacian weights are different measured objects with different nulls, semantics and admission owners. Economic market modes and PNF structural motifs are analogies, not the same objects. Portfolio-risk improvement does not prove PNF semantic truth; PNF spectral outliers do not prove economic alpha.

### Updated priority / dependencies
Finite source-independent Gram positivity and symmetry and market/residual equicorrelation eigenvector identities are now written, but unverified by Agda. Finish original-source centred covariance identity A2 and F2 spectral multiplicity/PSD thresholds as parallel lanes. Then build exact MP law B1–B10. Economic F1/F3/F4 and PNF C1/C2/C3 must each pay separate data/null-model assumptions. Cleaning C5/F5 shares a generic PSD theorem but each needs its own diagonal/provenance contract. Economic risk validation F6–F8 does not depend on PNF semantic promotion D5. dashiTRADE F10/E1–E4 requires its own no-lookahead and action-cost receipts.

## 6. Continuation 2026-11-09 — exact finite theorem implementation

Committed to PR #1480:
- `DASHI/Information/PNFFiniteCovarianceEconomicsExact.agda`: actual finite row Gram, symmetry theorem, population equicorrelation operator, zero-sum eigenvector theorem, all-ones market eigenvector theorem, number-of-coordinate scalar definition, and zero-correlation identity.
- `DASHI/Information/PNFFiniteGramPositiveExact.agda`: explicit finite matrix projection and sum of squares, positive-cone assumptions, proof of sum nonnegativity by induction over `Fin n`, Gram quadratic PSD.
- Earlier `DASHI/Information/PNFMarchenkoPasturFiniteExact.agda`: conditional Gram positivity interface, MP edge calibration, externally owned PNF evidence predicates, and canonical numeric-ABI non-promotion weld.

**Verification:** These are authored Agda proof terms in a GitHub draft PR. Agda executable was not available in the current environment. Do not call them kernel-checked or promote unverified types/identities. The full finite spectral decomposition, correlation normalisation, MP probability law, original numerical PNF evidence and economic outcomes remain open.

**Priority refinement:** the exact source-indexed and normalised covariance construction A2 is the common blocker to both PNF and finance. F2's market/residual eigenvector laws do NOT establish sector modes, distributional MP predictions, or empirical financial factor interpretation. Follow with A4 rank and B1–B5 formal real-measure interface. Keep the economic F6–F11 walk-forward ledger independent of PNF semantic authority.

## 7. Follow-on exact finite cut

New source: `DASHI/Information/PNFCentredCovarianceExact.agda` constructs a centred matrix from explicitly supplied raw data/column mean, symmetric scaled covariance and PSD of the *scaled sum-of-squares* quadratic for a nonnegative scale. This is not yet the proof equating the quadratic with `vᵀCv` for the operator `scaledCovariance`; finish via finite-sum reordering/distributivity. It also does not establish that supplied means are true sample means.

New equations in `PNFFiniteCovarianceEconomicsExact.agda`:
- `marketEigenvalueClosedForm` derives (1−ρ)+ρp=1+(p−1)ρ for p≥1.
- `equiMarketEigenClosedForm` transports this to the all-ones eigenvector.
- `equiZeroSumEigen` gives eigenvalue 1−ρ for every zero-sum vector.
- `equiZeroCorrelationIsIdentity` proves the population rho=0 operator identity. **This is not convergence of finite-sample spectra to 1.**

Next maximum-cut leaves, in order:
1. P0 `kernelAcceptsPNFFiniteCovarianceEconomicsExact`, `kernelAcceptsPNFFiniteGramPositiveExact`, `kernelAcceptsPNFCentredCovarianceExact` — actual Agda 2.9 compilation and source/API repairs.
2. P0 `sampleMeanDefiningEquation`, `positiveUnbiasedScale`, `scaledCovarianceQuadraticEqualsScaledGramQuadratic` — finish same-object covariance PSD, not just two separately positive definitions.
3. P0 `equiResidualSpaceDimension`, `equiPopulationPSDRange` — complete F2 including finite dimension and rho constraints.
4. P1 `mpVarianceAspectExact`, `mpEdgeOrderDerived`, `mpZeroAtomAndNormalization` — real carrier and probability law.
5. P1 `empiricalPNFNullSpecific`, `independentEconomicNullSpecific` — two separately paid scientific models.
6. P2 `originalPNFRebuildAndSpectralReplay`, `economicOutOfSampleRiskAblation` — actual data receipts, independent semantic/economic outcomes.

No testing, market claims or historical PNF covariance assertions were invented from the finite algebra.

## 8. Maximum-cut continuation — exact exchange, standardisation, synthetic economics check (2026-11-09)

### New committed implementation
- `DASHI/Information/PNFFiniteSumExchangeExact.agda`: `finiteSumExchange`, a genuine finite Fubini lemma by induction and existing `sumFinAdd`. Algebraic precursor to the missing `vᵀCv = scale·∑ᵣ(∑ᵢXᵣᵢvᵢ)²` proof.
- `DASHI/Information/PNFStandardisedCovarianceExact.agda`: `correlationDiagonalOne` and `correlationTraceEqualsDimension` for a `StandardisedWindow` which explicitly supplies each column's unit-diagonal normalization receipt. Does not assume arbitrary centered columns are standardized.
- `scripts/pnf_mp_economic_synthetic_check.py`: deterministic synthetic-only iid/common-factor/shuffled spectral comparison, preserving correlation trace and PSD; clipped-eigenvalue covariance is not claimed to have unit diagonal.

### Local synthetic sanity receipt (independently authored local test; not a source-specific PNF or market replay)
A 200×120, rho=0.25 seeded synthetic diagnostic was run locally using NumPy, with sample-covariance denominator 199, giving MP upper edge ≈3.1561. In that local run, independent null max eigenvalue ≈2.9738; one-factor panel max ≈31.7247; shuffled panel max ≈2.9954. All sample correlation traces were 120. The script committed above implements the same classes of tests but was not rerun from the GitHub checkout. These outcomes support only a software/mechanical sanity check, NOT S&P 500 data or PNF evidence.

### Accounting and exact next leaves
- `finiteSumExchange`: authored proof, kernel UNVERIFIED.
- A6 `correlationTraceEqualsDimension`: conditional on independently paid unit-diagonal source normalization, authored proof, kernel UNVERIFIED.
- A2 `scaledCovarianceQuadraticEqualsScaledGramQuadratic`: OPEN; this must be proved using actual finite exchange + multiplication distribution, not inferred from two definitions.
- A2 `sampleMeanDefiningEquation`, `positiveUnbiasedScale`: OPEN.
- F2 `equiResidualSpaceDimension`, `equiPopulationPSDRange`: OPEN.
- B1–B10 MP density/measure/transform/limit law: OPEN.
- D1–D5 same-source PNF replay and authority: OPEN.
- F1/F3–F11 empirical economics and costed trade ablation: OPEN.
- P0 Agda 2.9 checker acceptance of all new modules and transitive imports: OPEN.

**Source and authority rule:** The synthetic check tests mathematics/software behavior, not PNF semantics or real portfolio performance. The external Fleet spectral labels remain candidate/planning evidence only. The numeric ABI remains non-promotable by its established empty promotion type.

## 9. Existing PSD reuse and exact operator identity continuation (2026-11-09)

**Correction to dependency ownership:** DASHI already supplies `DASHI.Physics.Closure.NSTriadKNPhysicalCutoffOrbitGramAssembly.FiniteGramOrderAuthority`, with zero/additive/square positivity and additive monotonicity laws. Its finite ordered-ring and `sumFin` infrastructure belong to `NSTriadKNPhysicalCutoffInnerProduct`. We reuse this existing PSD order authority: `PNFFiniteGramPositiveExact.positiveConeFromExistingPSD` and `finiteMatrixGramPSDFromExisting`; `PNFCentredCovarianceExact.centredCovarianceGramPSDFromExisting`. The PNF-specific `PositiveCone` is now an adapter for compatibility, not a newly required proof source. This does not imply signed residual Laplacians are PSD: the signed and unsigned operators remain distinct.

### New exact algebra authored and committed
- `PNFFiniteBilinearExpansionExact.sumFinMulRight`, `rowProjectionScale`, `finiteCovarianceSumExchange`.
- `PNFCovarianceQuadraticIdentityExact.gramActionEqualsRowProjection`: finite Fubini + distributivity.
- `PNFCovarianceQuadraticIdentityExact.unscaledGramQuadraticEqualsSquares`: vᵀ(XᵀX)v equals finite rowwise sum of squares.
- `PNFCovarianceQuadraticIdentityExact.covarianceScaleOut`, `scaledCovarianceQuadraticEqualsScaledGramQuadratic`: same-source centred scaled operator quadratic equals scaled Gram sum of squares.
- `PNFCovarianceQuadraticIdentityExact.covarianceOperatorPositiveSemidefinite`: transport the existing finite Gram PSD authority through the equality for nonnegative scale.
- `PNFEquicorrelationPositiveExact.equiQuadraticDecomposition`: equicorrelation risk quadratic decomposes into (1−rho)·∑vᵢ² + rho·(∑vᵢ)².
- `PNFEquicorrelationPositiveExact.equiQuadraticNonnegativeForPositiveRho`: proves sufficient PSD for 0≤rho≤1 expressed as rho≥0 and 1−rho≥0. The full rho≥−1/(p−1) range remains OPEN.

**All new Agda proof terms are authored, NOT Agda 2.9 kernel-accepted**. Lightweight delimiter checks passed; this is NOT a typechecker substitute. A2's *finite same-operator identity* is now authored, but the normalization/empirical alignment still remains open and the kernel gate has not been discharged.

### Revised maximum-cut accounting
- P0 `kernelAcceptsPNFCovarianceQuadraticIdentityExact` and all imports: OPEN (run pinned Agda + repair).
- P0 `sampleMeanDefiningEquation` and `positiveUnbiasedScale`: OPEN (selected n>1, field inverse, source-specific mean).
- P0 `sampleCovarianceRankBound`, `sampleCovarianceForcedZeroMultiplicity`: OPEN (exact linear algebra).
- P0 `equiResidualSpaceDimension`, `equiPopulationPSDRange`: OPEN beyond rho≥0 sufficient PSD.
- P1 B1–B10 full MP distribution, moments, resolvent, weak limit: OPEN.
- P1 C1–C9 same-source PNF null and operator spectral reconstruction: OPEN except finite algebra sublemmas.
- P2 D1–D5 source replay and semantic admission; F1, F3–F11 economics risk/costed market validation: OPEN.
- P3 dashiTRADE Nashi no-bypass & action-cost ledger: OPEN.

**No false closure:** existing PSD establishes the relevant ordered-scalar finite positivity law. It does NOT establish iid MP assumptions, empirical PNF source identity, positive signed-Laplacian behavior, finite-sample market eigenvalue outlier significance, or semantic/economic promotion.

## 10. Generic PSD-preserving spectral cleaning (2026-11-09)

Added `DASHI/Information/PNFSpectralCleaningPSDExact.agda` using canonical `FiniteGramOrderAuthority`:
- `FilteredFiniteSpectrum`: actual finite mode-indexed coefficients, filtered eigenvalue weights and per-mode nonnegativity proof.
- `spectrallyCleanedQuadratic`: explicit finite sum ∑λᵢ(v·uᵢ)² (coefficient is supplied as a genuine per-mode coordinate, not an assumed eigenvector).
- `nonnegativeSpectralFilterPreservesPSD`: finite-sum square positivity from the canonical PSD owner.
- `CleanedOperatorEquality`: requires a literal equality from the selected operator quadratic to the finite spectral sum (NOT mere Set-valued placeholder).
- `cleanedOperatorPositiveSemidefinite`: PSD transport along that explicit equality.

The generic algebraic part of C5/F5 is now **AUTHORED, KERNEL UNVERIFIED**. The actual cleaned PNF covariance and cleaned economic correlation must still supply genuine orthogonal eigenvectors, reconstruct the original operator, prove the displayed quadratic equality and, for a correlation matrix, restore/check diagonal 1. These are **not** consequences of nonnegative filtering alone.

### Revised sharp cut
P0: Run Agda 2.9 with pinned stdlib to typecheck all seven new modules and dependencies; correct any failures before claiming kernel acceptance.
P0: Pay same-source actual means and scale identities and prove finite covariance rank/nullity and equicorrelation residual subspace dimension/negative rho bound.
P1: Instantiate spectral cleaning with reconstructed matrices and diagonal restoration; formal MP density/zero mass/moments/transforms/weak convergence remains independent.
P2: Replay the historical PNF data with source metadata and independently test the S&P 500 economic claims; quantitative outliers alone have no PNF truth or trading-alpha authority.
P3: Consume the cleaned economic risk estimate in dashiTRADE's existing no-bypass support/cost pipeline, with held-out ledger.

## 11. Continued exact finite maximum cut — sourced means, unbiased covariance and diagonal repair

**New Agda declarations (authored, NOT Agda-kernel-checked)**

- `DASHI/Information/PNFSampleMeanExact.agda`: `sumConstantValue`, `ActualFiniteMean`, and `sampleMeanDefiningEquation`. Exact finite mean receipt `sum(rawColumn)=n·mean` is enough to derive `sum(centeredColumn)=0` via existing `sumFinAdd`, `sumFinNeg` and ring inverses. This is a real algebraic implication, but the receipt still needs instantiation for a selected PNF or financial dataset.
- `DASHI/Information/PNFUnbiasedCovarianceExact.agda`: `UnbiasedCovarianceWindow` fixes n=suc(suc k), supplies a proof of scale·(n−1)=1 and nonnegative scale, and derives `unbiasedCenteredColumnSumZero`, `unbiasedCovarianceOperatorPSD`, `unbiasedCovarianceSymmetric`. Actual field inversion and source data certificates remain unpaid.
- `DASHI/Information/PNFSpectralCleaningPSDExact.diagonalCongruencePreservesPSD`: cleaned operator quadratic remains PSD under an explicitly provided vector-coordinate transform. This is an operator-level congruence theorem, NOT a derivation of strictly positive diagonal, inverse square roots, or trace preservation.

**Economic/PNF numerical negative control:**
`scripts/pnf_mp_economic_synthetic_check.py` now explicitly reconstructs the clipped covariance, records raw diagonal error, uses positive-diagonal congruence normalization, and verifies PSD and unit diagonal numerically. Separately executed local NumPy seeded fixture (n=200,p=120,rho=0.25) returned:
- MP upper edge: 3.1560959816749232.
- Largest eigenvalues: independent 2.973781095949251; common-factor 31.724663532759376; independently shuffled 2.9953737602923094.
- All three sample correlation traces: 120.
- Common-factor cleaned covariance raw diagonal max deviation: 0.12508710519166777, demonstrating why spectral clipping alone does not produce a correlation matrix.
The committed script has been revised to test diagonal correction; the revised GitHub script itself has not been executed from a checkout here.

**Exact remaining max-cut ledger (supersedes earlier open descriptions where stated):**
- A2 source-selected mean law `sampleMeanDefiningEquation`: conditional algebraic proof **authored**, source instantiation OPEN; unbiased inverse/positivity carried as explicit `UnbiasedCovarianceWindow` receipts; field-level construction OPEN.
- A2 finite quadratic operator equality and PSD: algebraic proof **authored**, actual kernel acceptance OPEN.
- A3 symmetry: algebraic proof **authored**, kernel acceptance OPEN.
- A4/A5 rank≤min(p,n−1) and forced-zero multiplicity: OPEN. From centered-column-zero sums we have a constructive left-null candidate, but a rank-nullity/eigenspace theorem still must be connected.
- A6 correlation diagonal/trace: proof conditional on unit-diagonal receipts **authored**, real standardisation OPEN.
- F2 equicorrelation market/residual eigenvectors and rho≥0 sufficient PSD: **authored**, full negative-rho interval, dimension and kernel checks OPEN.
- C5/F5 nonnegative spectral PSD and generic congruence preservation: **authored**; source-owned eigen-reconstruction and strictly-positive diagonal/inverse square roots OPEN.
- B1–B10 actual Marchenko–Pastur distribution and convergence: OPEN.
- C/D PNF source-data replay and independent semantic promotion: OPEN. Existing numeric ABI remains non-promotable.
- F/E independently evaluated financial risk forecast, real economic data, and costed dashiTRADE action ledger: OPEN.
- **P0 all modules:** no Agda 2.9 binary available in this execution environment; not kernel-verified. Do not treat committed proof text as accepted theorem.

**Further cut choice:** connect the actual sample-mean and unbiased-scale receipts to the source-bound same-window activation/returns loaders; use existing finite ordered-linear algebra for rank/nullity; choose a concrete PSD spectral-decomposition owner for filtered covariance, then attach the genuinely probabilistic MP law separately.
