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

## 12. Further finite rank constructive cut — centred row dependency

Added `DASHI/Information/PNFCentredRankDependencyExact.agda` (authored, Agda kernel NOT checked):
- `addInverseRight`: derived from existing ordered-ring commutativity and inverse.
- `sumToZeroDeterminesFirst`: if a+b=0, a=−b.
- `zeroSumFirstDeterminedByTail`: any zero-sum Fin(suc n) vector has first coordinate equal to minus the finite sum of the remaining coordinates.
- `centredFirstRowDeterminedByRemainingRows`: instantiates this for every column of the *same source-paid centred matrix* using `sampleMeanDefiningEquation`.

This is an explicit finite linear dependence certificate establishing that the first centred observation row is algebraically determined by the n−1 remaining observation rows. It is the constructive geometric content behind `rank(X_centered)≤n−1`, but DOES NOT itself prove a formal matrix rank bound or zero eigenvalue multiplicity: those still require a selected finite field/vector-space dimension-and-rank owner and eigenspace/nullity connection.

P0 status:
1. Repair and kernel-check all new Agda declarations and dependencies — OPEN.
2. Instantiate actual means and nonnegative inverse-(n−1) from source-selective real coefficients — OPEN.
3. Connect centred dependency to a field-based finite rank/dimension theorem and covariance nullity/eigenvalue multiplicity — OPEN.
4. Complete negative-rho equicorrelation PSD range with existing finite Cauchy–Schwarz/Jensen owner (investigate `NSTriadKNLuoFiniteJensenSquareExact`), with exact same coefficient carrier — OPEN.
5. Instantiate filtered eigenvector reconstruction and positive diagonal normalisation — OPEN.
6. MP measure law/limits and real PNF/economics source evidence — OPEN.

No external eigenvalue label is promoted by any of these algebraic results.

## 13. Existing finite Cauchy–Schwarz / Jensen owner (economics F2)

Inspection identifies a directly relevant exact theorem: `DASHI.Physics.Closure.NSTriadKNLuoFiniteJensenSquareExact.finiteJensenSquare` proves `(∑a_i)² ≤ (∑a_i²)·length` for finite lists over `Data.Rational.Base.ℚ`, reusing `NSTriadKNRationalOrderedFiniteL2.finiteCauchySchwarzSquared`. Its statement is real mathematics, not a receipt-only Set field.

For the equicorrelation full PSD range, the maximum cut is therefore **not** to reinvent Cauchy–Schwarz. It is to instantiate the finance equicorrelation quadratic over the same rational carrier and finite-list summation, connect the existing Jensen bound and rational order multiplication by nonpositive rho, and finish necessity using the all-ones and a nonzero zero-sum vector for p>1. No full-range theorem has been authored in this round. Do not transfer this rational theorem automatically to arbitrary `ExactOrderedScalar` without a real carrier/ordered-field embedding.

## 14. MP reuse and executable null backend (2026-11-09)

**Reused source owners:** `DASHI.Information.PNFSpectralGeometry.SpectralNoiseBand`, `NoiseClassifier` and `DASHI.Information.PNFMarchenkoPasturFiniteExact.MPFiniteCalibration`; source-owned non-promotion remains `DASHI.Interop.PNFSpectralNumericABICore.pnfSpectralNumericABIPromotionImpossible`. Default branch search did **not** identify a separate complete Marchenko–Pastur density/weak-limit implementation.

**New committed code:**
- `DASHI/Information/PNFMarchenkoPasturAdmissionExact.agda`: `MPPNFCandidate` links an existing MP calibration to the existing PNF classifier with a definitional classification-equality proof. `mpCandidateAboveEdge` delegates to the original `above-null-band` theorem. `mpCandidateCannotPromoteNumericABI` directly reuses the canonical empty promotion type. Agda kernel acceptance OPEN.
- `scripts/pnf_marchenko_pastur_numeric.py`: numerical MP endpoints, continuous density, zero atom, finite centered covariance/correlation, bulk eigenvalue clipping, PSD-preserving reconstructed operator with explicit diagonal restoration, source-labelled receipt and forced-zero lower-bound calculation.
- `tests/test_pnf_marchenko_pastur_numeric.py`: 4 synthetic/unit tests checking density+atom normalization numerically, finite rank/trace/PSD/diagonal preservation, invalid data rejection, and common-factor versus independently shuffled samples.
- An independent local sibling numerical module with the same MP and covariance-cleaning mathematical functionality passed 4/4 tests under Python 3.13 / NumPy on 2026-11-09. The exact committed GitHub module/tests have NOT been run from a checked-out branch in this environment; run them in the repository and record their actual result before treating that implementation as tested.

**MP convention:** \(\gamma=p/(n-1)\) for centered sample covariance, edges \(\sigma^2(1\pm\sqrt\gamma)^2\), zero atom \(\max(0,1-1/\gamma)\). For correlation matrices \(\sigma^2=1\) is the explicitly chosen baseline, NOT a fitted PNF noise variance. MP density normalization is numerically tested, not formally proved in Agda. A finite-dimensional MP edge is a heuristic reference unless the relevant edge uncertainty, dependence assumptions and multiple-testing questions are addressed.

**New PNF/economics assertions enabled in software (not empirical conclusions):**
1. PNF explicit predicate activations and financial returns can pass through the same finite numeric covariance procedure when each has independently selected source, units, missing-data and dependence conventions.
2. A statistically unusual mode is only a candidate; candidate status never bypasses PNF provenance/semantic gates or dashiTRADE cost/action gates.
3. Correlation cleaning requires a diagonal repair after bulk spectral clipping. A cleaned covariance PSD theorem does not prove unit diagonal, out-of-sample risk benefit, sector identity or trading alpha.
4. If p>n-1, finite centered covariance has at least p-(n-1) zero eigenvalues. An exact proof of this multiplicity in Agda still needs rank/nullity, despite the constructive centred-row dependence lemma.

**Next exact maximum cut:**
P0 kernel-check all draft PR modules and repair any failures; run exact GitHub numeric tests.
P0 bridge existing finite rank/nullity to `centredFirstRowDeterminedByRemainingRows`; complete rational equicorrelation PSD interval using the repo's proven finite Jensen/Cauchy result.
P1 source-verified, explicit orthogonal eigendecomposition and diagonal correlation restoration (not merely generic PSD). Full MP measure-normalization, moments, Stieltjes equation and asymptotic weak limit remain OPEN in Agda.
P2 recover original PNF eigenvalue-generating inputs and run independently justified null controls; run actual financial-market data and held-out covariance-risk assessment.
P3 integrate the clean risk estimate as an optional upstream observation to Nashi with a source-specific no-bypass and costed walk-forward ledger.

**Attribution:** external Fleet values 74.5526/18.8350/5.5865 are planning labels, not proven eigenvalues from one 120-column correlation matrix. Do not infer an 82.48% explained-variance claim. The reel itself motivates the null-versus-signal comparison, but it does not establish applicability of iid MP to PNF data.

## 15. Finite rank/nullity bridge (2026-11-10)

The same source-centred n-by-p matrix has zero column sums. The explicit first-row reconstruction and linear whole-operator factorisation through n-1 tail rows have been authored in Agda.

**New modules:** `PNFCentredRankFactorisationExact`, `PNFCentredLinearRankExact`, `PNFCentredKernelExact`, `PNFCovarianceRankFactorisationExact`, and `PNFFiniteRankNullityBridgeExact`. They construct exact column and operator compression, prove both encoding and decoding maps linear, show equality of kernels for full centred and tail maps, and derive the covariance rank bound and finite rank/nullity equation from an explicit general finite-field rank theorem interface.

The Nat arithmetic corollary is `covarianceNullityAtLeastForcedLowerBound`, with p∸(n−1)≤nullity(C). `forcedZeroEigenvalueMultiplicityLowerBound` transfers this to the zero eigenspace only when the selected symmetric spectral decomposition supplies an equality between zero multiplicity and kernel dimension.

**Still open:** Agda kernel checking of all new modules. `FiniteFieldRankNullityOwner` has not yet been instantiated with a checked finite-dimensional linear algebra theorem, and `CovarianceZeroSpectrum` requires a real symmetric spectral multiplicity theorem. Neither is silently assumed complete.

**Exact executable witness:** `scripts/pnf_exact_finite_rank_nullity.py` uses exact rational row reduction and constructs an independent kernel basis for same-source centred covariance. A sibling implementation ran on small matrices, including 3×5 (rank 2, nullity 3), 4×2 (rank 2, nullity 0), 2×4 (rank 0, nullity 4). The precise GitHub branch file has not been executed from a checkout.

The result is domain-neutral finite geometry. PNF semantics and financial MP null assumptions remain distinct.

### Finite rank/nullity proof and verification supplement

Let n=k+1 with n>=2. Write B for the k×p matrix containing the final k centred observation rows, and let R be the (k+1)×k linear reconstruction with top row (-1,...,-1) and lower block I_k. The source-paid mean identity establishes *exactly* Xc = R B (not just a reported numerical rank). Thus for any scalar covariance scale s,

    C = s Xc^T Xc = s B^T R^T R B.

Consequently rank(Xc)≤min(k,p) and rank(C)≤min(k,p). Over any field with the finite-dimensional rank-nullity theorem, dim ker(C)=p-rank(C)≥max(0,p-k). Over reals, C is symmetric, so its zero-eigenvalue multiplicity equals dim ker(C). With s>0, the stronger equality ker(C)=ker(Xc) follows from v^T C v = s ||Xc v||² and definiteness; the rank upper bound itself does not need s>0.

The Agda implementation of R, its linear laws and the two source-specific operator factorizations is authored. The *generic* finite-field theorem `FiniteFieldRankNullityOwner` and zero-spectrum identification `CovarianceZeroSpectrum` are not instantiated in this branch, and Agda kernel acceptance remains open. These exact obligations must not be renamed as closed.

Local exact-rational verification additionally passed **216** pseudo-random finite matrices spanning n=2..8 and p=1..9 (three matrices per shape), checking rank(Xc)=rank(C), independent kernel basis, exact C·v=0, and nullity≥max(0,p−n+1). This is runtime evidence for the formulas, not an Agda proof or an actual PNF or market dataset.

## 16. 369–27, dialectic/trialectic and pants-gluing maximum cut (2026-11-10)

### Source audit: existing owners, not invented interpretations

- `DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact` proves 27-state T^3 and three-factor 19,683-state T^9 hyperfabric cardinalities. These are **state-space cardinalities**, not observed sample sizes or automatically matrix ranks.
- `DASHI.Reasoning.TrialecticObserverMatrix369Exact` supplies the typed three-by-three observer matrix (three self positions, six directed other-model positions). Its D4 chart bijection is not psychological ontology.
- `DASHI.Reasoning.Trialectic369DescentNaturalityExact` proves exact A/B, B/C, C/A chart overlap/restriction/regluing for SSP trits and exact row-to-27-cube projection naturality. It explicitly does NOT certify identity with a larger X6 Čech/Grothendieck site.
- `DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact` proves the three 27-state dialectic cells <-> T^9 hyperfabric rechart.
- `DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact` proves that even matching three dyadic boundary edges do not determine the triadic face.
- `DASHI.Topology.TernaryCylinderPantsGeometryExact` and `DASHI.Reasoning.TypedHyperfabricPantsGluingBridgeExact` provide finite 1→3 pants/channel combinatorics and exact interface-match seams. Neither is a smooth manifold/TQFT or a license to change topology or erase provenance.

### Exact declarations newly authored on PR #1480

1. `PNFTrialecticSpectralDescentExact`: generic value-typed three-chart overlap/gluing theorem; observer-matrix roundtrip; `mapMatchingFamily` and `pointwiseSpectralClassificationCommutesWithGluing` plus chart naturality; directly reuses triadic-face nonfactorability. This generalizes the existing SSP-only cover to arbitrary *spectral evidence values* without inventing local covariance reconstruction.
2. `PNF36927FiniteRankBoundaryExact`: preserves existing 3 (pants branches), 9 (observer positions), 27 (ternary states) carrier counts and derives **conditional** forced-nullity bounds p∸2, p∸8, p∸26 for real source panels with exactly 3, 9, 27 observed rows. Carrier cardinality alone never pays an observation count or a sample mean receipt.
3. `PNFTrialecticPantsSpectralInterfaceExact`: pairs a matching three-chart family with an independently required full `Pants.InterfaceMatch`; transports proposition/capacity matching and reuses the canonical hyperfabric/pants seam witness.
4. `PNFMP36927ChartNaturalityExact`: specializes generic pointwise descent to the **existing MP-calibrated PNF `NoiseClassifier`**; explicit AB/BC/CA restriction squares commute. This is pointwise classification of *already supplied values*, not local computation of a matrix spectrum.
5. `PNFDialecticTrialectic369RechartExact`: composes the existing `CellDialectic ↔ T^9` and `ObserverMatrix3 SSPTrit ↔ T^9` bijections and proves both roundtrip equalities. Requires an explicit trit→scalar encoding before any MP threshold is applied.
6. `PNFPantsPooledCovariancePSDExact`: for a source-confirmed common vector carrier, three PSD within-branch quadratics and **two** nonnegative between-branch rank-one corrections, proves positivity of the *selected pooled quadratic* through the existing `FiniteGramOrderAuthority`. The actual pooled quadratic equality is a separately paid mathematical/source field; pants seam matching does not prove it.
7. `scripts/pnf_trialectic_covariance_gluing_negative_control.py`: exact rational counterexample, three pairwise PSD 2×2 charts each with rho=−3/4 (determinant 7/16), but global 3×3 ones-vector quadratic −3/2 (negative eigenvalue −1/2). The exact Fraction equalities were verified locally.
8. `scripts/pnf_three_branch_scatter_exact.py`: source-independent rational pooled-scatter identity with three groups and two nonnegative between-group outer products. An independently executed local version passed 320 parameter combinations spanning feature dimensions 1..5 and group sizes 1..4 each.

### Why the gluing correction matters economically and for PNF

For disjoint source groups A, B, C with sizes a, b, c, means μ_A, μ_B, μ_C and μ_AB=(a μ_A+b μ_B)/(a+b), their pooled *unscaled centred scatter* is exactly

S_ABC = S_A + S_B + S_C
      + [ab/(a+b)] (μ_A−μ_B)(μ_A−μ_B)^T
      + [(a+b)c/(a+b+c)] (μ_AB−μ_C)(μ_AB−μ_C)^T.

This identity must be paid for the **same source and same feature coordinates**. Its two additional terms are PSD and are essential to pooled risk modelling or grouped PNF structure. If one merely glues independent pairwise covariance charts, PSD need not survive; the exact rational negative control demonstrates the obstruction.

### Remaining exact maximum cut (including kernel status)

P0: Agda 2.9 kernel-check *all* changed modules (especially the generic observer chart and the new triple pooled PSD proof); repair any types/implicit parameters. No kernel success is claimed here.

P0: Derive `pooledThreeGroupScatterIdentity` from actual same-source finite groups in Agda instead of supplying `pooledQuadraticIdentity` as a field. Derive the exact two between-group weights and preserve selected means/normalisation.

P0: Instantiate a genuine checked `FiniteFieldRankNullityOwner` and `CovarianceZeroSpectrum` from selected finite-dimensional field/spectral infrastructure; the previous rank-nullity mathematical proof and source-specific factorisation are authored but owner instantiations remain OPEN.

P1: Construct an actual numerical chart with compatible eigenvalues from **the same global covariance** and validate MP null hypotheses by PNF source/temporal/hierarchy group. Pointwise `NoiseClassifier` naturality cannot justify computing eigenvalues separately on patches or replacing a global operator by glued local PSD matrices.

P1: Establish an actual covariance-preserving group action or field transport under the 369/27 chart maps if desired: mere T^9 carrier bijection does not preserve Euclidean inner products, covariance, eigenvalues or source-semantic meaning.

P2: Replay original PNF activation matrices (not external Fleet planning labels); retain separate provenance and semantic promotion gates. For economics, test sector and common-market covariance plus three-group pooled risk out of sample; evaluate shrinkage and MP bulk cleaning against other estimators and Nashi cost gates.

P3: Only if independently supported, construct a literal sheaf/stack or cobordism-level operator identity; do not infer TQFT, global PSD, causality, psychology or economic alpha from finite chart/pants compatibility.

**Verification:** New Agda proofs are *authored and committed*, not typechecked in Agda 2.9. Independent local rational computations checked the negative-control values and 320 three-group pooled-scatter cases; the exact copies committed to GitHub have not been rerun in a local Git checkout. No original PNF or S&P 500 data was replayed during this round.

## 17. Native balanced-ternary, time-indexed fibre, hyperfabric and actual trader state machine (2026-11-10)

### Original architectural owners audited and reused
- `DASHI.Algebra.Trit` and `DASHI.Algebra.BalancedTernaryFiniteCarrierExact`: actual signed `neg/zer/pos` carrier and `Trit^n ≃ (Fin 3)^n` enumeration. A trit is **not** a sufficient statistic for a continuous magnitude; `PNFHistoryTimeNativeTritActivationExact` supplies the precise same-source equality when a panel truly is ternary-valued.
- `DASHI.Core.IndexedRelationalHyperfabricSpineExact.IndexedFabric`: source-bearing dependent fibres over `Vec Trit.Trit depth`. Generic ontology address depth is not the financial asset count and never automatically the MP sample size.
- `DASHI.Reasoning.HistoryTimeIndexedConsumerFibreExact`: selected live fibre and consumer vary with `(history,time)`; producer refinement preserves consumer version/closure; consumer revision requires separate re-audit.
- `DASHI.Reasoning.TypedHyperfabricCore` and `DASHI.Cognition.PNF.FibreNaturalDeltaTransportExact`: local stalk updates must commute with restrictions; an updated global section carries its own source receipt. This is not automatic covariance preservation.
- `DASHI.Core.TemporalPromotionNonRetroactivityBidiExact` and `DASHI.Core.TemporalStrandProvenanceBidiExact`: later source receipts cannot make earlier consumers/source states retrospectively admissible.
- `DASHI.Finance.TemporalMarketFibreExact`, `PointInTimeUniverseFibreExact`, `DeepStatArbFibrePipelineExact`, `DashiTradeFibreBridgeExact`: point-in-time source universe, historical constituent membership, factor method, residual, policy, portfolio, execution and realised-outcome provenance all remain separate.

### Exact Agda implementation committed (source-authored, kernel **not yet accepted**)
1. `PNFHistoryTimeTernaryCovarianceFibreExact`: source-selected `(history,time,situated Vec Trit)` indexed windows and covariance, with symmetry, canonical PSD reuse and same-window equality transport.
2. `PNFHistoryTimeVariableDimensionExact`: fully dependent `kAt(h,t)`, `pAt(h,t)`, source means, scale and covariance. Same-time rank/nullity lower bound uses the earlier finite-field owner, still uninstantiated. The fixed-dimensional model embeds conservatively; time-specific feature changes need an explicit covariance-compatible coordinate transport.
3. `PNFHistoryTimeMPSpectralModeExact` and `PNFHistoryTimeVariableMPSpectralExact`: every purported eigenpair is tied to the actual same-time covariance eigen-equation. MP aspect calibration must satisfy \(\gamma_{h,t}(n_{h,t}-1)=p_{h,t}\), with a correct square root, positive variance and arithmetic-preserving scalar bridge; the original `NoiseClassifier` and numeric-ABI nonpromotion theorem are reused.
4. `PNFHistoryTimeNativeTritActivationExact`: explicit source-raw-cell equals encoded \(−1,0,+1\) receipt; finite non-descent proof witnesses why sign alone cannot reconstruct magnitude.
5. `PNFHistoryTimeMarketSpectralFibreExact` and `PNFHistoryTimeTraderAdequacyExact`: actual time matched between selected source window, market fibre, historical universe and situated trade; permission/control delegated to original authority.
6. `PNFHistoryTimeConsumerAuthorityExact`: existing history-time producer refinement freezes consumer version and preserves closure; consumer revision remains governed by re-audit.
7. `PNFHistoryTimeHyperfabricDeltaExact`: constructs a globally compatible new section from coherent vertex/edge deltas with original restriction naturality and an explicit fresh update provenance receipt.

### What "inadequacy" meant in the 55-second S&P 500 reel
At ~44–47 seconds the user-supplied transcript says that **under the MP null edge this sample cannot separate signal from noise**. The surrounding claims concern finite-sample correlation noise, shuffled stock returns, a large market factor, some sector factors and MP bulk eigenvalue clipping. There is no assertion in the reel that all trading should be forbidden or that an outlier guarantees prediction.

This is an estimation-sufficiency and hypothesis-identification failure, **not** a direct BUY/SELL decision. In an actual time-indexed trading architecture, an under-edge eigenmode lacks evidence to become a factor claim; an uncalibrated MP null or source/leakage failure can separately mark a *risk estimator* inadequate. This distinction is necessary to avoid an arbitrary always-HOLD policy that contradicts the reel's informational meaning.

### Actual trading state and its formal limits
- `DASHI.Trading.PermissionKernel.MarketWindowState` stores `shape,energy,persistence,liquidity,risk` **and** `modelCost,residualCost,riskPenalty,currentPermission`. Its quotient/readout uses only the first five; `authorize` yields `ACT/HOLD/BAN`, and `permissionKernel` is idempotent. This kernel is an authorization classifier, **not** a return predictor, covariance validation procedure, realized execution model or full order-state machine.
- `DASHI.Trading.DashiTradeDreamOptionConeExact.TradingFabricState` adds `proposal,inventory,liquidity,uncertainty,history,risk`. The same LONG proposal has distinct BUY availability when inventory differs; the exact existing non-factorability theorem rules out a direction-only BUY compiler.
- `DASHI.Finance.TradingPermissionActionRefinementExact` interprets BAN as prohibiting exposure increases but allowing appropriate reduction or flattening; it explicitly separates permission from execution intent. `TradingControlPermissionSeparationExact` shows a permission surface alone cannot reconstruct all control decisions.
- `DASHI.Finance.DeepStatArbFibrePipelineExact` separates residual factor fit, causal learned policy, portfolio, execution, cost and realised return, and uses PIT-specific rolling protocol. None is implied by an MP noise-edge result.
- `DASHI.Cognition.PNF.NashiDecisionProofBridge` requires explicit `TextMarketJoinReceipt` conditions: binding, time alignment, revision completeness, entity resolution, no lookahead, mechanism link and regime compatibility. A market narrative or an MP candidate does not bypass these.

### New trader inadequacy max-cut
`DASHI.Information.PNFMPTradingInadequacyControlExact` defines **five explicit source-adequacy statuses**: `inadequateSample`, `uncalibratedNull`, `qualifiedRiskEstimate`, `bulkOnlyQualified`, `outlierCandidateQualified`. For a *policy-selected* risk-estimation warning only, inadequate sample/null changes an otherwise `clear` legacy risk gate to `caution`; it never clears `blocked`. Qualification or a bulk-only/outlier observation leaves the original gate unchanged. `guardedPermissionIsOriginalKernel` ensures permission is computed by the actual legacy kernel. For the richer Dream state, uncalibrated/inadequate samples can make the uncertainty coordinate `uncertain`, closing the canonical BUY branch while not erasing history, inventory or liquidity. These are **policy adapters**, not theorems that MP itself commands HOLD.
- Exact source witnesses: `inadequateSampleWithdrawsNewRiskPermission`, `uncalibratedNullWithdrawsNewRiskPermission`, `bulkOnlyDoesNotBlockAnOtherwisePermittedState`, `uncalibratedDreamBuyUnavailable`, `qualifiedMPDoesNotOverrideInventory`, `noSpectralAdequacyOnlyBuyCompiler`.
- Critically, `permissionQuotientDoesNotDetermineCost` exhibits identical authorization quotient with different model costs, and `noPermissionOnlyEconomicCostModel` refutes recovering economic cost from the permission surface alone. Economic benefit still requires costed held-out forecast/realisation tests, not just kernel idempotence.
- `PNFHistoryTimeTraderAdequacyExact` binds the quality status to a selected `(history,time)` market/trade fibre and delegates to the existing `TradingPermissionActionRefinementExact.compileIntent`; the original static-later-universe backward-transport obstruction is reused.

### Native point-in-time numerical reuse
`scripts/pnf_history_time_mp.py` consumes `scripts/pnf_marchenko_pastur_numeric.py` rather than implementing MP anew. It selects rows whose **event time and available-at time** are <= as-of, independently selects feature IDs whose historical membership was known at as-of **for the same history and source**, and carries consumer version. A newly entering feature is never backfilled into older incomplete rows. `tests/test_pnf_history_time_mp.py` adds source/history, first-admission, no-lookahead, trit quantization and consumer-version tests. Both files are committed but the exact GitHub versions were not run from a checkout in this environment; no test-pass claim follows from merely committing them.

### Maximum cut still OPEN
P0: Agda 2.9 kernel-check/repair all new and imported modules; the existing typed ring's API and universe constraints are not verified by delimiter scans.
P0: Instantiate real finite-field rank/nullity and spectral zero-multiplicity owners; the source-specific factorization and bound are authored but not formally closed without them.
P0: Source-construct true means, n−1 inverses, actual term-level centred values for time-varying/hierarchy-typed observations; forbid arbitrary toy receipt substitution.
P0: Prove a selected time/history hyperfabric restriction transport actually preserves a particular covariance quadratic before reusing the same spectrum across chart/time changes.
P1: Connect variable-dimension MP eigen-equations to a selected certified numerical/eigendecomposition engine, actual iid/dependence nulls, and financial/PNF separate calibration. The full analytic MP limit remains open.
P1: Provide a genuine independently verified out-of-sample risk-quality criterion for `qualifiedRiskEstimate`. Its existing policy constructor must not be interpreted as an automatically earned empirical admission.
P2: Run exact committed Python tests, replay original PNF activation windows and historical S&P asset-universe returns, compare MP clipping/shrinkage/factor models using rolling PIT evaluation, report realised risk/turnover/impact with a no-lookahead action ledger.
P2: Bind qualified covariance-risk information only as a risk observation to the real Nashi text-market join and dashiTRADE option cone; do not invent direct mode→alpha or mode→order semantics.

## 18. As-of MP covariance-risk qualification / actual trader state machine (2026-11-10)

The 55-second source reel makes a **sample-identifiability** assertion: a mode under the MP bulk edge is not distinguished from noise by that sample. It does NOT establish that cleaning improves out-of-sample covariance prediction, provides alpha, or requires that all trading stop. In the actual DASHI trader, `PermissionKernel` is only an ACT/HOLD/BAN authorization quotient, `DashiTradeDreamOptionConeExact` additionally tests inventory/uncertainty/history/liquidity, `TradingPermissionActionRefinementExact` protects risk-reducing exits, and `DeepStatArbFibrePipelineExact` owns factor fitting, learned policies, execution, impact and realised performance.

**New source terms committed, not Agda-kernel checked:**
- `DASHI/Information/PNFTimeIndexedRiskQualityLedgerExact.agda`: finite held-out squared-error loss computed from original predicted and realised natural-valued risk scores, not arbitrary pass/fail flags. Every fold has a strict forward evaluation path, prediction publication no later than decision, and outcome availability no earlier than its event. `QualifiedRiskEvidence` requires a nontrivial fold count and actual cleaned-vs-baseline loss ordering; `qualityReceiptEnablesSelectedRiskStatus` is explicitly *conditional* on that proof. This is an exact integer-coded loss ledger, NOT a full real covariance error proof. `noMPLabelOnlyRealizedRisk` uses existing intersectional nonfactorability to prove that an MP null-band label cannot determine realised risk.
- `DASHI/Information/PNFAsOfQualifiedTraderRiskExact.agda`: held-out evidence cannot qualify a current `(history,time)` risk assessment unless all evaluated outcomes were available by that decision's PIT timestamp; historical source, history, asset/feature universe and consumer version must match. `qualifiedHeldoutCannotCreatePermission` delegates to the original `Trade.legacyPermissionFor` without granting new action authority; exposure control still passes through `Refined.compileIntent`.

**Executable point-in-time pipeline committed:**
- `scripts/pnf_history_time_risk_walkforward.py` imports the existing `pnf_marchenko_pastur_numeric.py` and reuses `TemporalObservation`/`HistoricalFeature`. It fits same-source, complete-case covariance only to rows with event time and availability <= forecast as-of, and selects the one next event only for *subsequent* forecast-error scoring. Reports baseline and MP-clipped predicted portfolio variance against realised squared return, never an order or alpha.
- `assess_walkforward` now REQUIRES explicit `qualification_asof`, rejects outcomes unavailable by that time, future-issued forecasts, repeated held-out events (which cannot fabricate fold count), mixed histories/sources/consumer versions/feature sets, and too few folds. It reports held-out comparative risk loss and no-trade/no-alpha booleans.
- `tests/test_pnf_history_time_risk_walkforward.py` has synthetic regression coverage for strict forward evaluation, delayed source availability, a changing feature universe without historical backfill, cross-source and future-target rejection, duplicate target events, hindsight certification, repeated fold suppression and minimum fold admission.

**Verification accounting:** These files are committed to draft PR #1480. The Agda binaries/Nix environment were unavailable in the current tool container; new Agda proof terms are **not kernel accepted**. The exact new GitHub Python file/tests have **not** been run from a checkout in this execution environment; do not present source-authoring as test-pass. The previous locally executed synthetic MP and rational gluing results remain valid for their own fixtures only.

**New decisive P0 gates:** (a) check/repair transitive Agda imports, (b) source-derive loss labels for the same real covariance/portfolio positions, not merely integer-coded forecasts, (c) prove as-of provenance for the actual producer/market feed with available-at timestamp semantics, (d) derive a calibrated absolute risk error/tolerance policy before granting `qualifiedRiskEstimate` to Nashi, (e) run committed Python tests against real PIT financial history and separately the original PNF source activation panel. Winning a selected synthetic loss comparison is neither statistical significance nor economic trading surplus.

## 19. PIT knowledge-time correction for constituent removals

A feature's recorded last valid date is not necessarily the date a historical trader or PNF consumer could know the removal. Source-bound replay must distinguish **event/effective time** from **knowledge/availability time**, preserving the repository's general history/time-indexed fibre principle and its no-retroactive-promotion rules.

In `scripts/pnf_history_time_mp.py`, `HistoricalFeature` now carries `last_valid_known_at`. A supplied `last_valid_at` without its knowledge timestamp is rejected, instead of silently excluding observations from earlier historical universes. Prior to the announcement time, a later-discovered end date does not retroactively remove that feature; once known, the actual validity bound applies.

`scripts/pnf_history_time_risk_walkforward.py` uses exactly the same PIT membership semantics. New regression cases exercise an asset whose end validity is known only later, proving the earlier replay still contains it and that an undated removal is rejected.

**Important:** This is still a finite as-of data selection policy, not proof that a particular third-party market feed supplies historically versioned constituent disclosures. Source providers must furnish both effective and knowledge time, plus any publication/revision history; missing metadata fails closed.

### Verification and decisive remaining work
- New Agda finite ledger, native as-of risk admission, Nashi/trader gate integration: committed **but not kernel checked**. No installed Agda or Nix toolchain is available in the execution environment.
- New Python as-of replay, walkforward risk evaluation, and unit tests: committed **but exact branch copies not executed from a checkout**. Previous independent local MP and rational pooled-scatter tests do not verify these new modules.
- The held-out risk comparison is a selected squared-error test of an ex-post squared return proxy. It is not a significant estimate of conditional true covariance and cannot authorize alpha/trading or semantic promotion.
- P0: actual source-feature/event availability, field-based rank/nullity and symmetric spectral owners, same-source time-indexed covariance transport, and kernel verification.
- P1: validate analytic MP assumptions and numerical calibration under serial dependence, heteroskedasticity, null resampling, regime changes and multiple outlier testing.
- P2: run the branch tests on the original PNF source windows and properly versioned stock histories; compare the heldout risk forecasting performance with shrinkage/factor baselines and separately costed portfolio outcomes.

### Strict native feature-admission floor (subsequent P0 correction)

In addition to as-of event availability and historically known delistings, both `pnf_history_time_mp.py` and `pnf_history_time_risk_walkforward.py` now enforce a common **feature-admission floor**: a selected complete-case observation cannot predate the first-known/admitted time of *any* selected feature. Otherwise a subsequently backfilled feature value could leak into earlier rows even though all raw dictionary keys are present. New synthetic negative-control regressions deliberately backfill late features and assert the historical window stays truncated.

This is a conservative historical constituent/PNF coordinate policy. It may exclude pre-membership price observations that an alternative specified and justified research protocol wishes to use. Such an alternative must define and source its own historical availability/admission semantics explicitly rather than silently bypassing the point-in-time constraint.

**Verification:** The tests are newly authored and committed; the exact branch code is still not executed locally from a checkout. No unverified test count is reported as passing.

## 2026-11-11 — Cross-PR epistemic observer / Marchenko–Pastur highest-alpha weld

**Actual live owners checked:** PR #1480 `pnf-mp-maxcut-2026-11-09` (original audited head `6ef9c6525269ca661fe6e06945f64fcf056e4863`), PR #1465 `chatgpt/esd-pnf-trialectic-spectral-world-20261104` (source on separate parent #1458), historical PR #37 `PNFSpectralGeometry`, and PR #1479 `chatgpt/epistemic-power-maxcut-20261109` (epistemic cognitive-warfare/cortisol work). **Do not import PR #1479-only modules into #1480 without an explicit branch merge.**

**New source-written theorem** in `DASHI/Information/PNFMPObserverNonPromotionWeldExact.agda`:
- `taskOnlyMPClass`: the actual MP `NoiseClassifier` applied to an arbitrary candidate eigenvalue estimator that sees the existing `Work.observedTasks` source record only. No empirical eigenvalue is fabricated.
- `taskOnlyMPClassCannotDetermineIntent`: the existing `Work.sameTasksCannotIdentifyPurpose` and canonical `IntersectionalNonFactorability.rechartingCannotRecoverErasedPhenomenon` imply that no MP threshold/rechart can recover controller intention from observationally identical task histories.
- `publicOutcomeMPClassCannotRecoverRetention`: post-processing a public accepted-disposition observation with any numeric MP chart/classifier cannot recover unobserved retaining work.
- `noMPClassCanAuthoriseNumericPromotion`: reuses the original empty `PNFSpectralNumericABIPromotion` type.
- **Scope:** a source-level distinguishability/no-go result; not a claim that an MP eigenvalue of true independent human outcomes is itself a random matrix or that a measured spectral outlier is evidence of manipulation. Attribution for MP theory belongs to Marchenko and Pastur; epistemic three-task modelling is DASHI original work motivated by its separately cited authors.

**Original sibling source owners already implemented (DO NOT REDO):** `PNFFiniteGramPositiveExact`, `PNFCentredCovarianceExact`, `PNFCovarianceQuadraticIdentityExact`, `PNFCentredFiniteRankNullityBridgeExact` / `PNFFiniteRankNullityBridgeExact`, `PNFHistoryTimeVariableMPSpectralExact` with same history/time finite covariance eigen-equations and aspect ratio `p/(n-1)`, `PNFMP36927ChartNaturalityExact` with pointwise MP classification commuting with the **same** 3-chart observer gluing, and `PNFMPTradingInadequacyControlExact` preserving the original trader permission kernel. No bypass around these original sources.

**Phases and remaining high-alpha exact leaves, in priority order:**
- P0 **kernel check** the new negative-control theorem and all dependent `PNF`/epistemic imports; no kernel pass asserted.
- P0 **same-source calibration:** `pnfWindowActivationEquality`, `centredSampleMeanIsOriginal`, `sampleScaleEqualsInverseNMinusOne`, `pnfEmpiricalNullCalibrated`; actual source rows, missingness, sample-window and positive variance needed.
- P1 **finite spectral mathematical closure:** `sampleCovarianceForcedZeroMultiplicity`, `sampleCorrelationDiagonalTrace`, eigen-decomposition reconstruction and PSD cleaning; check existing rank-nullity owners before writing anything new.
- P1 **asymptotic MP:** `marchenkoPasturZeroAtom`, `marchenkoPasturDensityNormalised`, `marchenkoPasturMomentFormula`, `marchenkoPasturStieltjesEquation`, `marchenkoPasturWeakLimit` and separately `marchenkoPasturExtremeEigenvalueBounds`. These are OPEN, not implied by finite Gram PSD or MP edge formula fields.
- P1 **same-action exceptional spectral comparison:** on separate #1479/#1098/#1106/#1389, compute actual common-actor character decomposition (not just count 240 or E8 weight-two dimensions); if one wants to compare Gram empirical spectra, one must source-pay both covariance objects and their normalizations.
- P2 **ESD/PNF context:** PR #1465 has a selected same-world eigenbasis and required MP calibration, but no original full-text-reviewed population-specific null proof or semantic authority; preserve current PNF candidacy and observer provenance.
- P2 **human/biology/cognitive warfare:** source-specific physiological measurement and controller intent remain independently unidentifiable from MP class; do not equate a covariance outlier with stress injury or unlawful manipulation.
- P3 **real numerical replay and walk-forward** on source-pinned histories, held-out nulls, actual financial/clinical measurement units; no forward data leakage, no invented bpp/return or harm claim.

**Status:** one new cross-owner Agda source committed to PR #1480; no Agda kernel check, asymptotic MP convergence proof, real-world causal claim or PR merge made in this pass.

### Highest-alpha temporal-null sensitivity implementation (2026-11-11)

**Committed executable owner**: `scripts/pnf_mp_temporal_null_sensitivity.py` and `tests/test_pnf_mp_temporal_null_sensitivity.py`. Two explicit nulls: (1) asymptotic unit-variance iid MP band with `γ=p/(n−1)`, using the pre-existing `MPNull`; (2) empirical 95th percentile of per-column circular-shift surrogate maximum eigenvalues, with exact seed, window label, data source and sample count. The second null preserves each observed column's temporal autocorrelation and marginal distribution but destroys/rearranges cross-column clock alignment. Neither is a universal valid finite-sample significance test; circle shifts may be inappropriate for nonstationarity, shared trends, missingness, group structure or causal dependence.

**Executed independent exact same-algorithm numerical reproduction (synthetic only)**: 120 rows × 24 independent-column Gaussian AR(1) paths with ρ=0.8 and RNG seed 20261111. Largest measured sample correlation eigenvalue 2.9990378735740615; iid MP upper edge 2.0998580985470516; circular-shift surrogate 95th percentile of 100 maxima 3.6411209899661743. Thus `iid_above_edge=true` while `surrogate_above_empirical95=false` on this deterministic sample. This is a constructive **counterexample to treating an iid MP-edge exceedance as a null-independent signal**, not a source-specific market/ESD/PNF finding. The committed regression is based on the same algorithm but **not replayed from the GitHub branch in this container**.

**P1/P2 remaining closure:** `pnfNullAssumptionsAssessed` and `pnfEmpiricalNullCalibrated` need actual original data and an appropriate justified time/group preserving null; `pnfStableSpectralSubspace` requires repeated/held-out windows and projector stability; `mpOutlierIsCandidateOnly` is already enforced by the native source classification owners, not clinical, manipulation or trading authority. The strictest future reproducible test should compare iid, block, group and time-aware nulls with appropriately validated exchangeability assumptions, and log failure rather than assert causal meaning. See original PR #1465 same-world ESD eigenbasis and PR #1479 non-factorability/observer-gate work.

## 2026-11-11 next max-cut — finite temporal-information obstruction and same-window zero spectrum

**New original source-written Agda modules on PR #1480:**
- `DASHI/Information/PNFMPTemporalOrderingNonIdentificationExact.agda`: four-sample exact countermodel with `alternating=[0,1,0,1]` and `clustered=[0,0,1,1]`. Both have **sample sum 2**, **sum of squares 2** and therefore exactly equal scalar (univariate) centred sample variances; lag-one product sums are **0 and 1**. Named lemmas: `sameStaticMoments`, `differentLagOne`, `staticMomentsCannotIdentifyTemporalStructure`, `noStaticCovarianceMomentOnlyAutocorrelationDecoder`, `arbitraryStaticRechartCannotRecoverLag`, `alternatingLagZero`, `clusteredLagOne`. This is a finite mathematical obstruction: a static covariance/MP rechart cannot reconstruct temporal ordering from its already-collapsed observation. It does **not prove the real data violate iid**, nor does it generate a stochastic ensemble or calibrated null.
- `DASHI/Information/PNFHistoryTimeZeroSpectrumExact.agda`: same-owner `HistoryTimeZeroSpectrum` requires `PNFFiniteRankNullityBridgeExact.CovarianceZeroSpectrum` for the exact `PNFHistoryTimeVariableDimensionExact.actualWindowAt` and `scaleAt`; `forcedZeroModesForActualWindow` derives (p-(n-1)\le zeroEigenvalueMultiplicity) for the **selected same-matrix** covariance. This does NOT supply the separate finite-field rank-nullity owner or actual eigenbackend spectral=kernel equivalence. Those remain P0/P1 unpaid original-source gates. Do not label unconditional zero-eigen multiplicity closed.

**Refined phase/lemma matrix:**
- P0 `pnfNullAssumptionsAssessed`: **finite static-moment temporal non-identification source-written COMPLETE**; empirical original-data dependence, stationarity, group structural dependence, missingness and source-selected surrogate/null calibration remain OPEN.
- P0 `pnfWindowActivationEquality`: actual original PNF observation rows, same sample window/candidate coordinate and source-hash provenance still OPEN. Finite rank and centred means already advanced; don't duplicate.
- P1 `sampleCovarianceForcedZeroMultiplicity`: same-window `forcedZeroModesForActualWindow` source-written **conditional**, actual real-field rank and spectral equality receipts OPEN.
- P1 `marchenkoPasturWeakLimit` and independent extreme-eigenvalue law: OPEN; no finite countermodel is a weak-convergence theorem.
- P2 `pnfEmpiricalNullCalibrated`: synthetic AR1 vs circular shift and finite non-identification source-written, **original valid iid/temporal/group null remains OPEN**.
- P3 clinical, legal, epistemic/intent, trade permissions: MP statistics alone cannot decide; original source owners and authority rules separately required.

**Independent executable check this round:** exact Python root-set action enumeration across E8 fifth-pair coordinates 4,5,6,7 yields same fixed points [60,60,60,60,126,126,126] and 34 orbits each. This supports the specifically selected #1479 representation no-go, not a general exceptional equivalence claim.

**Verification:** committed source-written Agda, no Agda kernel run. External original PNF panel, original null model, MP probability limit and selected physical E8 intertwiner remain unpaid.

## 2026-11-11 dependency correction — independent PR #1480 buildability

**Important corrected error:** Original `PNFMPObserverNonPromotionWeldExact.agda` source (first committed this pass) directly imported `DASHI/Governance/EpistemicPowerHistoryAndNonSubstitutionExact.agda`, which is in **PR #1479 only**, not present on master or #1480. Such a source would fail file resolution and was **NOT an independently valid Agda module on #1480**. Replaced it at commit `b110844912fe71c099a6b73ea6637a97556c2048` with a wholly generic theorem requiring only modules on #1480 and master.

The corrected exact declarations are:
- `mpClassOfObserver`: source-selected observer + numeric estimator + original MP classifier.
- `mpRechartCannotRecoverErasedOutcome`: supplied source-owned `NF.NonFactorabilityWitness` implies no MP classification can recover erased outcome; calls canonical `rechartingCannotRecoverErasedPhenomenon`. This is a REAL generic negative result, not a source-specific instantiated theorem on #1480.
- `mpClassCannotPromoteNumericABI`: directly invokes original empty numeric promotion theorem.
- The **concrete** source witness `Work.sameTasksCannotIdentifyPurpose` remains on #1479 until the two PRs are deliberately stacked/merged or compiled in a joint test checkout. No accidental cross-PR module import remains.

**Prior text correction:** passages naming `taskOnlyMPClassCannotDetermineIntent`, `publicOutcomeMPClassCannotRecoverRetention` and `noMPClassCanAuthoriseNumericPromotion` as currently existing #1480 declarations describe the initial unbuildable draft; they have been replaced by the three generic declarations above and must not be reported as current. Same-world source-specific instantiation remains OPEN. This discovery lowers the MP cognitive-warfare seam from claimed direct integration to generic standalone mathematics with explicit dependency.

**Other scope:** the finite temporal-ordering negative example and conditional same-window zero-spectrum modules remain source-written; no Agda kernel test was run.

## 2026-11-11 continuation — multivariate covariance vs temporal ordering

**New Agda owner:** DASHI/Information/PNFMPStaticGramTemporalNonIdentificationExact.agda. It imports existing finite temporal-ordering, core non-factorability, and actual MP observation rechart on the SAME #1480 branch; no #1479-only imports.

Synthetic 4×2 histories are [(0,1),(1,0),(0,1),(1,0)] and [(0,1),(0,1),(1,0),(1,0)]. Both have exact column totals (2,2), full raw Gram [[2,0],[0,2]] and equal centered covariance (over any ordinary characteristic-0 field with usual sample normalization). Chronological lag-one first-column product sums differ: 0 versus 1.

**Exact source-written lemmas:**
- sameColumnTotals, sameEntireRawGram, equalFullTwoColumnStatistics.
- sameCentredCovarianceCrossProduct: cross-multiplied equality of all 2×2 centered covariance entries, with source n=4; no unlicensed field division.
- equalFullGramButDifferentTemporalLag, noStaticTwoColumnSpectralDecoder, noRechartedTwoColumnSpectralDecoder.
- twoColumnMPClassificationCannotRecoverTemporalLag: ACTUAL #1480 MP classifier applied to an arbitrary covariance-statistic-based estimate cannot reconstruct the lag-one difference.
- totalsExactlyTwo and offDiagonalGramZero: finite computational checks.

**Independent local arithmetic reproduction:** two matrices verified totals (2,2), Gram (2,0,2) and lag 0 versus 1. No Agda kernel check performed. This is a synthetic mathematical no-go, NOT an actual iid model assessment or causal claim.

**Remaining phases:** P0 pnfWindowActivationEquality / pnfNullAssumptionsAssessed need original authenticated data and selected null with temporal, group and missingness assumptions. P1 sampleCovarianceForcedZeroMultiplicity remains conditional on real field rank/nullity and same-matrix eigenvalue/kernel equality; marchenkoPasturWeakLimit and extreme-eigenvalue convergence need independent probability-space and moment/tail proofs. P2 calibrated empirical nulls, held-out projector stability and source-specific PNF authority remain open. Avoid treating MP spectral threshold as ability to recover omitted time ordering or to infer actor intent.

### Executed finite regression: full covariance and identical eigenspectrum

The locally executed deterministic regression `tests/test_pnf_mp_static_gram_temporal_nonidentification.py` passed (1/1 test). On the two selected 4×2 panels the actual unbiased centred covariance equals `[[1/3,-1/3],[-1/3,1/3]]` in both cases and the actual eigenvalue list equals `[0,2/3]`. The lag-one statistic differs 0 versus 1. The test is now committed on #1480. Hence any deterministic MP statistic/classifier based solely on that covariance and eigenvalue list is provably incapable of recovering the ordering distinction. This is a finite experimental cross-check of the source-written Agda negative control, NOT the MP asymptotic law or a statement about actual data.

The selected original Bałaban source symmetry check on #1479 confirms the last physical P0 leaf is **literal scalar source identification and box environment compatibility**, not the already existing conditional generator symmetry or four-representative evaluator transport. No physical proof certificate was manufactured.
