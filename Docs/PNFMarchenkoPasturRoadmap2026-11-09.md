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

**T6 (reported spectrum caveat).** Reported values 74.5526, 18.8350, 5.5865 sum to 98.9741. Only IF they are eigenvalues of a p=120 *correlation* matrix with trace 120 does their trace fraction equal 98.9741/120≈0.8247842. Historical experiment has not been rerun or independently validated in this branch.

## 2. Phases, exact remaining declarations and deliverables

### Phase A — exact finite carrier [P0 maximum cut]

A1 `finiteGramPositiveSemidefinite`: IMPLEMENTED as theorem conditional on finite-sum laws; kernel check PENDING.
A2 `sampleCovarianceIsGramQuadratic`: OPEN. Construct actual finite centred activation matrix and show the covariance quadratic equals sum of squares divided by n−1, with positive scale.
A3 `sampleCovarianceSymmetric`: OPEN. Derive symmetry from that actual construction, rather than supplying it as a field.
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
D3 `historicalEigenvalueTraceConsistency`: OPEN. Check all 120 eigenvalues, trace=120 if correlation, empirical uncertainty.
D4 `sourcePreservingNullNegativeControls`: OPEN. Hold representation source and temporal constraints fixed while testing residual structure.
D5 `PNFSemanticPromotionReceipt`: OPEN. Explicit independent source, semantic, stability, and non-artifact warrants; no eigenvalue-only promotion.
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
- An eigenvalue-only threshold is not a finite-sample hypothesis-test p-value.
- S&P 500 correlation behaviour is not evidence that PNF has the same ensemble law.
- dashiTRADE's 'eigen-event' classification is an action boundary, not literally a covariance eigenmode.
- The new finite Agda file has not been accepted by Agda 2.9 in this environment.
