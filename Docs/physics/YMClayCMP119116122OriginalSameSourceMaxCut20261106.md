# CMP119 + CMP116 + CMP122 on ONE original Wilson source: exact max-cut audit
**6 November 2026 • YM parent PR #1444 • Golden Agda owners • source-head audit at 191590060b56b19644662fc3e0a9421238082bb3**

## Correction to the earlier max-cut
Do **not** start by proving fresh CMP119 RG, CMP122 nonlinear UV stability, CMP116 cluster/localization, KP summation, or normalized-log/covariance algebra. The repository already has source-indexed owners for all these, much of it with precisely the source-first arguments required. Build the *original Wilson–Gibbs specialization* to their hypotheses, then project their existing results. A published theorem authority and a `machineChecked` compiler under a record premise are not the same as a source-specific witness to that premise.

The literal Agda core of the new source-conserving wiring is `DASHI/Physics/YangMills/YMClayCMP119122116SelectedProducerWeldExact.agda`:

1. `cmp119122BetaAndCMP116PotentialSameSource`: from ONE `BetaDrivenCompleteDensityInputs` and its actual `BetaDrivenLocalizedEffectiveActionFamily`, constructs the **conjunction** of the literal beta-history coupling identity and the CMP109/116 localized component-sum equality for that exact CMP119 density. It does not introduce a second density or new mass-gap measure.
2. `sameLiteralR342SourceFiniteCovarianceDecay`: existing `R342.LiteralTrajectoryCMP116Source` → `asPublishedLiteralSelectedLocalization` → **literal R467 original selected connected-covariance physical envelope**.
3. `sameLiteralR342SourceYieldsR479TransferGap`: the SAME source, plus the already-owned selected limit and energy semantics, gives the R479 positive transfer-gap core without an independent R467 record.
4. `sameLiteralR342AndLocalRateYieldsGap`: uses R482/R301 to *derive* candidate positivity from the SAME reconstructed spectrum's local rate, avoiding the extra arbitrary positive-gap token.

These are **source-written proof terms awaiting Agda kernel acceptance**, and still require the actual R342 input on the selected Wilson family. They are intended to delete duplication from the proof graph, not to promote a conditional source to the Clay endpoint.

## Exact source-producer and consumer audit

| Source / owner | Already source-written or standard imported | Narrow actual source-specific equation to instantiate |
|---|---|---|
| `Balaban1989BetaDrivenCompleteDensityFlowExact` | `betaDrivenCompleteDensityFlow`, coupling identity and smallness from original finite beta history | `WilsonDensityAt(a,L) = selected CMP119/CMP122 densityAt(k)` including Wilson trace, gauge fix/ghost, full E/R/B/V and Jacobians when the source action uses them |
| `BalabanPublishedUVStabilityNonlinearRGCoreExact` + `BalabanCMP122PublishedFourDimensionalUVStabilityExact` | published nonlinear UV stability/active Section-2 invariant under the selected source hypotheses, not a new generic one-step stability theorem | physical chosen Wilson/ghost/Haar/background and exact effective-density `ActiveEffectiveDensityFlow` representation, including CMP119↔CMP122 carrier dictionary |
| `BalabanCMP119PhysicalTOperationWeldExact` | assembled density equals physical localized T-operation on a typed input; nonnegativity and finite slow field realizers derived | original source assembled density = selected physical T-operation and strict positive support on original same density |
| `BalabanCMP119AnchoredNormalizedExpectationSourceExact` | published anchored numerator/denominator cancellation + localized normalized expectation (CMP119 Sect. 3) | actual renormalized Wilson/local physical insertion belongs to that very analytic anchor class |
| `BalabanCMP119CMP122BoundaryReinjectionSourceExact` | CMP119 boundary analytic/localized terms; CMP122 large-field R-operation reinjection preserves the source class | literal periodic polymer/boundary/domain dictionary; **do not re-prove published boundary mechanism** |
| `BalabanCMP116119NormalizedExpectationDerivativeRound281Exact` | published differentiated normalized expectation + mixed log/connected covariance adapter | selected physical two insertions map to the source's exact two J coordinates, root and support distance |
| `BalabanCMP116SelectedJApplicabilityRound309Exact` | source theorem vs selected T5 J-applicability split, not artificial covariance | actual original gauge-invariant local test pair is an admissible CMP116 marked pair on SAME density |
| `BalabanCMP116LiteralTrajectorySourceRound342Exact` → `BalabanCMP116LiteralTrajectoryToPublishedLiteralR467Exact` | common-domain/selected marked-source pipeline; R342→R467 compiler already source-written | `literalSelectedDifferentiatedLocalization` for that original pair AND physical envelope `sourceEnvelopeBelowSpectrumEnvelope` with a cutoff-/volume-uniform positive physical decay rate |
| `BalabanCMP116PublishedLiteralRateToGapRound482Exact` | R467 plus selected local energy/rate semantics constructs positive transfer gap, avoiding arbitrary positive-energy token | actual OS spectral generator, physical time units, density of selected local modes, no invisible lower-energy sector |
| `BalabanCMP122ROperationReflectionSupportCutExact` | literal positive/negative/crossing source polymer classification, equation (1.100) envelope on crossing | **actual crossing-kernel reflection-positivity theorem**: mere exponential bound is not PSD |
| `BalabanClayT5TypedContinuumDefectCauchyExact` | explicit dyadic defect telescope and fast-Cauchy real already exists | same original Wilson-renormalized observable at adjacent cutoffs, actual defect bound, signed telescoping and physical measure representation |
| `BalabanClayT5BoundedWeakCompactnessRound439Exact` + `BalabanClayT5SameFamilyContinuumRecoveryRound425Exact` | Markov/Prokhorov/full selected convergence and same-family OS compilation under exact source premises | literal physical compact-containment witness, determining weak-test algebra, actual expectation topology and RP-preserving limit |
| `BalabanClayPlaquetteNoncollapseContinuumCalibrationExact` + `BalabanClayT5CumulantLowerBoundNontrivialityExact` | explicit positive OS norm and uniform cumulant survival implications | same original Wilson lower certificates and counterterm/tail losses with verified sign/units |
| `YangMillsDirectSourceOSSameHGapExact` | explicit same-OS-H and gap attachment, physical distinction admitted | instantiate the selected original continuum source and the physical same-H + local sector/density, not a second abstract Hamiltonian |

**Prioritization correction:** the source-native marked-pair CMP116 path is the default B route. The supplementary Dobrushin/Perron physical-cube path is an alternate *sufficient* route, not an extra mandatory assumption. The CMP119 anchored expectation route is already better aligned with the one-step UV defect needed for the T5 Bishop real than an invented generic Lipschitz estimate.

## Four genuine same-object proof cuts remaining after imported mathematics

### Y.01. Original finite Wilson→CMP119/CMP122 exact carrier + action
For all selected cutoffs, volumes, field configurations and legal source gauges establish an explicit original equality (or a correctly measured gauge-fixed change of variables)
[
\mathbb E_{\mu_{a,L}^{\rm Wilson}}[F] =
\frac{\int F_{\rm selected}\, e^{-S_{119/122}(A,E,R,B,V)}\,d\nu_{\rm phys}}
{\int e^{-S_{119/122}(A,E,R,B,V)}\,d\nu_{\rm phys}}.
]
Do not pretend `RealAnalysisAxioms`, a `OneLinkProductHaar` record or two equal types prove this. For original compact SU(N), verify actual Borel Haar, measurable gauge factors, original decoder, partition positivity and noncommutative blocking; reuse the already implemented 1,024-link C3/64-pair/896-spectator code. If gauge fixing includes ghosts, demonstrate determinant/BRST/Ward compatibility, not an independent gauge-fixed measure assumption.

### Y.02. Literal selected insertions→published CMP119/CMP116 mark class
Construct the functions `sourceJLeft`, `sourceJRight`, `sourceRoot`, `supportDistance` from the actual physical local/loop observable. Prove the selected two derivatives are those of **the same original partition function** and source estimates. Reuse R281, R309, R342, R467 and the current new R482 direct compiler. This is an equality of source, coordinates and physical support—not only a name match.

### Y.03. Quantitative UV/IR *physical* tail and reflection compatible limit
Derive source-specific anchored expectation defects (sum_k epsilon_k(F)<\infty) and two-marked source envelope (C_F e^{-m d_{\rm phys}}), both with constants independent of cutoff/volume and explicit operator renormalization. Boundary reinjection and large fields must be included in the source density. The companion typed T5 defect theorem already turns defects into Bishop fast Cauchy, while R467/R482 consumes literal CMP116. Separately prove the **crossing** R-operation contributions preserve positivity of the reflected Gram form. Convergence of a positive matrix of source labels is insufficient without the same physical reflected test algebra.

### Y.04. Continuum noncollapse + OS/Clay semantics
From SAME selected source show a lower OS norm and a nonzero signed fourth cumulant, actual weak/Schwinger limit and Euclidean invariance, local field/test space, stress/Ward, OS same generator and full local spectral density. Derive (H_G|_{\Omega^\perp}\ge m_G I) in physical units and prove the group-indexed construction for the prescribed compact simple gauge groups. This is not delivered by a source `ProofLevel = machineChecked` under uninstantiated fields.

## BIDI acceptance and falsifiers
- **FWD 119/122→116:** a selected physical density and two legal source J coordinates must reproduce the exact original mixed second log derivative, connected covariance and source envelope.
- **BWD 116→119/122:** every marked source root/domain appearing in the supposed physical bound must trace to the selected Wilson density/physical T-operation and *the same* beta history, with no ungrounded source-independent envelope.
- **FWD 122→OS:** every reflected finite Gram matrix stays PSD after selected RG/blocking and cutoff limit; test crossing R-polymers explicitly.
- **BWD OS→122:** every physical OS local insertion and its RG predecessor must lie in the claimed CMP119/116 analytic family with correct renormalized normalization.
- **Control:** a real symmetric 2×2 kernel with entries (\begin{bmatrix}1&2\\2&1\end{bmatrix}) has all positive entries but a negative quadratic for (v=(1,-1)); pointwise positive/decaying weights alone do not imply reflection positivity.
- **RG:** require actual original nonperturbative `q<1` or CMP116 two-marked physical rate at fixed physical `ell`. Stagewise q<1 and a bare-link high-temperature bound do not suffice.

## Verification/phase status
New three-way bridge source is **AGDA_SOURCE_PENDING** and is wired to `DASHI/Unified/BalabanRGTOERegression.agda` and `.github/workflows/ym-native-maxcut-exact-agda.yml`. No Agda binary/Nix is available in this runtime and no kernel green receipt is claimed. The finite source same-object 1,024-link goals are separate. The physically original Y.01–Y.04 source-witness obligations are nontrivial; the published CMP119/116/122 theorem operators and existing formal adapters should NOT be rewritten as new subprojects.

**Attribution:** Bałaban CMP119 (1988), CMP116 (1988), CMP122 (1989); Kotecký–Preiss; Menotti–Pelissetto; Osterwalder–Schrader; repository donors as listed above. This dossier is a new source-conserving assembly and acceptance cut, not a claim to have proved their original theorems or the Clay endpoint.
