# Unified Routes And Lanes Plan

Declared surface level: `architecture` and `roadmap`.

Purpose: state the current canonical NS/YM/unification walls and the validation
discipline that keeps those walls honest.

## Governance States

- `Proved = true`: proved locally in DASHI.
- `AuthorityAudited = true`: external dependencies are explicitly named and
  packaged, but not reproved locally.
- `SubmissionReady = true`: the manuscript/reviewer surface is operational
  without pretending local proof.

Fail-closed discipline is unchanged: `Proved = false` blocks theorem
promotion even if the surface is authority-audited or submission-ready.

## Canonical Walls

### NS

The live NS wall is the coupled `A1/A3` bootstrap plus the quantitative `A4`
Lei-Ren-Tian-to-Fourier transfer.

Route:

```text
A1.1/A1.2/A1.3 bounded Abel mass / weak-* compactness / shell-tail control
  + A3.1/A3.2/A3.3/A3.4 quantitative stationarity bootstrap
  + A4 uniform output-support transfer
  -> A5/A6 bias-to-leakage consumers
  -> A7/A8/A9 depletion/closure ladder
  -> standard PDE writeup / reviewer packet
```

Operational consequences:

- `A5-A9` are downstream consumers, not the primary frontier.
- Theta/danger-shell material is diagnostic only.
- The repo may record exact candidate theorem packages for `A1/A3` and `A4`
  without promoting them. Candidate grammar and promotion state are separate.
- The repo may also record an exact candidate downstream `A5-A9` package so
  the depletion / contradiction ladder is reviewer-readable once the upstream
  fronts are accepted. This does not weaken the fail-closed distinction
  between "recorded route" and "proved theorem".
- NS manuscript readiness surfaces may be audited or submission-ready while NS
  Clay promotion remains false.
- The repo may also package the classical `CKN + ESS + LRT` intake as an
  explicit self-contained theorem packet feeding `A1/A3`, `A4`, and then
  `A5-A9`, while still keeping promotion fail-closed until those packets are
  accepted in the exact normed form consumed downstream.

Primary surfaces:

- `NSAbelTriadicDefectMeasureConstructionBoundary`
- `NSAbelTriadicStationarityConstructionBoundary`
- `NSBoundedAbelMassEstimateBoundary`
- `NSQuantitativeStationarityRateBoundary`
- `NSLeiRenTianOutputSupportTransferBoundary`
- `NSLeiRenTianFourierOutputCouplingBoundary`
- `NSWriteupAndConstantsReadinessBoundary`
- `NSStandardPDEWriteupAssemblyBoundary`
- `NSPaperSubmissionPacketBoundary`

### YM

The live YM wall is no longer "generic continuum construction". It is the
cited Balaban/OS authority intake centered on `H3a`, with `H3b` and
no-spectral-pollution downstream.

Route:

```text
finite self-adjointness / spectral margin
  -> H3a continuum transfer
  -> H3b vacuum-projector transport
  -> no-spectral-pollution
  -> RP / OS-Wightman authority
  -> continuum mass-gap assembly
  -> writeup / reviewer packet / external acceptance
```

Operational consequences:

- Mosco/liminf compactness is necessary but insufficient.
- `H3a` is the load-bearing transfer theorem.
- `H3b` and no-spectral-pollution are downstream consequences, not peer walls.
- Explicit theorem-shape packaging for `H3a/H3b` does not change the current
  authority-backed governance state.
- RP/OS/Wightman remain explicit authority-side blockers.
- The real remaining external burden is now typed more sharply than
  "everything after finite margins": Balaban block-spin effective action,
  infinite-volume survival of the finite margin, and RG-compatible reflection
  positivity are the load-bearing external items.

Primary surfaces:

- `YMSprint109NoBottomSpectrumPollutionCompactness`
- `YMSprint109MoscoSpectralLiminfAssembly`
- `YMSprint119MoscoAllObligationsReducer`
- `YMSprint119TransferCalculusAllObligationsReducer`
- `YMBruhatTitsToOSLatticeTransferBoundary`
- `YMContinuumTransferToNoSpectralPollutionSocketCompositeLightweightBoundary`
- `YMNoSpectralPollutionToOSWightmanSocketCompositeLightweightBoundary`
- `YMReflectionPositivityFullTheoremAssemblyBoundary`
- `YMContinuumMassGapFinalAssemblyBoundary`
- `YMOnlyRemainingAuthorityBlockersBoundary`
- `YMStandardLanguageWriteupReadinessBoundary`
- `YMPaperSubmissionPacketBoundary`

### Unification

The live unification wall is the corrected `U-1a-H` route, not a generic
"full unification" blocker list.

Route:

```text
per-lane U-1a-H justification
  -> scale-invariant cross-term decomposition
  -> residual PDE specification
  -> ellipticity / Carleman intake
  -> cross-term nullity / modulo-null linearity
  -> four-point cancellation
  -> parallelogram
  -> Jordan-von Neumann
  -> signature / Clifford consumers
  -> authority packet
```

Operational consequences:

- Two-homogeneity alone is not enough.
- The missing theorem burden now has a precise front:
  residual PDE specification, ellipticity class, Carleman intake, and then the
  cross-term nullity theorem itself.
- The repo may also record the exact downstream `UCT.5-UCT.8` consumer chain:
  modulo-null linearity -> four-point cancellation -> parallelogram ->
  Jordan-von Neumann, provided those remain explicitly downstream of `UCT.4`.
- Authority packet surfaces do not replace the missing four-point /
  parallelogram theorem chain.
- Exact UCT.1-UCT.4 theorem grammar may be recorded locally while cross-term
  nullity remains fail-closed until the PDE/Carleman intake is actually
  accepted.
- The repo may also package the downstream `UCT.5-UCT.8` chain as a
  self-contained consumer ladder once `UCT.4` is granted, without widening any
  terminal claim.
- The main remaining unification burden is now promotion evidence on the
  candidate `UCT.1-UCT.8` package, not missing downstream theorem-shape
  grammar. The live theorem wall is still `UCT.1-UCT.4`; the later clauses are
  already structured as consumers pending that wall.

Primary surfaces:

- `UnificationScaleInvariantCrossTermHypothesisBoundary`
- `UnificationU1aHJustificationNSLaneBoundary`
- `UnificationU1aHJustificationYMLaneBoundary`
- `UnificationU1aHJustificationGlobalBoundary`
- `UnificationU1aHPerLaneCompositeBoundary`
- `UnificationCrossTermNullityDiscriminantBoundary`
- `UnificationNullClassSubspaceCompleteBoundary`
- `UnificationParallelogramFromBilinearBoundary`
- `UnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary`
- `UnificationSignatureCliffordConsumerSocketBoundary`
- `UnificationLaneJustificationAuthorityBoundary`
- `UnificationConsumerAuthorityAssemblyBoundary`
- `UnificationAuthorityReviewPacketBoundary`

## Validation Discipline

Routine validation for these walls uses two tiers only:

1. Targeted heavy-frontier smoke checks with a hard cap:

```bash
timeout 15s agda -i . <module>.agda
```

2. Aggregate integration check:

```bash
agda -i . DASHI/Everything.agda
```

Rules:

- Exit `124` on a targeted run is a budget signal, not a type error.
- Targeted success keeps all fail-closed theorem and authority flags unchanged.
- The aggregate check is green only when `DASHI/Everything.agda` passes.
- The aggregate check is a coherence check across lanes, not a promotion event.

## Ownership Boundary

This lane owns validation manifests and compile-policy documentation only. It
does not reinterpret theorem status, clear authority blockers, or widen any
claim surface beyond the current fail-closed NS/YM/unification walls.
