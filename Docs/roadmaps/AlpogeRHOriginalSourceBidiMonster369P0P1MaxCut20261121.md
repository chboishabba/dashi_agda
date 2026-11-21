# RH P0 original-source BIDI / reverse-solve integration and Monster–369 donor audit

**Date:** 21 November 2026. Agda golden integration PR [#1533](https://github.com/chboishabba/dashi_agda/pull/1533). Lean source-admission PR [#113](https://github.com/chboishabba/dashi_lean4/pull/113). This is the *consolidation plan and verified source inventory* for existing owners, not a new claimed RH proof.

## 1. Exact original external producer (P0.00)

Levent Alpöge announced the original RH and Dirichlet GRH formalization on 2026-11-20: https://alpo.ge/remark.pdf . Its public byte-exact mirror: https://github.com/Deicyde/riemann-hypothesis . Independent audit: https://math.mit.edu/~drew/grh/ (20 Nov 22:05 UTC).

**Source inspected directly:** `src/Main.lean` in Deicyde mirror blob `dbd5db70bc11b35f18fa5751216ab335321e7bfc`; five actual declarations are `riemannHypothesis`, `riemannZeta_eq_zero_re`, `LFunction_ne_zero_of_half_lt_re`, `LFunction_eq_zero_re`, `LFunction_eq_zero_re_of_isPrimitive`. The independently specified `src/Challenge.lean` blob `9677ace64b3a5e8b1a571d82d52ee13c53b08026` contains the same five *goals with sorry*, not a proof. Its `Main` theorem imports `Statements` and `Supplements.Kernels.MainTheoremsAll` and obtains RH from `rhOfAll`; Dirichlet from `allChi`, `claimAll.2.1`, `critAll`. Those are verified theorem-name connections; **not** a reconstructed mathematical proof dependency DAG.

Archive 239275554 bytes sha256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Lean and Mathlib v4.33.1. Challenge exported sha256 `bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9`. External independent check states 175187 source modules compile; independent kernels nanoda / con-leche accept and statement comparison passes. **All these are external receipts, not DASHI-local executions**.

**Redistribution licence:** The external mirror README states the original source is unlicensed. **No copy/vendor archive committed**: public-source availability is not a grant to republish the 1.03GB proof. The isolated Lean [#113] includes original DASHI adapter code and pinned hashes; local materialization needs appropriately permitted access. This is a **legal/provenance P0 admission blocker**, not an analytic mathematical obstruction.

## 2. Already-paid exact Clay and Mathlib theorem identity (P0.01)

Inspected *actual* `dashi_lean4/MillenniumExternal/ExactTargetSurface.lean` on original master:

```
clayRiemannHypothesis_of_mathlib : RiemannHypothesis → Millennium.ClayRiemannHypothesis
mathlibRiemannHypothesis_of_clay : Millennium.ClayRiemannHypothesis → RiemannHypothesis
clayRiemannHypothesis_iff_mathlib : Millennium.ClayRiemannHypothesis ↔ RiemannHypothesis
```

These are proof terms consuming the existing pinned LeanDojo `Millennium.ClayRiemannHypothesis` target, not a new theorem target. New Lean #113 `MillenniumExternal/AlpogeRHBoundaryExact.lean` simply consumes that BIDI; version-isolated `proofs/alpoge-lean433/RHAdmission.lean` imports the real `Main` and names all five outputs. **Neither new file has been elaborated/compiled in this session**.

**Reverse-solve:**
1. Read terminal `Millennium.ClayRiemannHypothesis` and use its **existing** equivalence to root Mathlib RH, not a synthetic RH representation.
2. Find external original `Main.riemannHypothesis` which already has type Mathlib RH in v4.33.1.
3. Solve *version/definition coherent proof admission*, not mathematics: current DASHI root and external Lean/Mathlib have different pins; do not mix oleans. Either create compatible local root build with the exact Clay theorem version or prove genuine cross-version statement translation.
4. Compile the actual theorem `clayRiemannHypothesis_of_mathlib original_mathlib_rh` in one trusted kernel, then inspect axioms.
5. Reverse-check `mathlibRiemannHypothesis_of_clay` on the exact same theorem, and preserve the independent original Dirichlet GRH scope.

**This is the P0 acceleration:** once same-kernel admitted, RH original Clay Lean endpoint requires no new strict-moment/Weil positivity argument. The original A1/A2/G3 signed analytic producers remain mathematically interesting for **independent mechanistic geometric proofs** but should not gate importing an already validated theorem.

## 3. Agda golden original endpoint: what BIDI pays and what it does not (P0.02)

Existing `DASHI/Analysis/RiemannAnalyticSubstrate.agda` defines `RiemannHypothesisFor analytic` on the original source carrier; `AlpogeGRHGeometricTransportExact.agda` has `externalRHImpliesDashiRH` requiring an `ExternalRHGeometricTransport` with genuine zero preservation and critical-line reflection. **This record is currently uninhabited**. The current Agda file is a typed conditional transport; it is not an import of the 175187-module Lean proof.

Exact remaining mathematical/computational leaves:
- `alpogeExternalMathlibRHSameTheoremInRootKernel`: source archive, permission and version-locked Lean proof object, *not* a statement string;
- `agdaRiemannCompletedZetaEqualsMathlibRiemannZeta`: literal function identification including completion gamma factors/trivial zeros/pole 1;
- `agdaActualComplexZeroPredicateIffImportedMathlib` and `agdaActualCriticalLinePredicateIffImportedMathlib`: actual complex field and normalisation transport;
- `agdaRHFromTrustedSourceProof`: complete original Agda endpoint in a compatible trusted proof-transport mechanism; a text reference to a Lean proof or an assumed record **does not prove this in Agda**;
- `agdaDirichletGRHToArithmeticConsequences`: actual Dirichlet character carrier and source exact S01–S22 theorem assumptions, separately from ordinary RH.

No local Lean/Agda checker or CI invoked; source-written Agda remains acceptance OPEN.

## 4. Steelman / BIDI / reverse-solve, applied to the *actual mechanism*

Original author explicitly highlights **Stepanov-type multiplicity, Fourier-analytic tricks, chains of theta lifts of length roughly √X, higher-rank O(2,n) determinant/automorphic signs and qN = Mk+R**, together with Guinand–Weil/prime sums. Those descriptions are in his original four-page manuscript; they are **not automatically identified with any DASHI module**.

**Steelman:** preserve all those physical/mathematical dimensions at once instead of reducing his work to mere Weil positivity or dismissing finite symmetry:
- **Source identity axis:** actual `riemannZeta` / Dirichlet L and selected original Fourier/Guinand–Weil test space;
- **Finite symmetry axis:** genuine ternary C3^3 and spatial native 27, S3 six-order path comparison, source-normalized character and involution;
- **Automorphic/theta axis:** source regularized theta integral, quadratic signature, determinant/multiplicity chain, actual Weil explicit formula;
- **Consumer axis:** keep determinant vs full three-channel information and index residual holonomy, `FactorsThrough` only for a declared observer/consumer pair.

**Bidirectional solve**: (external theorem → our terminal theorem) is P0; (our typed geometry → exact source analytic observable) is P1 and requires source-faithful evaluation, not model shape. Test whether each diagrammatic face commutes on the literal source carriers and explicitly retain nonzero residual counterexamples.

**Reverse solve**: start with the exact closed theorem's real proof dependencies and trace backward for any genuinely reusable lemma; do not invent an O(2,n)/theta/cubic identity based on suggestive notation. If an existing producer pays an endpoint, delete duplicate proof attempts; if one source-to-source weld remains, name only that leaf. Conversely, an interface with uninhabited analytic fields is not closed by tracing its name.

## 5. Newly inspected Monster/symmetry/369 donors and exact eligibility

| Original owner and PR | Actual known producer | Distinctive reuse opportunity | Exact non-promotion / next weld |
|---|---|---|---|
| Agda [#1472](https://github.com/chboishabba/dashi_agda/pull/1472) head `36db4df1`, Y443 / Vnatural | finite 80-relator Coxeter word scaffold and *conditional* word transport into actual `Vnatural` action | character-labelled symmetry/VOA proof provenance, potential representation-type bookkeeping for theta chains | **not** source O(2,n) determinant/automorphic L-functions or Xi; actual 3B representation/Vnatural action still gated |
| Agda [#1510](https://github.com/chboishabba/dashi_agda/pull/1510) head `70c60efc`, C3/S3 | actual selected 196830 pointed-sheet finite actions and 65610 orbit/phase blocks | six-coordinate-order, Reynolds/invariant and lossless C3/S3 consumer transport | finite action does not establish analytic zeta zeros or theta automorphy |
| Agda [#1527](https://github.com/chboishabba/dashi_agda/pull/1527) head `fc5198a3`, weighted C3/S3 Reynolds | exact finite weighted mode-ledger and explicit **noncommuting** radial operator witness | exact equivariance/defect test template for cube face residuals, weighted quadratic form comparison | source physical modes are not analytic Dirichlet characters; don't assume every operator commutes |
| Agda [#1489](https://github.com/chboishabba/dashi_agda/pull/1489) head `bf2eef07`, same-H heat/zeta | rational finite C3-equivariant H, projectors, heat/zeta trace, twisted trace | reusable finite spectral Gram / operator intertwiner proof pattern | no Xi-zero spectral completeness or Hilbert–Pólya identification |
| Agda original `RiemannG2DeterminantConsumerQuotient369Exact` | **true** fixed-kernel scalar sufficiency: q(u)=det3(n1,n2,h(u)); full 3-channel state factors through q only for the fixed kernel consumer | **highest-alpha 369/RH donor** for source author's determinant and signed-test-functional rhetoric: use `ConsumerSufficient` and actual 3-row determinant producer | q is NOT source author's O(2,n) determinant; the open actual target-centered G2 scalar remains unresolved unless a same-form link is produced |
| Agda `RiemannG2HighestAlphaAfter369Exact` | original G2 steelman says no exact target-centred scalar donor yet; literal direct finite producer prioritized over name-level donor hunt | preserve failed weld, don't restart candidate search based on C3 naming | without source identification *not* a replacement for original external proof |
| Agda `C3RiemannConjugationBridgeExact` | exact symbolic fixed-locus comparison; functional reflection s↦1−s equals conjugation only on line Re(s)=1/2 | reuse actual involution equations and reverse-critical-line predicate normalization in Agda P0.02 | finite C3 conjugation fixed point and RH critical-line cannot be identified without actual zero carrier |
| Agda `C3CubeFourier27Exact`, `TernaryPermutationS3LawsExact`, #1291 indexed residual | true 27-cell/27-character C3^3 combinatorics, six permutations and six-face endpoint witnesses | P1 stronger cube built from existing zeta squares: 3-way Fourier/geometry/consumer transport, not new abstract cube | cube carriers require actual source operations and residual bound; spatial nearest-neighbour ≠ residue cyclic successor |
| Agda `Monster369ZetaSameObjectWeldExact` | exact **cyclotomic** C3 zeta scalar aligns among selected Monster phases and finite Schrödinger model | efficient same-phase transport for a *character*-indexed test/FFT consumer | the scalar ζ₃ is not the Riemann zeta function; H_ζ/W_ζ same-representation action still open |
| Agda `Griess1990RationalAlbertTrialityTransportExact` | typed 27D rational Jordan product/trace/actor intertwiner; source certificates vs actual Agda inhabitant separate | consumer-specific bilinear-form/isometry design and exact counterexample tests | Griess/Albert cubic is not original O(2,n) automorphic determinant; action matching still required |
| Agda `PenumbralSingularThetaIntegral` / `SingularThetaBorcherdsBridge` | typed regularized theta kernel, singular-divisor and Borcherds log-norm identities | **strong thematic theta source donor**: compare actual source theta lift definitions/weight/dimension and regularization against external proof's operator | even real theta lift may be an entirely different kind (Borcherds/Penumbral vs orthogonal higher-rank chain). Demand source theorem/measure/line bundle equivalence; no automatic weld |
| Agda [#1529](https://github.com/chboishabba/dashi_agda/pull/1529) head `7b35790d`, Bishop π/CM | true original modular j, E4/E6 partial actual-analytic bridge, dyadic CM certificate | useful **auxiliary** modular/CM source-function and estimate donors if external theta proof uses precisely those | the same CM vocabulary is insufficient; original completed ζ/Weil functions and analytic convergence still need identification |

### P1 exact remaining donor-weld matrix (ordered)

1. `alpogeActualStephanovFourierThetaDependencyMap`: inspect original theorem chain and extract the **genuine** `O(2,n)` / theta-lift / determinant / Guinand–Weil math objects (OPEN, requires the 1.03GB source; copyright/permission boundary).
2. `originalRiemannG2DeterminantEqualsSourceThetaDeterminant`: **candidate**, not presumed true. If false, commit explicit typed no-go and keep G2 route independent.
3. `originalPenumbralThetaEqualsSourceOrthogonalThetaLift`: **candidate**, source dimension/weight/kernel/regularization equality required.
4. `actualC3RiemannReflectionToNativeCompletedZetaZeros`: consume original exact C3 reflection and analytic completed ζ, do not deduce zeros from fixed phase counts.
5. `original369C3DeterminantConsumerFactorThrough`: compute actual determinant observable from true three-channel source; if enough for selected test, use canonical `ConsumerDescentMinimalObserverExact`; otherwise retain residual.
6. `originalS3SixFaceWeilTestCube`: source-backed six-face diagram built from existing C3/zeta squares and native 27 geometry, with actual scalar equality or controlled face residuals, not equality of labels.
7. `originalThetaWeilQuadraticTracePositiveBidi`: compare actual original test space and positive forms, not abstract Gram signatures; import external RH as terminal proof independently of this mechanism.
8. `monsterVOAAndXiSameFunctionNegativeControl`: retain cyclotomic/Monster/Dirichlet/Riemann zeta distinction and log non-promotion countermodels.

**Priority:** P0.00–P0.03 before P1 theta/G2; do not reopen the live RH A1/A2/G3 analytic wall when the aim is source adoption. Once an external source proof is admitted into one compatible kernel, the terminal Mathlib-to-Clay endpoint is already paid. Agda still needs genuinely trusted theorem transport and original complex/analytic same-object identification.

## 6. Exact acceptance receipts and constraints

- New Lean [#113] committed source-only adapters and license-safe pinning; **Lean compiler not invoked**.
- Agda [#1533] prior `AlpogeGRHGeometricTransportExact` source-written, abstract input still uninhabited; **Agda compiler not invoked**.
- The source snippets above are derived from direct file readbacks, not inferred only from PR titles. PR heads are the latest connector-reported values **at this audit time**, not immutable future heads.
- The original fourth user screenshot is social commentary, not an independent source for any theorem; the original 4-page announcement is provenance, not the underlying Lean proof itself.
- **No CI, no Lean, no Agda**, local finite SymPy only if actually run and specifically reported.

## 21 November second original theorem-body inspection — paid RH termination spine

Beyond just `Main`, direct-read original files (not guessed from metadata):

- `src/Supplements/Kernels/MainTheorems.lean`: `allChi : UpperTheory.EveryCharacter := UpperTheory.FinalTheorems.everyCharacter`; `rhOfAll : RiemannHypothesis := Formalism.VW.rh_of_every allChi`; `critAll` and `claimAll` are the other Dirichlet consumer hooks.
- `src/Formalism/GammaFactorNonvanishing/CritLine.lean`: `rh_of_every` specializes `UpperTheory.EveryCharacter` to the trivial character mod 1, using the *actual* `LFunction_modOne_eq`; `critLine` uses primitive-character functional equation, gamma-factor nonvanishing and contradiction away from the critical line. **This is an explicit source-proved mathematical RH ↔ Dirichlet bridge**, not a DASHI speculative analogue.
- `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`: `UpperTheory.FinalTheorems.everyCharacter` is obtained from `everyCharacter_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter` (the actual immediately-used source theorem).
- `src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean`: `UpperTheory.EveryCharacter` is the same precise nonvanishing statement for all characters; `plugAll` invokes original imprimitive-character extension.
- `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`: very large and high-level source with explicit theta, automorphic, Galois, published-theorem and archimedean dependencies; reading its import list **does not** establish that any particular DASHI `PenumbralSingularThetaIntegral` map equals the source.

**Exact reverse-solve dependency chain now grounded by original code:**

```text
Main.riemannHypothesis
  ← Supplements.Kernels.MainTheorems.rhOfAll
  ← Formalism.VW.rh_of_every (allChi)
  ← UpperTheory.FinalTheorems.everyCharacter
  ← UpperTheory.FinalTheorems.everyCharacter_of_row
  ← UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
     + UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin
     + UpperTheory.One.vwin_of_row
```

This directly localizes the *mathematical source admission* at `EveryCharacter`, and the *exact Clay handoff* at root `RiemannHypothesis`. No need to synthesize an RH-equivalent G3 proof to use the source theorem. The imported package's full, transitive proofs remain enormous and subject to license + local trusted-kernel verification. Future geometric work can compare the real higher-rank source machinery at those earlier owners, not simply the surname `theta`.
