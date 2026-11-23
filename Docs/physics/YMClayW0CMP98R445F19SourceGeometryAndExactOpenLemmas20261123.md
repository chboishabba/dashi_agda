# YM W0 — CMP98 nonlinear average × native R445/F19 coordinates × CMP119/122 source T, precise residuals (23 November 2026)

## Important geometric correction after reopening the originals

Do **not** identify the original F19 straight selected two-bond holonomy with the published Bałaban averaging map by fiat.

Primary source archived in-repo: `Docs/support/reference/balaban-source-extracts/cmp98-averaging-operations.txt`, pp. 18–20 Eq. (9) ordered path holonomy, (10) RG transformation with constraint delta, (11) gauge covariance, (14) linearized block average and **(15) exponential of a block-average of transported-contour logarithms**. The published average Q_B(U) is not by definition the single selected straight two-bond path W(U), even if the two have the same gauge endpoints. CMP119 pp. 254–258 Eq. (2.18) sums outer Omega/Lambda histories, includes S_j sums **inside T_k**, Eq. (2.19) disjoint component factorization, Eq. (2.20)/(2.22) ordered scale-indexed constrained local integrations, with background U_B(V), source R modifications and complete E/R/B action.

The correct commuting geometry is

```
     ORIGINAL physical fine Wilson field U (1024 positive bonds)
            /                               \
 native R445 even/odd pair order         genuine CMP98 average Q_B(U)
        /                                       \
(W_c=U_c0 U_c1, V_c=U_c1, 896 spectators)   test F(Q_B(U))
       \                                        /
        \______ same original Wilson/Haar _____/
                   marked numerator
```

The physical equality to seek is **an equality of integrated pushforward observables**, not the generally incorrect pointwise identity `Q_B(U)=W(U)` or `CMP119 T^(j)(X) = entire F19 T_W`.

[
\boxed{\int_{U} e^{-S_W(U)} F(Q_B(U))\,dH^{1024}(U)
=\int_W dH^{64}(W)\;T_W\big[F(Q_B(WV^{-1},V,S))\big].}
]
Here T_W is the existing fixed-density F19 64-pair/896-spectator conditional Haar functional. The additional equality to the CMP119/122 constrained, gauge-fixed Omega/Lambda/S history sum must be proved **on the same source** and with its own normalizers.

## Critical recovered prior art: full original 64-link native ↔ F19 BIDI was ALREADY source-written

Further import-graph readback from `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda` recovered pre-existing **stronger** source owners that must be cited before interpreting the new local inverse code:

- `YMClayOriginalF19R445Native64HolonomySquareExact.originalNative64IsExplicitParity64`: pointwise all 64 original native link labels agree with the exact parity-selected two-link multiplication, **already source-written**;
- `YMClayOriginalF19R445Native64HolonomySquareExact.originalF19AndNativeR445Actual64CommutingSquare` / `originalF19CoarseWilsonObservableEqualsNativeR445`: existing full native-64-vs-sorted-F19 same-original-canonical-link square, with a documented `originalF19Sorted64AreNativeParity64 = refl` source normalization requiring pinned kernel acceptance;
- `YMClayOriginalR445NativeF19WeightedPhysicalSourceBIDIExact.originalNativeR445NumeratorIsOriginalF19` and `originalNativeR445NormalizedEqualsPhysicalF19Effective`: already source-written same-Wilson-density/same-partition normalized native R445→F19 pushed coarse-observable equality, with the above 64-index certificate/import trust pending;
- `YMClayOriginalF19R445DecoderCommutingSquareExact`: both-way full canonical 1024-link field/128 selected pair/896 spectator bijection;
- `YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact`: four arbitrary **fine** mark coefficients, not only coarse-blocked observables.

**Therefore:** the newly appended W0 native pair inverse in `YMClayR445OriginalNativeParityPairWeldExact` supplements/clarifies the already-made full 64-link geometry, and the Q8 reference certifies its geometry in a finite group. It does NOT count as a new closure of the full native↔F19 source square, normalized weighted source or original 1024-link codec. The new work that was genuinely absent from those donors is **arbitrary transported-nonlinear-average Q(U) as a fine observable through the SAME original F19 physical density**, plus the exact D=Q W^-1 relative holonomy correction, source-dependency and numerical nonidentity control. In particular the preexisting normalized theorem applies to functions F(W) of native coarse holonomies, whereas the CMP98 observable F(Q(U)) can depend on the conditional fibres and 896 spectators: it cannot be replaced by F(W).

The new `YMClayW0OriginalF19CandidateEquation171TExact` is imported through `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda` into `DASHI/Unified/BalabanRGTOERegression.agda` for source-graph regression. These are **imports, not a pinned Agda compiler receipt**. Avoid duplicates and only add the missing Q_B source instantiation, CMP119 domain history and analytic physical source rates.

## Concrete new source-proof terms, not additional abstract records

Reused the **existing** source-native Agda owners:

1. `YMClayR445OriginalNativeParityPairWeldExact.agda` now has
   - `originalR445NativeF19RecoveredPair` (from the actual native W and second original bond V, reconstruct U=WV^-1).
   - `originalR445NativeFirstRecoveredFromF19`, using the already proved `originalR445NativeBlockAgreesExplicitParity` and true SU(N) group associativity/inverse; no independently assumed equality.
   - `originalR445NativeF19RecoveredPairIsOriginal` and `originalR445F19RecoveredPairBlockIsNative`: the original two physical fine bonds and the native W reconstruct bidirectionally at every selected coarse bond.
   - `originalR445RelativeAverageDefect`, `originalR445RelativeAverageDefectTimesNative`, `originalR445RelativeAverageDefectTimesF19Pair`: for an actual source average value Q on the same coarse bond define the group-relative holonomy D=QW^-1, and prove Q=D W including the reconstructed native F19 pair. This is group geometry, **not yet identification with CMP98's concrete Eq.(15) formula**, and does not claim that D is independent of the fine fibre.
2. `YMClayW0OriginalF19CandidateEquation171TExact.agda` already contains the original fixed-W Haar disintegration, F19 first local pair step, one physical Wilson density, all four fine moments. It now adds `sourceAverageObservable`, `originalWilsonAverageMarkedNumeratorEqualsOriginalF19` and `originalWilsonTwoAverageMarksEqualsOriginalF19`: source-written *unconditional under the original one-link Haar algebra* exact transport for an arbitrary fine field map `average : (64 original pairs,896 spectators)→64 averaged links` and two arbitrary coarse tests F,G. Both marks remain inside the same original Wilson weight, **not** independent conditional averages. The actual CMP98 block average is the desired specific inhabitant of this function type after source domain/codec identification.

These are mathematical identities in the original selected source's **provided** Haar structure; no Agda 2.9 pinned kernel receipt, new Borel Haar construction or full physical CMP119 result is claimed. Existing source content is not silently rebranded as new.

## Local finite group and spatial acceptance

`scripts/check_ym_w0_native_r445_f19_q8_geometry_20261123.py`, executed locally:
- Q8 exact noncommutative subgroup of SU(2); 4D periodic side-four lattice 256 sites, **1024 positive fine links**, side-two 16 sites, 64 original coarse bonds.
- Exactly 128 distinct parity-selected consecutive fine links and 896 spectator complement; no double count.
- Original native W=U0U1 and F19 inverse U0=W V^-1 agree for all 64 selected bonds.
- Original gauge action g(x)U(x,y)g(y)^-1 telescopes on the actual oriented two-step path for all 64 native coarse bonds.
- Explicit off-axis alternative path with the same endpoints yields a nontrivial relative D=QW^-1 in **48/64** of a selected example fine configuration. D transforms by conjugation at the **start vertex** for all 64. This alternate path is a **negative-control gauge-covariant contour**, NOT the actual transported-log-average Eq.(15).
- No continuous SU(N) Haar, published Q_B, selected gauge-fixing Jacobian, CMP119 localized T, W3, or mass-gap validation inferred.

## Exact remaining lemma cuts (explicitly proposed names; search prior-art before building)

| Cut | Proposed exact source lemma / object | Actual geometry/measure payment | Status |
|---|---|---|---|
| W0.G0 | `originalR445NativeF19RecoveredPairBlockIsNative`, `originalR445NativeFirstRecoveredFromF19` | Original parity-labelled 64 coarse bonds, 128 unique fine links, source-native SU(N) group map and inverse | **SOURCE_WRITTEN**, Agda kernel pending; Q8 exact reference pass |
| W0.G1 | `originalCMP98Equation15AverageOnNative1024` | Build published transported-contour log/exponential Q_B(U) on the original 1024-link compact group with proper gauges/log chart and source block scale; compare it to W using D, **do not force D=1**. Reuse CMP98 Path13/R147–R193, principal chart, rooted gauge, block average prior art | **OPEN original source identification**, chart and rational special-case owners exist |
| W0.G2 | `originalCMP98SourceAverageF19MarkedPushforward` | Instantiate new arbitrary-average F19 integral equality with actual Q_B(U) from G1; prove native unsorting and original 1/F/G/FG on two unique Wilson fine plaquette sources | **Universal mathematical theorem SOURCE_WRITTEN**, physical Q_B instantiation/Agda kernel pending |
| W0.G3 | `originalCMP119OmegaLambdaSAdmissibleNativeHistory` | Genuine nested Omega_j/Lambda_j/S_j determining sets B, disjoint X components, characteristic factors, S_j summed *inside* T; selected geometry meets source collar/separation and **physical L constraints**, not merely R445 side-4 L=2 toy. Reuse P10/P11, CubeEdgeDomains and Gate4 boundary/collars | **OPEN physical source instance**; generic carriers already exist |
| W0.G4 | `originalCMP122Eq171GaugeConstrainedLocalKernel` | Actual constraint delta for **Q_B** (not W), gauge fixing/Faddeev–Popov/Jacobian, local variable intersection Z_(j+1)∩Omega_(j+1)∩X, R modifications, true continuous SU(N) Haar integrable test class. Reuse Gate4/P3, Eq171 finite/convergent quadrature, source-native geometry | **OPEN physical integral / analytic realization** |
| W0.G5 | `originalCMP119OrderedHistorySumsEqualWilsonAveragePushforward` | Compare fully assembled 2.18–2.23 source T^(j) and residual, including internal S, with G2 test-function Wilson pushforward (never one single T^(j) = global F19 T). Show **four** marked columns and one normalizer, same physical E/R/B/V/beta history | **OPEN physical equality**; generic factorized/density and E/R/B compilers imported |
| W0.G6 | `originalCMP116TwoMarkRootedW3UniformAbsoluteBound` | Source-native roots, J_F/J_G, rooted absolute polymer shell, physical-volume/cutoff-uniform decay and scale-summable UV defects including large fields | **OPEN analytic**, CMP116 and KP/Cauchy arithmetic imported |
| W0.G7 | `originalWilsonSameSourceRPContinuumOSGap` | Original full reflected Gram positivity including crossing R, projective/tight continuum, local noncollapse, same OS Hilbert space H and physical Δ>0 | **OPEN analytic / continuum** |

**Important separation:** Older roadmap `YMClayExecutionPhasesDeliverablesExactLemmas20261106.md` labels F1.0–F1.3 etc OPEN; since then many source-written native parity/permutation and F19 modules landed, but no pinned exact-head Agda/trust graph is available. Those historic 'OPEN' items should not be treated as contradiction or silently marked kernel-closed. This note supersedes their immediate **source-construction** priority, not their acceptance requirements. Main controlling `Docs/roadmaps/ClayYMProofRoadmap.md` remains authoritative.

## Larger Y.01–Y.04, A3/S4 and Clay statuses unchanged

- **Y.01:** Original same-cutoff native Wilson density and selected CMP119/122 E/R/B/gauge-fixed T and running beta action; now native-F19 spatial map/source-pushforward part improved, **full physical source identity OPEN**.
- **Y.02:** Original Wilson two actual legal CMP116 J-rooted marks and differentiated normalized source equality, **OPEN physical class applicability**.
- **Y.03:** Original absolute rooted W3 exponential shell and nonperturbative scale-summable UV estimates, including bad fields and OS-compatible reflection transfer, **OPEN**.
- **Y.04:** Original nontrivial continuum OS theory and same-H strictly positive gap for prescribed compact-simple G, **OPEN**.
- The older A3.0–A3.4, S4.0–S4.4, C5.0–C5.3 are **not** closed by W0 finite work; mathematical kernel and all-group meaning remain required.

Attribution: Wilson/Haar, Bałaban CMP98 (1985) Eq. 10/15, CMP109/116/119/122; prior DASHI native parity and F19 Haar, CMP98 Path13/selected principal charts, P10/P11/CubeEdgeDomains, Gate4/P3, CMP119/CMP122 and CMP116 OS producers. No new universal Clay theorem.
