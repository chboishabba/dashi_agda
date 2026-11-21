# RH/GRH source max-cut — indexed zero/ζ/ζ², Filsinger polarity and original Galois–star theta

**21 November 2026.** Golden [Agda PR #1533](https://github.com/chboishabba/dashi_agda/pull/1533), upstream selective [Lean PR #113](https://github.com/chboishabba/dashi_lean4/pull/113). Pinned Alpöge proof fork `chboishabba/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`. No CI; new Agda theorem source has **no kernel receipt**.

## Correct source-owner recovery: three-mode square with zero and time/k history

The prior RH P1 roadmap overemphasized a plain 27-cell chart and C3 involution. **Original mathematical carrier has additional distinctions that MUST survive.**

- `DASHI/Moonshine/Monster3BZeroZetaSquaredC3SeparationExact.agda`: the **actual source owner** already implements a tagged `ZeroOrRootOfUnity`. Its `scalarZero` is distinct from `nonzeroPhase phase0` (the exponent-zero C3 phase has value **one**), `nonzeroPhase phase1` (ζ₃), and `nonzeroPhase phase2` (ζ₃²). Balanced regular C3 representation evaluates to zero but is not an empty representation or zero phase. Zero-evaluation quotient loses hidden phase.
- `DASHI/Moonshine/C3FourierConjugationExact.agda`: ζ₃² = ζ₃⁻¹ = conjugate ζ₃, genuine ordered Fourier `chi1` and `chi2`; conjugation is an involution, not a zero-annihilation law.
- `DASHI/Moonshine/Monster369ZetaSameObjectWeldExact.agda`: these **cyclotomic** scalars are genuinely identified among selected Monster/Heisenberg/VOA symbolic phases; actual carrier/action recognition remains gated. **Cyclotomic ζ₃ is not the complex Riemann zeta function ζ(s)**; similarly ζ₃² is not ζ(s)².
- `DASHI/Interop/PNFHyperfabric369.agda` explicitly has `documentTimeAxis` and `documentTimeHypervoxel`. `DASHI/Reasoning/TypedHyperfabricActionCrossingTransportExact.agda` already owns `transportTrace`, ordered crossing events and `transportTraceAppend`, with no reverse/braid promotion.
- Smith/Filsinger actual donor `DASHI/Physics/Motors/SmithFilsingerFinitePhaseMatchingExact.agda` and `scripts/check_smith_filsinger_phase_maxcut_exact.py`: phase polarity, source/sink time slots, sign reversals and independent balance ledgers matter. Equal phase averages and source ratios do **not** prove identical work or measured Maxwell/Earth source. The mathematical lesson applicable to RH P1 is to retain per-k sign and residual through transport rather than infer zero work from a balanced phase sum.
- True RH analytic geometric symmetry owner `DASHI/Mathematics/NumberTheory/RiemannXiSymmetryExact.agda` models `s↦1-s`, conjugation and critical reflection as different maps, with fixed-locus calculations on rational coordinates. Those are **not** identities between ζ(s) and cyclotomic ζ₃.

### New implemented finite carrier

`DASHI/Analysis/RHGRHIndexedZeroZetaPhaseResidualWeldExact.agda` **reuses the canonical tagged source** for `Mode` and source C3 conjugation rather than inventing a new phase table. Its `IndexedZeroPhaseFrame Index Sign Residual` stores:
`index, mode, sign, residual, observedZero`.
- `reflectModeInvolutive` and `reflectFrameInvolutive` source-write the exact two-reflection BIDI.
- `balancedObservedZeroWithZeta` and the conjugate example preserve their different nonzero underlying modes **despite** both reporting zero observation, while the sign and residual retain their exact original values. These are finite negative controls, not RH zero witnesses.
- `IndexedCommutingConsumer` **requires** an actual reflection-invariant downstream consumer; `consumerReflectsAt` uses that premise. The underlying two-reflection identity holds independently by involution. No Dirichlet/automorphic consumer has been constructed.
- `scripts/check_rh_indexed_zero_zeta_filsinger_20261121.py` is a stdlib exact finite regression, source-committed **not yet independently executed**. Its test models zero vs unity vs ζ vs ζ² and sign/residual under reflection.

Do not collapse `index`, source causal order, phase, sign, residual, and observed zero into an untyped scalar "zero mode". The relevant square is **indexed, proof-relevant and information-preserving**, with actual cancellation only at declared evaluation consumers.

## Deep external theorem type: no false finite-group identification

The fork's true source `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/HalfIndexLattices/TLiftK.lean` defines `UpperTheory.TP.TLiftK : Prop` by quantifying over **all** relevant CM number fields (E), base Hermitian data (B), Hermitian (X), skew-Hermitian (W) of growing dimension, Hecke characters and character restrictions, infinity-place exponents, automorphic representations and **the existence of an actual lifted submodule (U') with `IsLift`**.

Exact source edges:
- `UpperTheory.TP.K.tLiftK : UpperTheory.TP.TLiftK := UpperTheory.TP.tLift_holds_k`, source `ThetaKernels/TLiftK.lean`;
- `UpperTheory.Gal.Int.Geo.geoOne_holds : GeoOne` is built from `geometric_realization_of_weight_one weight_one_geometric_realization` (Lefschetz formula), source `GeometricFlagBases/WeightOneGeometricRealization.lean`;
- `UpperTheory.Gal.Int.galoisRepresentations_of_thetaLift (up : UpperTheory.TP.TLiftK) : UpperTheory.GalStar.Row0b recT := galoisLocalGlobalStrong_of_geometry_lift geoOne_holds up`, source `GaloisRepresentationsOfThetaLift.lean`;
- `UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter : Row0b recT := galoisRepresentations_of_thetaLift tLiftK`, source `RowSrc.lean`.

**Therefore:** a 27-mode C3 sheet, Monster 3B phase, G2 3×3 determinant or Filsinger two-slot signed ledger is NOT automatically an inhabitant of `TP.TLiftK` or `Row0b recT`. The valid steelman is to use their exact phase/sign/spectral-observer certificates **inside** the original automorphic construction where the original typed structures genuinely admit those finite fibres.

## BIDI / reverse-solve actual mathematical obligations

| Gate | Exact required theorem | Existing donor | Status |
|---|---|---|---|
| P0 original terminal | imported `RiemannHypothesis` → the actual root `Millennium.ClayRiemannHypothesis` | original 5 fork theorem producers; existing root exact BIDI | OPEN compatible kernel |
| P1-F01 indexed three-mode fidelity | zero vs neutral phase, ζ/ζ² conjugation, k/sign/residual retained | original 3B separation, C3 Fourier, hyperfabric, new indexed source | SOURCE WRITTEN; Agda check OPEN |
| P1-F02 true commuting square | original indexed source evaluation (C_k) commutes with reflection and chosen transition (T_{k→k'}) **with residual** (R_{k,k'}) | original `TypedHyperfabricActionCrossingTransportExact`, `ActionCrossingTraceCalculusExact` | OPEN actual evaluation/transition; pure reflection involution not sufficient |
| P1-F03 physical/phase nonpromotion | zero Fourier amplitude/phase parity does not force zero work or global energy balance | Smith/Filsinger polarity/cross-ratio/time ledger | finite negative control only; no Maxwell source identity |
| P1-F04 original theta indexed fibre | actual map from original (E,B,X,W,χ,U) to the **same** indexed C3 zero/sign/residual ledger with genuine source action | fork `TP.TLiftK`, `TPGHolds`, DASHI C3/369/Monster owners | OPEN selected object and field/weight/mode intertwiners |
| P1-F05 source Galois star | source-correct preservation from original `TP.TLiftK` to `GalStar.Row0b recT` with actual `GeoOne` | original `galoisRepresentations_of_thetaLift`/Lefschetz producer | ORIGINAL FORK HAS THIS; DASHI improvement OPEN |
| P1-F06 analytic zeta | prove source-specific map from Riemann ζ(s), completed ζ and actual spectral zeros to proposed indexed observer; critical line, zero multiplicity and nontrivial zeros preserved | `RiemannAnalyticSubstrate`, `RiemannXiSymmetryExact`, original Mathlib RH | OPEN; **cyclotomic ζ₃ not ζ(s)** |
| P1-F07 strict G2/OffGamma | original test (q), selected (t,J), signed cosine sum and universal pole-quotient Off/Gamma allowances | G2 scalar and current final analytic-core owners | OPEN; do not infer from C3 cancellation |

### Immediate next cut

First **kernel check the small indexed Agda source**. Then choose *one* source-backed finite character/Hecke/theta carrier already used by `TLiftK` and test whether its finite fibre carries our full `[scalarZero, ζ₃, ζ₃²]` mode, time/k, sign and residual, or prove that the interpretation fails. Do **not** start by claiming a generic (C_3→mathrm{TP.TLiftK}) theorem: the latter is a deeply quantified automorphic assertion. Keep the original imported RH terminal entirely separate from P1 mechanism research.

This is the source-faithful way to exploit recent Filsinger polarity and time-indexed hyperfabric infrastructure without inventing Galois, theta or RH proofs. No world/PG work.
