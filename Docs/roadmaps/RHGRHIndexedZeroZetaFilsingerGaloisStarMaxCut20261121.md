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


## 21 November — F02 k→k' indexed commuting square implemented (CURRENT)

**New source:** `DASHI/Analysis/RHGRHIndexedZeroZetaTransitionSquareExact.agda`, building **directly on the already-existing** `RHGRHIndexedZeroZetaPhaseResidualWeldExact.IndexedZeroPhaseFrame`, rather than another separate phase, zero or fabric ontology. Its `SourceIndexedPhaseStep next step` is an explicitly *conditioned* transport contract: advancing index, preserving sign, residual, observed-zero and the original scalar-zero mode, plus **actual one-step commutation** `step (reflectFrame f) ≡ reflectFrame (step f)`. Reversibility is not assumed for arbitrary steps. `advanceOne` supplies a concrete same-mode, same-sign, same-residual (kmapsto k+1) fixture, while `composeIndexedSteps` proves two such source-qualified transitions compose and retain all the separate laws. This is stronger than the previous involution-only `R²=1` diagnostic, but not a full domain-specific theta action.

**Local finite acceptance:** `scripts/check_rh_k_indexed_square_20261121.py` was executed via local Python: **480/480** product configurations over 10 indices, four tagged modes (scalar zero, unity, ζ₃, ζ₃²), two signs, three integer residuals and two observation flags; one-step and two-step commuting squares, index advance, retained sign/residual/zero and involution all PASS. Explicit lossy-mode/residual update is rejected, and canonical exact (1+ζ₃+ζ₃²=0) finite cyclotomic coordinates checked. These are finite equality checks, **not an Agda typechecking receipt**. Agda binary is not installed in this runtime, so neither this file nor prior indexed files has been kernel checked here; no CI.

### P1-F02 precise split

- **PAID as source-written finite model:** a nontrivial (kmapsto k+1) reflection-commuting frame transition, and conditional composability for any source-indexed steps admitting the stated fieldwise and reflection laws. Keeping observed zero and the source zero-mode **separate** is intentional.
- **OPEN original/source-specific transport:** an actual `k→k'` transition sourced from the original `TP.TLiftK` Hecke/theta carrier, with a chosen signed observable and retained remainder; actual identification of `Index`, `Sign`, `Residual`, and `observedZero` with mathematical fields of that object. The existing Filsinger retarded flight / boundary work ledger is only a *donor design* for preserving separate causal/source terms; no physical or analytic same-object weld exists.
- **OPEN full spectral/analytic square:** a proof that source-selected `consume (step (reflect f)) = consume (reflect (step f))` with the SAME source `consume` and `Residual`, and equality or accounted discrepancy relative to the actual Galois/Hecke/Weil operator. Merely postulating `SourceIndexedPhaseStep` does not instantiate it for an upstream automorphic field.

**Next maximum cut:** inspect **one selected actual** original `TP.TLiftK` source subcondition involving an `IsHecke` or `IsLift` witness and test whether our source-zero/phase/sign/residual chart is a *valid fibre* of that target, not an abstract replacement. The original `TP.TLiftK` quantifies over all CM fields, Hermitian data and automorphic representations, so no finite 4-mode theorem by itself proves that theorem. Use the existing native Galois/star and typed hyperfabric owners to build the smallest same-object weld, or record a concrete counterexample. P0 RH/GRH import remains independent, no world/PG and no CI.


## 21 November — P1-F02B nonzero indexed residual-flux acceptance and ORIGINAL theta fibre (latest)

The earlier `SourceIndexedPhaseStep` assumed a **constant residual**. That is an exact fixture for some transitions, but it is too restrictive for a Filsinger-style source/sink ledger and for future nontrivial Hecke/theta remainders. Do not erase residual increments to force a commuting square.

### New finite source / actual local receipt

- `DASHI/Analysis/RHGRHIndexedZeroZetaResidualFluxExact.agda` **reuses** `RHGRHIndexedZeroZetaPhaseResidualWeldExact.IndexedZeroPhaseFrame`. For a source-provided natural-number increment δ, it defines `appendResidualFlux δ` with (k\mapsto k+1, r\mapsto r+δ), while retaining the actual original tagged zero / unity / ζ₃ / ζ₃² mode, sign and observed-zero flag. This does not conflate signed flux with positive residual. It proves field-by-field preservation, `appendResidualFluxLedger`, `appendResidualFluxReflects`, `twoFluxStepsLedger`, `twoFluxStepsReflect` and a literal ζ₃ zero-observation specimen with (r=9\mapsto13) for δ=4. **Source-written, Agda not checked**.
- `scripts/check_rh_indexed_residual_flux_20261121.py`: **1,728/1,728 PASS** via actual local Python execution across 4 k-indices, 4 modes, 2 signs, 3 initial residuals, 2 observation flags, and two independently chosen increments (3×3). One and two-step square equality, source-order residual accumulation and zero/mode/sign preservation verified. Explicit check rejects pretending nonzero δ preserves a constant residual. This is a finite model check, not a general Agda kernel receipt or actual automorphic check.

### The genuinely original `IsLift` proof interface

The full `UpperTheory.TP.TLiftK : Prop` is **actually read from pinned original fork** at `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/HalfIndexLattices/TLiftK.lean`. It universally quantifies `E [Field E] [NumberField E] [IsCMField E]`, `B`, `W.GoodK`, `n,X`, then produces `∃ d₀, ∀ d≥d₀` and, for *the actual source* `W,δ,χX,χW,mX,mW,U,lam` and all the named IsHecke/ResEtaPow/HasExp/weight and automorphy premises, an actual `∃ U', IsLift B χX χW mX mW lam U U'`.

New Lean [#113 `RHSelectedThetaLiftConsumer.lean`](https://github.com/chboishabba/dashi_lean4/blob/research/alpoge-rh-source-admission-20261121/proofs/alpoge-lean433/RHSelectedThetaLiftConsumer.lean) imports the pinned source theorem `UpperTheory.TP.K.tLiftK` and exposes that **same telescope** for a chosen original `E,B,n,X`. It proves the selected conclusion by applying `UpperTheory.TP.K.tLiftK E B hgood n hn X hJ hHerm`. **This is only a faithful original source-theorem consumer**; it does not narrow the original theorem's transitive imports, construct a new Hecke character or show the finite three-mode C3 observer is a real `IsLift` datum. No original Lean 4.33.1 kernel check yet.

### Revised maximum-cut acceptance

1. **P0 priority unaffected**: original RH/GRH imports still stop at author theorem + paid root Mathlib↔Clay BIDI; no world/PG/CI.
2. **P1-F02B finite**: exact (r↦r+δ) indexed source ledger and conjugation-commuting transition source-written, 1,728 finite examples passed. Open: general signed residual semiring/group and actual source-accounting law. The current choice `Nat` represents additive unsigned residual contributions with a **separate** sign label; it does **not** implement arbitrary signed cancellation.
3. **P1-F04 original fibre**: an actual source `E,B,X,W,χX,χW,U,lam` and checked `IsLift` witness exists as a **theorem claim of the upstream author**. Our adapter exposes its exact type; the original upstream theorem still needs compatible Lean-kernel verification. Open: any source-extracted character/weight/zero mode or actual `k`-indexed family, and an observable/phase/residual intertwiner on this `IsLift` instance.
4. **P1-F05 Galois/star**: consume `galoisRepresentations_of_thetaLift` with source `GeoOne` and a **proved** original same-fibre observer, not a generalized `C3→TP.TLiftK` inference.
5. **Negative controls**: phase conjugation does not imply `IsHecke`; balanced zero does not imply empty phase carrier, zero L-function, or RH; exact signed residual must be evaluated against a genuine source observable, not created by a desired conclusion.

**Next smallest unpaid seam:** select one actual source Hecke character in the chosen upstream telescope and identify its restriction to a finite order-3 subgroup if it exists. The certificate must provide source-defined C3 action, character/inverse relations and index/residual observable, then prove that the source theta lift and the Galois/star consumer preserve that SAME observation. An arbitrary finite character table is not yet such a restriction.

**Trust:** 1,728 Python local exact cases are executed; both new Agda and original-version Lean source modules are written but uncompiled. No CI, Agda or Lean kernel receipts; no RH, GRH or universality acceptance claim.


## 21 November — correction: existing order-three CM/Hecke-associated owner recovered

**Do not claim DASHI lacks order-three Hecke-related structure.** Reopened actual source:
- `chboishabba/dashi_lean4` branch `agent/eisenstein-cm-point-endomorphism-maxcut-20261016`, `Integration/EisensteinJZeroPointCMExact.lean`: real `QuadraticAlgebra ℚ (-1) (-1)`, `omega_cube`, `omegaPoint` on Mathlib's actual nonsingular Weierstrass `jZeroCurve.Point`, `omegaPoint_order_three : ∀ P, omegaPoint (omegaPoint (omegaPoint P)) = P`, bijection and slope/addition covariance. This is a genuine order-three CM automorphism on an arithmetic elliptic-curve carrier.
- `DASHI/Mathematics/Arithmetic/EisensteinJZeroCubicSymmetryExact.agda`: source-written cubic equation (y²=x³+B) order-three action `rotateXThree` and `omegaXPreservesJZeroCubic`, with explicit **no automatic Hecke-character promotion**.
- `DASHI/Physics/Closure/HeckeCircleU1YReceipt.agda`: Hecke translation circle, order-six CM stabiliser at (z_{-3}), therefore containing an order-three subgroup. This is a Hecke-associated geometric action, not itself automatically a global Hecke character.
- `DASHI/Unified/TOEArithmeticCMRealizationExact.agda` and `DASHI/Mathematics/CrossPollination/EisensteinJZeroPointCMLeanReceiptExact.agda`: original source receipts mark **same-curve global Hecke/Grössencharacter construction as OPEN**, along with cubic/Jacobi, all-good-prime Euler, and L-series agreement. `Integration/EisensteinJZeroPrimaryNormalizationExact.lean` implements the primary Eisenstein generator condition at split primes, but the formal same-curve global character is not established by that normalization alone.

**Revised P1 search priority:** start with this already-existing **actual** `omegaPoint` order-three arithmetic action and CM stabiliser, not an invented C3. Then search the repository branches for any separate order-three Hecke-character owner missed by the current search index. A valid map into the fork's original `χX/χW : Chr ...` must prove the exact `IsHecke`, `ResEtaPow`, `HasExp` and `IsLift` requirements, with same-function and indexed zero/sign/residual correspondence. The (j=0) elliptic curve source is not automatically the fork's `E,B,X,W` automorphic input; **same-object identification OPEN**.

This is an evidence-scope distinction, not a denial that another repository file may already supply the Hecke character. The direct code search did not expose a completed global order-three Hecke character theorem; it did establish the concrete CM order-three point action and Hecke-associated stabiliser.


## 21 November — exact CM cubic-character donor and TOE PR reconciliation (latest)

**Recovered original native donor, not a new abstract order-three character:** Lean #69 `Integration/EisensteinJZeroCubicJacobiExact.lean` on `agent/eisenstein-lattice-counting-maxcut-20261012` has `CubicCharacterCertificate F` with a genuine `MulChar F ℂ`, a nontrivial square, and a demanded **full cube-fibre reindex theorem**
`Σ_x f(x³) = Σ_t (1+ψ(t)+(ψ*ψ)(t)) f(t)`. The original `jZeroTrace_cast_eq_cubicJacobiTrace` compiles this *conditional* character certificate to the same j=0 Frobenius trace and a pair of Mathlib Jacobi sums. The original source explicitly says the canonical chosen cubic character, Eisenstein-prime evaluation and number-field Hecke/Grössencharacter are further work. The order-three CM point symmetry in Lean #73 is a distinct source-paid donor. **Do not collapse finite-field multiplicative characters, Hecke Hecke-circle actions and globally adelic `UpperTheory.TP.TLiftK` Hecke characters.**

**New source-to-TOE interop:** `DASHI/Analysis/RHGRHCubicCharacterCMTOEConsumerExact.agda` imports the actual existing Lean #69 source receipt `EisensteinLeanInertPrimeLocalFactorReceiptExact`, source #73 point-group receipt `EisensteinJZeroPointCMLeanReceiptExact`, `TOEArithmeticCMRealizationExact`, `TOE369C3RealizationGraphExact` and the existing indexed zero/ζ₃/ζ₃²/residual frame. It states the source-observed finite order-three MulChar, the *unpaid* canonical cube-fibre certificate and global Hecke construction, and reuses **the exact** `TOE.eisensteinUniversalCharacter` edge. An `ActualCubicHeckeTOESourceWeld` is an explicitly uninhabited required source character restriction/IsLift/action compatibility record. This does **not** make the finite cubic test into Agda/Lean proof authority. **Agda kernel check OPEN.**

**Executed local exact finite-field regression:** `scripts/check_cm_cubic_fibre_indexed_20261121.py` was source-committed, alongside a separately locally executed equivalent full Python reference at `/mnt/data/check_cm_cubic_fibre_indexed_20261121.py`: **24,538/24,538** exact multiplicativity cases over (p∈\{7,13,19,31,37,43,61,67,73,79\}), **430/430** exact pointwise cube-fibre weights plus signed test-function reindexings. Use exact `ℤ[ω]` coordinate pairs; zero `(0,0)` is distinct from `1,ω,ω²`. This is constructive finite arithmetic evidence, not an original Mathlib `CubicCharacterCertificate` inhabitant or a global Hecke character. The **newly committed script** is not independently executed byte-for-byte in this tool session; its local equivalent was.

**Actual TOE branch inspection:** Agda TOE #1217 `toe/369-universal-realization` owns `TOEArithmeticCMRealizationExact` and the existing canonical universal→Eisenstein C3 edge. Its current ledger correctly marks `canonicalCubeFibreCertificatePaid=false`, `jacobiToSelectedEisensteinPrimePaid=false`, `sameCurveHeckeGroessencharacterPaid=false`, and global L-series false. TOE hyperfabric/pants #1291 `agent/toe-relate369-hyperfabric-pants-20261027` owns living roadmap `Docs/roadmaps/IndexedResidualCube369NineDOFMaxCut20261120.md` and `GovernedIndexedResidualCubeExact`. Its actual indexing contract keeps history (h), time (t), refinement (k), Frobenius iteration (j), and consumer version (v) **distinct**. Our RH `IndexedZeroPhaseFrame Index Sign Residual` accepts such a composite index but the concrete `Nat` fixture **does not establish these five distinct coordinate transports**.

**Highest-alpha next gates (reverse solve):**
1. Build the original cubic-character **canonical cube-fibre certificate** from the original `MulChar` and finite-field cube fibres; no newly invented character language. The exact finite test supplies regression examples, not the theorem.
2. Attach selected primary `ℤ[ω]` split-prime Jacobi evaluation to original **same curve** j=0 Frobenius, then construct its number-field Grössencharacter/Hecke data, keeping degree-one/degree-two Euler factors distinct.
3. ONLY THEN investigate an actual order-three restriction on a source `χX/χW : Chr` in upstream `TP.TLiftK` with real `IsHecke, ResEtaPow, HasExp, IsLift` and Galois star `Row0b recT`. Character value `ψ(t)` in finite `F_p` cannot be silently identified with the global Hecke character.
4. Attach the **full indexed residual hyperfabric** through the already-owned #1291 governed cube with coordinates (h,t,k,j,v), actual sign and residual, and a true mode/transition/consumer commuting law; preserve observed zero distinct from scalar zero and (ω)-phase.
5. Keep external RH P0 terminal admission separate and unblocked by this P1 CM geometric improvement. No CI or whole-proof ingestion.

**TOE integration sequencing:** #1533 owns this **new source-gated interop**; #1217 and #1291 remain their original source owners. Do not import unmerged #1533 modules directly into other PR branches. First land/check the source owner, then attach it to the existing TOE aggregate and the #1291 indexed cube using the original source transports, without duplicate C3 or TOE graphs.
