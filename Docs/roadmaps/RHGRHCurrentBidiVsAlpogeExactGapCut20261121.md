# Current DASHI RH BIDI vs Alpöge RH / GRH — exact gap-directed depth cut

## 21 November — LATEST original DASHI Dirichlet-owner audit, P0 source correction

The user correctly noted our repo already has Dirichlet content. Exact source readback `DASHI/Physics/QFT/ConductorVsDiscriminantReceipt.agda` provides ORIGINAL six discriminant rows `D=-3,-4,-7,-8,-11,-12`, with separate order conductor, field discriminant, primitive **quadratic Dirichlet character conductor**, modular/order level and proof-relevant row consistency. These are real finite Dirichlet arithmetic data, not an opaque new character ontology. P0 must not replace them with a duplicate modulus table.

New original-owner Agda source `DASHI/Analysis/RHGRHDirichletConductorP0SourceCutExact.agda` consumes the existing rows and source-written proves:
- `D=-3`: order conductor **1**, primitive quadratic Dirichlet character conductor **3**.
- `D=-8`: order conductor **1**, primitive Dirichlet conductor **8**.
- `D=-12`: order conductor **2**, primitive Dirichlet conductor **3**, modular/order level **12**; the character conductor is **not** 12.
- `D=-3` and `D=-12` share a primitive quadratic character conductor **3** but have different order conductors. This protects against fake same-object identification of CM order, level and character, especially at j=0/ω.

**Important mathematical distinction:** the quadratic primitive conductor-3 character associated to `D=-3` is NOT the same character as the **order-three cubic finite-field** `MulChar` used at split primes (p\equiv1\bmod3); character order, modulus/conductor, codomain, action and analytic L-function are separate typed requirements. The pinned fork's all-character target quantifies over `DirichletCharacter ℂ N` and source `DirichletCharacter.LFunction χ s` for arbitrary `N,χ,s`, including primitive and imprimitive. These six CM rows provide finite input checks only, not an all-moduli character proof.

Separate exact source inspection:
- `DASHI/Analysis/RiemannAnalyticSubstrate.agda` already has a source `ZetaHalfPlaneLayer` with named Dirichlet-series equality and Euler product **interface**, but does not construct `DirichletCharacter ℂ N` or its genuine L-function.
- `DASHI/Analysis/RiemannOpaqueZetaHalfPlaneCountermodelExact.agda` proves the warning is substantive: the opaque `ZetaEqualsDirichletSeries` field does not force selected function-value identity.
- `DASHI/Mathematics/Automorphic/EllipticInfiniteLFunctionRoadExact.agda` has a genuinely separate elliptic L-function Euler/Dirichlet interface, with analytic continuation, functional equation and completed analytic rank still OPEN.
- Original P0 **Lean #113** `RHGRHP0DirectionalSourceCut` already consumes the fork's actual all-character `EveryCharacter` and its exact Dirichlet right-half/strip/primitive-strip conclusions. This is the strongest P0 terminal proof owner, rather than elevating finite quadratic conductor rows to GRH.

**Next P0 cut:** local Lean 4.33.1 source-closed kernel/axiom acceptance of **original all-character** theorem and all three Dirichlet published targets, followed by same-character/codomain/analytic L-function transport if exporting to Agda. A specific quadratic CM character can test a selected case only AFTER an actual `DirichletCharacter` is constructed with correct primitive modulus and proven equal to the original source character. Explicitly do **not** identify a finite field cubic character with the quadratic conductor-3 character from (D=-3), nor claim that this selected case proves global GRH. New Agda source **not kernel checked**, no CI.

## 21 November — LATEST P0 is GRH first; original source directional BIDI now explicit

The user clarified **P0 GRH is controlling**, so prioritize the exact original **all-Dirichlet-character** terminal, not P1 geometric construction. New [Lean PR #113 `proofs/alpoge-lean433/RHGRHP0DirectionalSourceCut.lean`](https://github.com/chboishabba/dashi_lean4/blob/research/alpoge-rh-source-admission-20261121/proofs/alpoge-lean433/RHGRHP0DirectionalSourceCut.lean) composes source-pinned original `RowSrc.galoisLocalGlobalStrong_recParameter` → `vwin_of_row` → `every_character_of_literature_of_vWin` → `UpperTheory.EveryCharacter`, and **then** original `Formalism.VW.rh_of_every`, `Claim.strip`, `Formalism.VW.critLine` to all original published RH/Dirichlet targets.

**Genuine BIDI on original RH target:** `RiemannZetaZerosOnLine ↔ Mathlib.RiemannHypothesis` is definitionally the same source predicate per pinned `src/Statements.lean`. `Claim.Zeta ↔ RiemannHypothesis` is original `Claim.zeta_iff`. `Claim.HalfPlane ↔ UpperTheory.EveryCharacter` is original definitionally identical all-character right half-plane predicate. **Direction to distinguish:** EveryCharacter → RH, but ordinary RH does **not carry a source theorem** implying EveryCharacter/Dirichlet GRH. Do NOT describe this as proof that RH→GRH is mathematically impossible. The independent root `MillenniumExternal.ExactTargetSurface` has `Millennium.ClayRiemannHypothesis ↔ Mathlib.RiemannHypothesis`; it is not a global GRH target for every character.

**GRH P0 stop depth:** preserve the source-authorized `EveryCharacter` and original 4.33.1 proof spine, inspect `#print axioms` and local kernel admission, then separate proof-compatible root/Agda transport. **No local Lean binary/kerneled statement acceptance, no CI**. The external fork's reported acceptance in a separate environment is not DASHI receipt. The finite Monster C27 charge-additive conditional mode, native sign holonomy, π/CM cubic Jacobi and 9DOF may yield an interesting **future P1 source proof improvement**, but no actual source `Chr/IsHecke` or `GalStar.Row0b recT` producer from them exists; do NOT put it on the P0 critical path.


**Date:** 21 November 2026. Source-pinned fork `chboishabba/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`; DASHI Lean integration [#113](https://github.com/chboishabba/dashi_lean4/pull/113); golden Agda [#1533](https://github.com/chboishabba/dashi_agda/pull/1533). **Steelman → BIDI → reverse solve; original source typed objects before theoretical analogy.** No CI, no original Lean/Agda kernel run in this cut. Typed Lean source written but uncompiled.

## Executive conclusion: TWO different reverse problems, not one missing estimate

**P0 terminal RH acquisition:** the fork has an original theorem of type Mathlib `RiemannHypothesis` (via `UpperTheory.EveryCharacter`), and DASHI's existing `MillenniumExternal.ExactTargetSurface` already owns the `Mathlib RiemannHypothesis ↔ Millennium.ClayRiemannHypothesis` theorem. Thus our *old analytic signed-estimate gap is NOT required* to import the externally established RH terminal theorem into Lean Clay. The minimum cut here is kernel-coherent source/theorem admission between Lean v4.33.1 and DASHI v4.35.0-rc3, then actual Agda complex/function/zero/line identity plus trusted proof transfer.

**P1 genuinely better geometric RH proof:** a separate, ambitious task is whether the external all-character nonvanishing producer can supply *our specific source-indexed signed test, near/far, or pole-quotient bound* or be replaced by a smaller geometric producer. Terminal `RiemannHypothesis` does NOT generally imply arbitrarily stipulated target-centered local cosine sums are bounded with the exact constants demanded by our particular G2 contradiction. The original proof's proof of RH and our original G2 contradiction are logically different architectures; no ghost theorem transfer from the former's conclusion to the latter's internal lemmas.

## 1. Original DASHI strongest current BIDI — distinct owner levels

Direct original source readback (not just search result):

| Owner | Already available or checked in source ledger | Exact OPEN and why |
|---|---|---|
| `DASHI/Analysis/RiemannAristotleG2CurrentCutExact.agda` | G1/G2a/G2b/G2c finite Gram, norm determinant, polarization; G2d/e determinant taper and finite near scalarization; signed near and far in a common determinant coordinate, plus scalar off-energy consumer; explicit reverse balance no-go | target-centred local-zero signed cosine/exponential-sum bound on **literal q(u), nearOffFinset(t,J), multiplicities, off-real part and target t**; plus **balance-breaking** or changed comparison object. Mere sharpened cancellation with unchanged projective balance can never supply the strict contradiction |
| `DASHI/Analysis/RiemannG2TargetCenteredScalarCancellationAssemblyExact.agda` | `LiteralTargetCenteredScalarProblem` defines the genuine q, `dSigma`, `totalSignedResponse`, `targetCenteredIntegral`, and same-literal identities; `directSignedPaymentClosesCancellationReceipt` is available | actual inhabitant of `DirectSignedConsumerPayment P` on this literal selected problem. It is **not** a generic positivity theorem |
| `DASHI/Analysis/RiemannG2DeterminantConsumerQuotient369Exact.agda` | for fixed kernel, `q=det3(n1,n2,h)` is an exactly sufficient observer and reconstructs kernel times determinant | cannot infer target-centred t oscillatory cancellation or a source author's orthogonal theta determinant without same-function equations |
| `DASHI/Analysis/RiemannG2CommonC3DeterminantCovarianceCompilerExact.agda` | common C3 action on *all three rows* preserves q, which preserves the fixed-kernel consumer | `LiteralRiemannCommonC3Attachment` to the **actual** nuisance rows/taper remains uninhabited; orbit invariance does NOT automatically produce signed cancellation |
| `DASHI/Analysis/RiemannG2BidiCutReconciliationExact.agda` | explicitly distinguishes scalar local-zero estimate from downstream post-Schur finite-near energy consumer; the generic Schur compiler is source-owned | `G2ScalarToFiniteSchurBridge` still uninhabited, needing near-carrier identity, taper weight, assembly, Schur transport and bound compatibility |
| `DASHI/Analysis/RiemannG2LiteralSpectralZeroWeldExact.agda` | true explicit-formula and xi-zero interfaces; source-owned reflection-stable near and exact far cutoff | actual equality of spectralZeroForm with determinant-taper near+far object; separate arithmetic-to-finite-Schur bound. Representation weld alone does not give signed cancellation |
| **AUTHORITATIVE current pole quotient**: `DASHI/Analysis/RiemannAristotleCurrentFrontierExact.agda` | independent universal pole-quotient `cluster = offOrdinate + Gamma`, bounds `B_off ≤ A_off`, `B_Gamma ≤ A_Gamma`; source-owned final consumer compiler and quantitative margin math | **common selected cutoff J** for off signed near+far allowance, Gamma allowance on actual same universal taper, strict `A_off+A_Gamma<M_cluster`, genuine attachments. In particular, this owner explicitly **does not equate the old G2d determinant taper with the final universal pole-quotient taper** |
| Agda `AlpogeRHOriginalClayEndpointBidiExact` | mathematical conditional RH ↔ original Agda Clay witness, given actual predicate transports | uninhabited cross-language same-object zero/critical-line/proof transport (independent of G2 signed route) |
| Lean `Synthesis/RiemannSelectedRHMaxCutFrontier.lean` | A1 three-tap inverse-square scalar compiler; A2 V4/H4/G3 signed sixth/eighth debt compilers and Route B signed fifth finite terminal compilers | A1 `ThreeTapInverseSquareShellPartitionBound`, curvature and gap margin; A2 actual leading constants, horizontal far curvature, compensation lower bound and strict scalar or no-go; Route B three source-specific eventual signed boundary/gap/outer limit analytic producers. All were documented OPEN, not discharged by similar words in a new source proof |

**Critical priority correction:** do not call the old G2d scalar the *only/current strongest* RH mathematical frontier: its BIDI is one viable analytical route but the later **authoritative pole-quotient/Off/Gamma** source is a different terminal consumer. Match **both** to an external candidate before transporting a bound.

## 2. Original fork — exact source theorem spine and the paid BIDI

Actual source at pinned commit:
- `src/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean`: **`Claim.HalfPlane`** is precisely
  `∀ N χ s, 1/2 < Re(s) → (χ ≠ 1 ∨ s ≠ 1) → L(χ,s) ≠ 0`.
  `Claim.Strip` and `Claim.Zeta` are the literal zero-location consumers.
- `src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean`: **`UpperTheory.EveryCharacter` is definitionally the same right-half-plane predicate**; no new zero-free observer type needed.
- `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean`: original `Claim.strip : Claim.HalfPlane → Claim.Strip` via primitive-reduction/functional-equation; `Claim.zeta : Claim.HalfPlane → Claim.Zeta`; **`Claim.zeta_iff : Claim.Zeta ↔ RiemannHypothesis := Iff.rfl`**. This is an *actual source theorem*, so no generalized "Clay positivity" substitute.
- `src/Formalism/GammaFactorNonvanishing/CritLine.lean`: original `Formalism.VW.critLine` and `Formalism.VW.rh_of_every` derive primitive strip and Mathlib RH from every-character right-half-plane nonvanishing, using gamma factor nonzero, functional equation and trivial mod-1 character.
- `src/Supplements/Kernels/MainTheorems.lean`: `allChi := UpperTheory.FinalTheorems.everyCharacter`, `rhOfAll := Formalism.VW.rh_of_every allChi`, and remaining 3 consumers.
- `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`: `everyCharacter` is obtained from `everyCharacter_of_row` and actual `galoisLocalGlobalStrong_recParameter`.
- `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/RowSrc.lean`: `galoisLocalGlobalStrong_recParameter : GalStar.Row0b recT` from `galoisRepresentations_of_thetaLift tLiftK`.
- `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/IntegralStructures/GaloisRepresentationsOfThetaLift.lean`: the former consumes `geoOne_holds` and `tLiftK`.
- `src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/ThetaParseval/ThetaKernels/TLiftK.lean`: `tLiftK` from `tLift_holds_k`.

**New Lean [#113] source-authored `RHClaimBidiExact.lean`:** `Claim.HalfPlane ↔ UpperTheory.EveryCharacter` (definitionally), `Claim.Zeta ↔ RiemannHypothesis` by the ORIGINAL `Claim.zeta_iff`, and existing `Formalism.VW.rh_of_every` proves right-half-plane → Mathlib RH. **No actual Lean kernel run yet**.

## 3. Which gap should determine how deep to inspect their proof?

| Our target | The fork gives now | Stop depth and next truly unpaid lemma |
|---|---|---|
| **RH in DASHI Lean Clay** | source-proven original `RiemannHypothesis`, exact existing Mathlib↔Clay theorem | **STOP at `rhOfAll` / `allChi`** for terminal. Pay local compatible-kernel admission only; deep theta discovery is irrelevant to this terminal |
| **Original Agda RH endpoint** | same RH theorem plus original Agda `RiemannHypothesisFor` | **STOP at literal `RiemannHypothesis` theorem** then implement source-backed complex/function/zero/line transports and actual trusted proof handoff; not by a copied record witness |
| **GRH (Dirichlet)** | stronger `EveryCharacter` and original `Claim.strip`, `Formalism.VW.critLine` | **STOP at `EveryCharacter`**, use original character carrier to import S01–S22 only when exact theorem assumptions match |
| **Our G2 source scalar signed estimate** | all-character zero-free line implies RH, but gives *no explicit same-q integral inequality in the source chain* | **DO NOT assume theorem transfer.** Search only original `Claim.strip` / `HalfPlane` / `rh_of_every` for an actual equality or signed cosine sum on our (q(u),t,J); absent that, deeper theta branch may improve *method* but does not pay `DirectSignedConsumerPayment` |
| **Authoritative universal pole-quotient Off/Gamma** | no displayed source theorem with literal original `B_off`, `B_Gamma`, (M_{mathrm{cluster}}) | seek exact source `UpperTheory.EveryCharacter` **analytic/theta producer** and ask if its positivity/zero-free engine yields the *same selected taper/cutoff and signed allowances*. Until matching selected source identity appears, do not claim closure of old Off/Gamma inequality |
| **Novel geometric shortening** | the true `TP.TLiftK → GalStar.Row0b recT → EveryCharacter` chain | descend **only to these source types**. Compare original theta/geometry to existing `PenumbralSingularThetaIntegral`, `C3CubeFourier27Exact`, `RiemannG2CommonC3DeterminantCovarianceCompilerExact`, `Griess1990RationalAlbertTrialityTransportExact`; prove typed same-object or explicit no-go before replacing an original producer |

This is an **asymmetric BIDI**: their `EveryCharacter` produces RH and GRH, but **RH alone does not imply GRH**. Their source's half-plane proposition is strictly stronger in scope than the Mathlib RH proposition. Our analytic scalar inequalities are also not automatically equivalent to either proposition.

## 4. Highest-alpha exact next implementations

**P0 (immediate, minimum):**
1. locally typecheck `RHClaimBidiExact.lean` and `RHTopCut.lean` in the pinned original fork 4.33.1, inspect exact axioms. Do NOT ask for MainTheoremsAll's separate class-number module unless compiler closure reveals necessary dependence;
2. re-elaborate source-compatible Mathlib↔Clay BIDI in one kernel (or exact typed source translation), then deliver the original Lean Clay `Millennium.ClayRiemannHypothesis` without new analytic hypotheses;
3. same-object Agda analytic carrier/complex normalisation, genuine theorem proof transport (the new source-written Agda record still uninhabited).

**P1 (geometric proof improvement, separate hypothesis):**
1. select **one** real external typed donor type (`TP.TLiftK` first or `GalStar.Row0b recT`) and verify its actual mathematical data/parametrisation; use original source unmodified;
2. build or refute precise `DASHI-geometry → TP.TLiftK` and `DASHI-G2-q → their real theta determinant` statement; explicit operator/measure/cutoff equality matters more than 27-state counts;
3. if a true identity found, re-compose the original `EveryCharacter` producer and compare actual imported theorem closure. Otherwise mark the geometric lane independent without reopening RH terminal;
4. **never claim G2 sign cancellation merely from C3 invariance**; the repository explicitly contains symmetry/Gram/balance no-go controls.

**Scope**: no world ingestion/PG, no CI, no Agda/Lean kernel execution this session. Documentation and Lean BIDI source are current; proofs remain to be checked and the original analytic zero-function/complex weld remains open.

## 21 November — executable first bridge at the precise BIDI gap: zero-horizontal collapse

### Reverse solve results from **actual** source definitions

- The checked fork owner `Claim.zeta_iff : Claim.Zeta ↔ RiemannHypothesis` sits on the existing Mathlib `riemannZeta`, excludes trivial zeros and (s=1), and yields `s.re = 1/2`. On this *same actual zero*, `s.re - 1/2 = 0` and `cosh ((s.re - 1/2) u)=1` for every real (u). These are elementary **consequences** of RH, not a proof of RH.
- The DASHI G2 **original literal** `LiteralTargetCenteredScalarProblem` specifies `dSigma sigma = integrate (4*q(u)*multiplicity(sigma)*cosh(offRealPart(sigma)*u)*cos((ordinate(sigma)-target)*u))`. This is the exact consumer contract, and `RiemannG2TargetCenteredScalarCancellationAssemblyExact.dSigmaIsLiteralKernel` is its original owner.
- Therefore **if** `ZeroIndex P` is proved to denote the genuine same Mathlib Riemann nontrivial-zero carrier, and `offRealPart` is literally the real displacement `s.re-1/2`, the cosh factor cancels **without rebuilding G2**. Our signed cosine sum remains mathematically unpaid.

### Implemented source consumers (not compiled yet)

- [Lean #113 `RHZeroHorizontalBridge.lean`](https://github.com/chboishabba/dashi_lean4/blob/research/alpoge-rh-source-admission-20261121/proofs/alpoge-lean433/RHZeroHorizontalBridge.lean): `zero_horizontal_of_mathlib_rh` and `cosh_horizontal_factor_of_mathlib_rh` use **Mathlib's own** `RiemannHypothesis`, `riemannZeta`, original exclusion of `-2(n+1)` and (s≠1), no substitute zeta carrier.
- [Agda #1533 `RiemannG2AlpogeZeroLineCosineCollapseExact.agda`](https://github.com/chboishabba/dashi_agda/blob/research/alpoge-grh-geometry-bridge-20261121/DASHI/Analysis/RiemannG2AlpogeZeroLineCosineCollapseExact.agda): `SameZeroCarrierCollapse` asks for **four transparent properties**: actual G2 zero index's horizontal displacement is zero, zero·u=zero, cosh(0)=one, and original integral congruence. It defines `sourceCosineCoshKernel`, `collapsedCosineKernel`, and proves pointwise and original `dSigma` integral equality under these premises, using the existing original `dSigmaIsLiteralKernel`.

The **only substantive new mathematical seam** between those new files is `actualMathlibZeroToSelectedG2ZeroIndexWithSameHorizontalDisplacement`, plus the trusted Lean→Agda transport and source-accurate real/integral identities. We must not imply this mapping already exists merely because the indexed zero states have similar coordinates. `SameZeroCarrierCollapse` is still uninhabited.

### Finite exact test (local SymPy 1.14; NOT kernel acceptance)

The full scalar source kernel (4 q m\cosh(a u)\cos((b-t)u)) equals (4 q m\cos((b-t)u)) after (a=0). SymPy reduced the symbolic difference to exactly zero.

Counterexample: with (m=1), (b=t=0), (u\in[-1,1]), and (q=+1) versus (q=-1), the collapsed integral equals respectively (+8) and (-8). Thus **RH zero-horizontal geometry does not force positivity, nonnegativity or cancellation for an unconstrained signed taper q**. An actual G2 q has its own constraints; this is a *logical non-entailment illustration*, not an actual Riemann-zero counterexample. Actual `G2d` / universal pole-quotient taper constraints and Off/Gamma budgets cannot be silently erased.

### Precise remaining BIDI cut, and required external depth

| Need | Current status | Inspect how far into fork? |
|---|---|---|
| RH terminal into Lean Clay | original `RiemannHypothesis` plus existing Lean Mathlib↔Clay equivalence | **stop at** `rhOfAll` / `MainTheorems` |
| Strong Dirichlet GRH | actual `UpperTheory.EveryCharacter`, `Claim.strip`, primitive character proof | **stop at** `allChi` / `EveryCharacter` |
| Agda original RH theorem | actual analytic zero function/complex carrier identity and trusted import still OPEN | **stop at** actual Mathlib RH theorem; pay Agda object weld |
| Agda original G2 zero-horizontal cancellation of cosh | source-written conditional exact G2 integral and Mathlib real-offset theorem; actual `zeroIndex↔nontrivialZero` OPEN | **stop at** `Claim.zeta_iff`, `VW.rh_of_every` or imported RH theorem; no need for theta proof dependencies |
| G2 target-centred signed cancellation | transformed cosine sum still indefinite without q and phase estimates; old balance-breaking premise remains OPEN | **only inspect deeper** if fork contains matching exact q/taper/zero-sum/source operator, otherwise independent |
| Universal Off+Gamma | different original universal taper, source-checked distinction from G2 determinant | do not reuse determinant-taper payment without real source same-taper transport |
| Geometric improvement to fork itself | actual `TP.TLiftK` / `GalStar.Row0b recT` are deeper source-typed targets | descend selectively to those **only** after testing exact geometric producer eligibility |

No new postulate is asserted, no unconditional algebraic `RiemannHypothesis` witness is fabricated and no stronger analytic theorem is claimed. No CI, no local Lean or Agda kernel run. The exact symbolic test is a finite regression, not completion of RH.

### Logical direction / vacuity warning (mandatory)

**This collapse is a forward consumer of an already admitted RH theorem, not a step toward proving RH.** In the original G2 setup, `nearOff` may select *off-critical-line zeros*. Under RH there are no such actual zeros; quantification over the selected off-line carrier is then vacuous. Treating the hypothesis that all selected zero horizontal displacements vanish as an assumption within a proof by contradiction would be circular if that assumption is precisely the RH conclusion being sought. The result is useful for *post-RH simplification and checking the same-object weld*, or potentially for proving a conditional consequence in a broader zero population, **not for paying an independent G2 contradiction or replacing the original fork proof**. The signed `+8/-8` test illustrates nonentailment in an abstract scalar model, not an actual off-line zero under RH.

For an **independent geometric improvement to the external RH proof**, return to the *upstream original source* `TP.TLiftK → GalStar.Row0b recT → EveryCharacter` and prove the same typed producer from existing DASHI geometry without assuming `RiemannHypothesis` or `Claim.Zeta`. Mark any geometric route requiring zero-horizontal RH as circular for RH-proof purposes.
