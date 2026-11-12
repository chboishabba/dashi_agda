# PR #1444 — fail-closed audit of proposed “all gates CLOSED” argument

**Date:** 2026-11-12. **Status:** source-written algebra, physical gates OPEN.  
**Basis:** user-supplied 289-line “complete mathematical and constructive resolution” (pasted on 2026-11-12), compared with live original Wilson PR #1444 and the selected Agda source declarations.  
**Attribution:** the proposed argument's standard mathematical ideas are distinguishable from DASHI's exact source interfaces, the existing cited Yang–Mills/Balaban/OS theorems, and any new DASHI proof terms. No unverified external theorem is promoted into a source receipt.

## The strongest source-backed bridge implemented in this round

New `YMClayE1D1OriginalCrossNumeratorNormalizedMomentFactorExact.agda` reuses the **exact original n=3 fine-blocked and n=1 bare SU(N) Wilson numerators and partitions**. With positive partitions from `YMClayOriginalWilsonFiniteNumeratorOrderExact.originalWilsonPartitionStrictlyPositive` and an **explicit coherent real division cancellation law** on the selected `divide` operation, it establishes

`X(F) = (E_f(F) - E_b(F)) (Z_f Z_b).`

- `originalFinePartitionPositive` / `originalBarePartitionPositive`: actual original source partitions, not an independently postulated number.
- `originalFineMomentTimesPartition` / `originalBareMomentTimesPartition`: source-specific positive quotient reconstruction under an explicit real field law.
- `originalCrossNumeratorIsMomentDefectTimesPartitionProduct`: exact scalar cross-product expansion from those sources and `subMulDistributes`.
- `originalWordPairCrossNumeratorIsNormalizedDefect`: specializes the exact identity to original Wilson word products `W_u W_v = W_{u++v}` via the existing source-word compiler/congruence.

This is an **identity**, not a numerical estimate. It does not establish a small `|X(F)|`, a cutoff-uniform norm or a physical RG map contraction. Kernel acceptance remains pending.

## Exact falsifiability controls implemented

1. `YMClayE1D1CrossNumeratorCenteringDoesNotForceContractionExact.agda`: an actual finite two-point model with normalized nonnegative Dirac weights. Its unit cross numerator is **zero**, while an explicitly {0,1}-bounded nonconstant indicator has cross numerator **one**. This is **not an SU(N) counterexample**; it establishes that `X(1)=0` + boundedness do not logically provide RG decay on nonconstant tests.
2. `YMClayRealSubtractionLawIndependenceExact.agda`: ordinary Nat addition/multiplication and identically-zero subtraction satisfy the named algebraic subtraction-interaction fragment `subSelf`, `subAddCancelMiddle`, `subAddDistributes`, `subMulDistributes`, `mulSubDistributes`, but `1-0 = 0 ≠ 1`. This is **not a full RealAnalysisAxioms model**. It shows P0.01 cannot be silently assembled from that limited fragment. The actual Bishop backend uses setoid equality `_≃_`; it is not definitionally the independently postulated propositional `ℝ` of `RealAnalysisAxioms`.
3. `YMClayD2ObservedDecayDoesNotForceFullSpectralGapExact.agda`: one concrete finite transfer kills its selected observed excitation while fixing a distinct nonzero nonvacuum mode. This is **not a physical OS transfer operator**. It isolates the need for the same Hilbert-space identification and a uniform/dense observable family before promoting selected correlation decay to a spectral gap.

All controls are imported into `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda` and targeted by `scripts/check_ym_original_rg_p0_kernel.sh`.

## Audit of the supplied claim chain

| Gate | Supplied argument | Exact missing source / status |
|---|---|---|
| P0.01–05 | Subtraction and quotient cancellation in an unspecified constructive real field; therefore `X(F)=Z_b N_f(F-E_bF)` is unconditional. | **NOT unconditional.** `RealAnalysisAxioms` names independently postulated `_-ℝ_`, `-ℝ_`, and external `divide` with no full mutual compatibility. Bishop's constructed `_≃_` is a different equality/carrier. Existing centered source proofs retain `OriginalRealCenteringLaws` and `OriginalRealPositiveDivisionLaws` parameters. |
| P0.06 | Standard unitary eigenvalue/spectral theorem proof that `|Tr(U)/N|≤1`. | Correct standard mathematical strategy, **not the cited concrete Agda proof**. `SUNMatrixRealTrace` only provides a trace function and cyclicity; `constantCyclicRealTrace` is a negative control. Need actual finite complex matrices, trace normalization and source-verified inequality, then the existing all-word bound transport. |
| P0.09 | Write `U=e^{aξ}V`, assume `E ξ=0`, posit massive inverse `(-Δ+m_eff²)⁻¹` with exponential decay and conclude `O(a^γ)`. | **OPEN.** No defined original gauge-covariant fine-fiber coordinate map, Jacobian, valid gauge fixing, centered first-moment cancellation, uniformly controlled Taylor remainder, or native original Wilson polymer estimate. Assuming `m_eff>0` risks circular use of a mass scale before proving a gap. Strong-coupling/high-temperature estimates are not interchangeable with the asymptotically-free UV scale. |
| E1 | One-loop beta coefficient implies strict RG contraction; invoke Banach fixed-point theorem. | **OPEN.** A perturbative coefficient does not prove a nonperturbative contraction of the selected full effective-action operator, scale-summable errors, cylinder projective consistency, positive interacting limit or reflection positivity. Relevant/marginal directions need explicit treatment. |
| D1 | Connected-polymer weights already satisfy `|ω(X)|≤K e^{-m₀|X|}`, yielding mass decay. | **OPEN.** That physical Wilson connecting-activity estimate is a principal missing R576/B1 theorem; the source mixed-log is currently a **formal** two-source jet, not an established analytic differentiated log `Z`. Need actual rooted-shell convergence and cutoff-uniform constants. |
| D2 | Reflection positivity on `μ∞` and one selected correlator's decay imply a positive gap on full OS Hilbert space. | **OPEN.** Must first construct the same interacting `μ∞`, preserve full reflected-word Gram positivity, identify its translation semigroup and self-adjoint H, and establish a sufficiently uniform decay estimate on a dense/separating nonvacuum subspace. |
| N1 | A schematic perturbative four-point term `-g²∫G⁴+O(g⁴)` proves non-Gaussianity; alternatively `σ=m_gap²/(2π)`. | **OPEN.** Neither term is a kernel-certified nonzero same-continuum SU(N) Wilson witness. An area-law string tension is not generally determined by the mass gap through that universal equality. |
| G1 | Positive `h∨`, Haar measure and one-loop asymptotic freedom automatically extend all quantitative proofs to every compact simple group. | **OPEN.** Each selected compact simple carrier, faithful finite representation, reflected OS measure, group-indexed constants and physical limit must be constructed/verified; one-loop group theory alone does not establish full constructive interacting QFT. |

**Consequent status:** 0/5 terminal Clay gates E1, D1, D2, N1, G1 proved. The document's final “CLOSED” table cannot be used as a verified mathematical or Agda receipt.

## Highest-alpha next source actions

1. **Immediate kernel gate:** on the actual PR checkout run `bash scripts/check_ym_original_rg_p0_kernel.sh`, and fix the first actual Agda error in import order. No CI substitution.
2. **Selected real field weld:** implement (not merely assume) `OriginalRealCenteringLaws` and `OriginalRealPositiveDivisionLaws` for the **same** real carrier, preserving equality/quotient distinction. The concrete Bishop backend is setoid-based and cannot be silently substituted for the postulated `ℝ`.
3. **P0.06 matrix trace:** construct the true `N×N` finite complex matrix trace with normalized real part and bound. Propagate through the existing original Wilson all-word theorem.
4. **P0.09 original physical RG producer:** establish a truly uniform, explicitly coupled original Wilson all-word weighted cross-numerator bound at correct UV scales, including `u`, `v` and `u++v`. The new normalized factorization gives the exact scalar transport target, but not the estimate.
5. **E1/R576/R577/N1/G1:** maintain separate same-object continuum, connected-cluster, OS spectral, noncollapse, and group-coverage receipts.

**Verification status:** GitHub source commits and readback, **not** Agda 2.9 kernel acceptance. No compiler or independent physical analytic estimate was run in this environment.


## 2026-11-12 subsequent same-carrier constructive Bishop P0 implementation

After this audit, the P0 scalar work advanced by two new Agda modules:
- `YMClayP0BishopRealCarrierInstancesExact.agda` proves native Bishop `x-c≃x+(-c)*1`, `x-0≃x`, genuine centered additive cancellation, and `(n/z)*z≃n` under native `0<z` using Murray/Csimma's imported setoid solver and proved inverse. Those are **concrete constructed Bishop real** proof terms, not uninstantiated record fields or new postulates.
- `YMClayP0BishopToOriginalWilsonRealWeldExact.agda` proves that a *single faithful interpretation* of `RealAnalysisAxioms.ℝ` into the Bishop setoid, reflecting equality and preserving the **actual source-selected divide**, supplies both existing `OriginalRealCenteringLaws` and `OriginalRealPositiveDivisionLaws` for original Wilson P0.01–05. Its `OriginalWilsonToBishopScalarWeld` itself remains UNINHABITED: the original Wilson scalar carrier is independently postulated and not definitionally Murray's Bishop carrier. A genuine quotient/equality-preserving same-carrier realization must be built instead of substituting setoid proofs for propositional equality.
- Existing concrete rational SU(2) quaternion normalized trace bound owner `BalabanSU2RationalWilsonTraceBoundExact.agda` had a missing explicit rational ring solver import; repaired. This is a concrete SU(2) *subcase*, not the full `SUNMatrixRealTrace` matrix source for arbitrary N.

**Remaining P0.06 signed-test gap:** `|W|≤1` does not imply a signed Wilson word is pointwise nonnegative, so it does not directly inhabit the positive-test complement of `originalWilsonNormalizedBelowOne`. To obtain `|E_W W|≤1`, prove `|N(W)|≤N(|W|)` from the actual Haar positivity+linearity with valid ordered-real absolute compatibility, or construct a certified affine-shifted [0,1] test. No such source proof is currently present.

**D2 important logical precision:** decay `⟨ψ,e^{-tH}ψ⟩≤ C_ψ e^{-mt}` on a dense core with **one common positive exponent m**, a genuine *positive self-adjoint* common H, and an actual spectral-measure theorem can establish spectral support above m even with unbounded state-dependent `C_ψ`. Density alone does not justify taking a limit to a norm-1 semigroup bound with such prefactors. This sharpens rather than negates the existing single-observable hidden-mode counterexample. Neither same-H source nor its all-core decay and spectral transfer is present in this PR.


## Second supplied all-CLOSED argument (2026-11-12): specific unresolved proof seams

The later 213-line proposed resolution now contains a suggested constructive matrix `SUNMatrix(N)`, finite-width row-unitarity/Cauchy–Schwarz estimate, a claimed `G_a(p,p) ≤ C_0 g_0²(a)`, a 64^n rooted tree activity entropy estimate, dyadic-cylinder limit, OS spectral core, four-point cumulant and dual Coxeter extension. These are **proof targets/heuristics** unless the cited source-specific constants, types, maps and estimates are actually inhabited. Its final eight-row `Closed` column is not an Agda or Clay receipt.

Critical boundaries:
1. **P0 scalar:** native Bishop `_≃_` identities are source-written, but the independently postulated original Wilson `RealAnalysisAxioms.ℝ` uses `_≡_`. `OriginalWilsonToBishopScalarWeld` still lacks an inhabitant. Its subtraction-zero transport was corrected to use native subtraction congruence.
2. **SU(N) trace:** the finite-matrix proof sketched in the attachment needs a *constructed* finite complex inner product, determinant-one and row norm; no `SUNMatrixRealTrace` embedding into that realization is supplied. Existing rational SU(2) path trace bounds do not prove arbitrary N. We now source-write signed Wilson `|N_n(W)|≤Z_n` and `|E_n(W)|≤1` and both true R445 fine-blocked/bare bounds **conditional on the selected trace and scalar laws**, in `YMClayE1D1OriginalSignedWilsonWordMomentBoundExact.agda`. This is real original-Haar transport, not an assumed nonnegative test.
3. **P0.09 propagator:** the formula `U=exp(aξ)V` does not yet define the required original gauge-covariant fiber chart/Jacobian or preserve the original Gibbs density after conditional integration. The co-incident Green-function and `g_0²(a) (a/L)²` estimates are stated, not proved uniform with actual lattice/volume/coupling control. A positive massive propagator may presuppose a scale that D2 is supposed to establish.
4. **D1:** `N(n)≤64^n` and `|ω(X)|≤ε^{|X|}` are separate combinatorial and physical theorems; in particular the latter is not derived from the actual R576 Wilson connected weights. Counting alone yields no clustering.
5. **E1:** pointwise Cauchy convergence of individually selected loop expectations does not automatically provide a **unique probability measure** on all generalized connections without consistent finite-dimensional distributions, positivity, tightness/extension or an appropriate constructive representation theorem. The named Kolmogorov–Prokhorov step is not a sourced, verified theorem in the current original Wilson stack.
6. **D2:** the reflected Gram form and same-limit reflection positivity must be proven and the reconstructed semigroup/H identified. Dense local cylinder vectors by construction do not automatically yield a uniform spectral gap. Common decay exponent on a dense core can suffice via a **separate spectral measure support argument** even with vector-dependent finite prefactors; directly sending norm approximations through the prefactors is invalid.
7. **N1/G1:** positivity of a running coupling does not prove a particular four-point cumulant nonzero without an error-versus-leading-term lower bound and a same-continuum source. `h^∨(G)>0` and compact Haar existence do not establish original group-indexed nonperturbative RG or continuum mass gap.

These distinctions are reflected in the executable roadmap. **All five Clay terminal gates E1/D1/D2/N1/G1 OPEN.** No new Agda kernel acceptance receipt or UV-uniform physical polymer estimate exists in this round.


## 2026-11-12 attachment-specific result: real SU(N) Haar fiber identity, without fictitious UV closure

The user's latest attached `Pasted text.txt` proposes `U_e=exp(a ξ_e)V_e`, an exponential Jacobian, a positive `K_V=D_V^*D_V+a²m_eff²`, and an already-decaying resolvent. Those formulas **are not yet a rigorously proved global disintegration** of the original Wilson side-four finite Haar weight; in particular the group exponential is not generally a globally injective coordinate chart, gauge-fixed zero modes and Jacobians are not identified on the selected original bond codec, and a positive `m_eff` cannot be freely introduced in a mass-gap argument.

There is, however, a genuine **source-first alternative for a single native two-link SU(N) multiplication block**:

- `YMClaySUNOneLinkHaarConvolutionSourceExact.agda`: proves from actual existing `OneLinkProductHaar`, bilateral invariance and Fubini that product of two independent Haar links pushes forward to the selected one-link Haar measure for **every** integrable original link test.
- `YMClaySUNTwoLinkHaarEffectiveFiberDensityExact.agda`: constructs the weighted coarse density `ρ_g(W)=∫_U g(U,U⁻¹W)` for *arbitrary* correlated fine two-link density `g`; the native SU(N) group inverse cancellation and Haar left-invariance yield `∫_U∫_V g(U,V)F(UV)=∫_W ρ_g(W)F(W)`. The same module derives source partition transport, pointwise positivity of `ρ_g` from original positive `g`, and exact unit-density reduction to pure Haar for all tests.
- `scripts/check_ym_two_link_haar_fiber_exact.py` independently passed 512 exact rational instances on noncommutative D4 with correlated densities and signed observables; D4 is **not SU(N)** and this is not a kernel receipt.
- The module imports are in the original Wilson physical regression and the local Nix/Agda target list.

**Actual remaining high-alpha P0.09 proof:** the full original side-four `YMClaySUNNativeBlockedPositiveHolonomyExact.nativeSUNBlockLinks` is a map from 1024 original fine positive bonds to 64 original coarse positive bonds, not a single two-link group multiplication on one coordinate. A legal global disintegration needs a real source bond-coordinate decomposition matching all coarse blocked holonomies to disjoint oriented fine-link product pairs and integrating out the residual interior links, with explicit original Gibbs density `Variable.periodicSUNGibbsDensity`, gauge covariance and Fubini. Only after its exact full-block `ρ_eff` is constructed can `ρ_eff - ρ_bare` be estimated by source-controlled polymer weights in the correct ultraviolet scaling regime. The local Haar identity is a useful finite proof subleaf; it does **not** deliver the physical uniform bound, mass gap, or E1/D1/D2/N1/G1 terminal Clay closure.

**D2 logical defect in the supplied text:** its spectral argument excludes a hypothetical *eigenvector* with energy `λ_0<m` but does not cover continuous subgap spectral support. Also an approximant `Ψ_δ` changes with `δ`; its correlation bound's constant `M(Ψ_δ)` is uncontrolled in that passage to `t→∞`. A valid operator gap proof requires the same self-adjoint H, OS core density, and a spectral-measure support lemma uniformly in the decay exponent, not only an eigenvalue contradiction.
