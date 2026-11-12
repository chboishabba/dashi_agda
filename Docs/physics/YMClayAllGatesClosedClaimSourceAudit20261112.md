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
