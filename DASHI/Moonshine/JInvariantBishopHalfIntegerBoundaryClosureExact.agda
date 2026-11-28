module DASHI.Moonshine.JInvariantBishopHalfIntegerBoundaryClosureExact where

-- Source-written, uncompiled. Actual row convergence from above,
-- followed by RH-style uniform boundary passage; no analytic extension
-- at q=-1 or assumed equality to an opaque zeta value.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _+_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowExact as Chart
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowClosureExact as Close
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as LR
import DASHI.Moonshine.JInvariantBishopUniformBoundaryPassageExact as U
import DASHI.Moonshine.JInvariantBishopHalfIntegerBoundaryTermsExact as H
import DASHI.Moonshine.JInvariantBishopHalfIntegerBoundaryFourierExact as F
import DASHI.Moonshine.JInvariantBishopDyadicRowTailMajorantExact as Tail
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as Row
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; scaleC; powC)
open Comp using (complexTrans; complexSym)
open Completion using (original-bishop-pointwise-complex-converges; realConverges; imaginaryConverges)

terms : Nat → Nat → Nat → BishopComplex
terms weight n k = powC (H.w H.plus k (Chart.h n)) weight +C powC (H.w H.minus k (Chart.h n)) weight

axis : Nat → Nat → BishopComplex
axis weight k = powC (H.w H.plus k R.0ℝ) weight +C powC (H.w H.minus k R.0ℝ) weight

partial : (Nat → BishopComplex) → Nat → BishopComplex
partial f K = C.complex (Seq.SeriesOf (λ k → C.re (f k)) K)
  (Seq.SeriesOf (λ k → C.im (f k)) K)

fixed : ∀ weight k → Lim.Conv (λ n → terms weight n k) (axis weight k)
fixed weight k = Lim.addConv (H.powerConv (H.fixed H.plus k) weight)
  (H.powerConv (H.fixed H.minus k) weight)

budget : ℝ → Nat → ℝ
budget c k = c * Basel.baselTerm k + c * Basel.baselTerm k
budgetValue : ℝ → ℝ
budgetValue c = c * Basel.baselLimit + c * Basel.baselLimit

budgetPrefixRead : ∀ c K → Seq.SeriesOf (budget c) K ≃
  (c * Seq.SeriesOf Basel.baselTerm K + c * Seq.SeriesOf Basel.baselTerm K)
budgetPrefixRead c zero = let open P.ℝ-Solver in solve 1
  (λ c → Κ 0ℚᵘ ⊜ c ⊗ Κ 0ℚᵘ ⊕ c ⊗ Κ 0ℚᵘ) P.≃-refl c
budgetPrefixRead c (suc K) = P.≃-trans (P.+-cong (budgetPrefixRead c K) P.≃-refl)
  (let open P.ℝ-Solver in solve 3
    (λ c a b → (c ⊗ a ⊕ c ⊗ a) ⊕ (c ⊗ b ⊕ c ⊗ b)
      ⊜ c ⊗ (a ⊕ b) ⊕ c ⊗ (a ⊕ b)) P.≃-refl c
    (Seq.SeriesOf Basel.baselTerm K) (Basel.baselTerm K))

budgetConv : ∀ c → Seq._ConvergesTo_ (Seq.SeriesOf (budget c)) (budgetValue c)
budgetConv c =
  let cv = Inv.mulR (Power.constantConverges c) (proj₂ Basel.baselSeriesConvergent)
  in Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc K) → P.≃-symm (budgetPrefixRead c (suc K))}) (_ , Inv.addR cv cv)

bound4 : ∀ n k → Tail.Box (terms 4 n k) (budget ((+ 16 / 1) ⋆) k)
bound4 n k = Tail.boxAdd (H.majorant4 H.plus k (Chart.h n)) (H.majorant4 H.minus k (Chart.h n))
bound6 : ∀ n k → Tail.Box (terms 6 n k) (budget ((+ 64 / 1) ⋆) k)
bound6 n k = Tail.boxAdd (H.majorant6 H.plus k (Chart.h n)) (H.majorant6 H.minus k (Chart.h n))

module At (inputs : Round11.BishopCutset) where
  module Fourier = F.At inputs

  undo4 = A.scaleC ((+ 1 / 6) ⋆) (powC LR.factor 4)
  undo6 = A.scaleC ((+ 1 / 120) ⋆) (powC LR.factor 6)
  row4 row6 : Nat → BishopComplex
  row4 n = undo4 *C Fourier.Rows.row4 (H.point n)
  row6 n = undo6 *C Fourier.Rows.row6 (H.point n)

  target4 target6 : BishopComplex
  target4 = undo4 *C Row.P4 F.negativeQuarter
  target6 = undo6 *C Row.P6 F.negativeQuarter

  row4Limit : Lim.Conv row4 target4
  row4Limit = Lim.mulConst undo4 Fourier.F4Conv
  row6Limit : Lim.Conv row6 target6
  row6Limit = Lim.mulConst undo6 Fourier.F6Conv

  module AtHeight (n : Nat) where
    module L = LR.At inputs (H.point n)

    pairRead : ∀ weight k → Close.pair (L.lattice weight) k ≈C terms weight n k
    pairRead weight k = A.addCCongruent
      (A.powCCongruent (H.readPlus n k) weight) (A.powCCongruent (H.readMinus n k) weight)

    prefixRead : ∀ weight K → Close.pairPrefix (L.lattice weight) K ≈C partial (terms weight n) K
    prefixRead weight zero = C.≈C-refl _
    prefixRead weight (suc K) = A.addCCongruent (prefixRead weight K) (pairRead weight K)

    rows4 : Lim.Conv (partial (terms 4 n)) (row4 n)
    rows4 = Lim.convTransport (prefixRead 4) L.latticeRow4
    rows6 : Lim.Conv (partial (terms 6 n)) (row6 n)
    rows6 = Lim.convTransport (prefixRead 6) L.latticeRow6

  module FourRe = U.Passage (λ n k → C.re (terms 4 n k)) (λ k → C.re (axis 4 k))
    (budget ((+ 16 / 1) ⋆)) (λ n → C.re (row4 n)) (C.re target4) (budgetValue ((+ 16 / 1) ⋆))
    (λ k → realConverges (fixed 4 k)) (λ n → realConverges (AtHeight.rows4 n))
    (realConverges row4Limit) (budgetConv ((+ 16 / 1) ⋆)) (λ n k → proj₁ (bound4 n k))
  module FourIm = U.Passage (λ n k → C.im (terms 4 n k)) (λ k → C.im (axis 4 k))
    (budget ((+ 16 / 1) ⋆)) (λ n → C.im (row4 n)) (C.im target4) (budgetValue ((+ 16 / 1) ⋆))
    (λ k → imaginaryConverges (fixed 4 k)) (λ n → imaginaryConverges (AtHeight.rows4 n))
    (imaginaryConverges row4Limit) (budgetConv ((+ 16 / 1) ⋆)) (λ n k → proj₂ (bound4 n k))
  module SixRe = U.Passage (λ n k → C.re (terms 6 n k)) (λ k → C.re (axis 6 k))
    (budget ((+ 64 / 1) ⋆)) (λ n → C.re (row6 n)) (C.re target6) (budgetValue ((+ 64 / 1) ⋆))
    (λ k → realConverges (fixed 6 k)) (λ n → realConverges (AtHeight.rows6 n))
    (realConverges row6Limit) (budgetConv ((+ 64 / 1) ⋆)) (λ n k → proj₁ (bound6 n k))
  module SixIm = U.Passage (λ n k → C.im (terms 6 n k)) (λ k → C.im (axis 6 k))
    (budget ((+ 64 / 1) ⋆)) (λ n → C.im (row6 n)) (C.im target6) (budgetValue ((+ 64 / 1) ⋆))
    (λ k → imaginaryConverges (fixed 6 k)) (λ n → imaginaryConverges (AtHeight.rows6 n))
    (imaginaryConverges row6Limit) (budgetConv ((+ 64 / 1) ⋆)) (λ n k → proj₂ (bound6 n k))

  actualAxis4 : Lim.Conv (partial (axis 4)) target4
  actualAxis4 = original-bishop-pointwise-complex-converges FourRe.boundaryConverges FourIm.boundaryConverges
  actualAxis6 : Lim.Conv (partial (axis 6)) target6
  actualAxis6 = original-bishop-pointwise-complex-converges SixRe.boundaryConverges SixIm.boundaryConverges
