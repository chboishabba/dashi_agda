module DASHI.Moonshine.CM163BishopHecke41CuspLimitExact where

-- SOURCE-WRITTEN, kernel pending. Actual residual is zero at the
-- cusp in the original Bishop limit sense, whenever the ramified
-- phase tends to zero inside the fixed reference disk. The bound
-- is uniform, not a pointwise inverse estimate.
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _*_; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Const
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.CM163BishopHecke41UniformCuspBoundExact as Bound
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open Completion using (original-bishop-pointwise-complex-converges; realConverges; imaginaryConverges)

absNull : ∀ {f : Nat → ℝ} → Seq._ConvergesTo_ f R.0ℝ →
  Seq._ConvergesTo_ (λ n → ∣ f n ∣) R.0ℝ
absNull cv = Seq.xₙ→x∧x≃y⇒xₙ→y (Seq.∣xₙ∣→∣x₀∣ (R.0ℝ , cv))
  (P.nonNegx⇒∣x∣≃x P.nonNeg0)

size : C.BishopComplex → ℝ
size z = ∣ C.re z ∣ + ∣ C.im z ∣

sizeNull : ∀ {t : Nat → C.BishopComplex} →
  Lim.Conv t A.zeroC → Seq._ConvergesTo_ (λ n → size (t n)) R.0ℝ
sizeNull cv = Seq.xₙ→x∧x≃y⇒xₙ→y
  (Conv.addR (absNull (realConverges cv)) (absNull (imaginaryConverges cv)))
  (P.+-identityʳ R.0ℝ)

scaledNull : ∀ {t : Nat → C.BishopComplex} → Lim.Conv t A.zeroC → ∀ M →
  Seq._ConvergesTo_ (λ n → size (t n) * M) R.0ℝ
scaledNull cv M = Seq.xₙ→x∧x≃y⇒xₙ→y (Conv.mulR (sizeNull cv) (Const.constantConverges M))
  (P.*-zeroˡ M)

sizeNonnegative : ∀ z → R.NonNegative (size z)
sizeNonnegative z = P.nonNegx,y⇒nonNegx+y (P.nonNeg∣x∣ _) (P.nonNeg∣x∣ _)

module At (inputs : Round11.BishopCutset) where
  module B = Bound.At inputs
  module R0 = B.R0

  diagonalZeroAlong : R0.R.W.UnitGate → R0.R.W.DiagonalGate →
    (p : Nat → U.BishopUpperHalfPlanePoint) →
    (∀ n → Norm.normSqC (R0.t (p n)) ≤ Norm.normSqC B.reference) →
    Lim.Conv (λ n → R0.t (p n)) A.zeroC →
    Lim.Conv (λ n → R0.d (p n)) A.zeroC
  diagonalZeroAlong hu hd p inside cv =
    original-bishop-pointwise-complex-converges
      (Lim.dominatedNull (scaledNull cv B.D.M)
        (λ n → P.nonNegx,y⇒nonNegx*y (sizeNonnegative (R0.t (p n))) B.D.Mnonnegative)
        (λ n → proj₁ (B.diagonalBound hu hd (p n) (inside n))))
      (Lim.dominatedNull (scaledNull cv B.D.M)
        (λ n → P.nonNegx,y⇒nonNegx*y (sizeNonnegative (R0.t (p n))) B.D.Mnonnegative)
        (λ n → proj₂ (B.diagonalBound hu hd (p n) (inside n))))

  sliceZeroAlong : R0.R.W.UnitGate → R0.R.W.SliceGate →
    (p : Nat → U.BishopUpperHalfPlanePoint) →
    (∀ n → Norm.normSqC (R0.t (p n)) ≤ Norm.normSqC B.reference) →
    Lim.Conv (λ n → R0.t (p n)) A.zeroC →
    Lim.Conv (λ n → R0.s (p n)) A.zeroC
  sliceZeroAlong hu hs p inside cv =
    original-bishop-pointwise-complex-converges
      (Lim.dominatedNull (scaledNull cv B.S.M)
        (λ n → P.nonNegx,y⇒nonNegx*y (sizeNonnegative (R0.t (p n))) B.S.Mnonnegative)
        (λ n → proj₁ (B.sliceBound hu hs (p n) (inside n))))
      (Lim.dominatedNull (scaledNull cv B.S.M)
        (λ n → P.nonNegx,y⇒nonNegx*y (sizeNonnegative (R0.t (p n))) B.S.Mnonnegative)
        (λ n → proj₂ (B.sliceBound hu hs (p n) (inside n))))
