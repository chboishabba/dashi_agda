module DASHI.Moonshine.CM163BishopHecke41UniformSeriesContinuityExact where

-- SOURCE-WRITTEN, kernel pending. Generalize the existing Basel
-- uniform-tail transport to any summable actual component budget.
-- This pays uniform approximation and sequential continuity on
-- the same fixed reference disk, including the origin.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base as Nat using (_≤_; NonZero)
import Data.Nat.Properties as NP
open import Data.Product.Base using (_,_; proj₁; proj₂; Σ; _×_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _-_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopUniformLimitSequentialContinuityExact as Uniform
import DASHI.Analysis.BishopDirichletUniformBaselTailsExact as Basel
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Const
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.CM163BishopHecke41UniformCuspBoundExact as Bound
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
open Completion using (original-bishop-pointwise-complex-converges; realConverges; imaginaryConverges)
open C using (BishopComplex)
open A using (_+C_; _*C_; powC)

module Budget (b : Nat → ℝ) (bConv : Seq._isConvergent (Seq.SeriesOf b)) where

  cutoff : (k : Nat) → .{{_ : NonZero k}} → Nat
  cutoff k = suc (proj₁ (Seq.cauchyConvergenceTest-if b bConv k))

  orderedTail : ∀ f → (∀ n → R._≤_ (∣ f n ∣) (b n)) →
    (k : Nat) → .{{_ : NonZero k}} → ∀ m n →
    m ≤ n → cutoff k ≤ m → cutoff k ≤ n →
    R._≤_ (∣ Seq.∑ f m n ∣) ((+ 1 / k) ⋆)
  orderedTail f h k m n mn hm hn =
    P.≤-trans (Seq.∑-triangle-inequality f m n mn)
      (P.≤-trans (Seq.∑-mono-≤ h m n mn)
        (P.≤-trans P.x≤∣x∣
          (proj₂ (Seq.cauchyConvergenceTest-if b bConv k) m n hm hn)))

  -- Choose the subsequence starting at the cutoff. This avoids a
  -- reversed-tail branch and transports the bound to the actual limit.
  limitErrorAfter : ∀ f v → (∀ n → R._≤_ (∣ f n ∣) (b n)) →
    Seq._ConvergesTo_ (Seq.SeriesOf f) v →
    (k : Nat) → .{{_ : NonZero k}} →
    (m : Nat) → cutoff k ≤ m →
    R._≤_ (∣ v - Seq.SeriesOf f m ∣) ((+ 1 / k) ⋆)
  limitErrorAfter f v h cv k m hm =
    let partial = Seq.SeriesOf f
        shifted n = partial (n + m)
        shiftedCv : Seq._ConvergesTo_ shifted v
        shiftedCv = Seq.xₙ⊆yₙ∧yₙ→y
          (Seq.subseq* ((λ n → n + m) , (λ n → P.≃-refl) , (λ n → NP.n<1+n (n + m))))
          (v , cv)
        dc = Conv.subR shiftedCv (Const.constantConverges (partial m))
        ac = Seq.∣xₙ∣→∣x₀∣ (v - partial m , dc)
        each : ∀ n → R._≤_ (∣ shifted n - partial m ∣) ((+ 1 / k) ⋆)
        each n = P.≤-respˡ-≃ (P.≃-symm (P.∣-∣-cong (Basel.partialMinusIsFiniteTail f m (n + m))))
          (orderedTail f h k m (n + m) (NP.m≤n+m m n) hm (NP.≤-trans hm (NP.m≤n+m m n)))
    in Seq.xₙ≤y⇒limxₙ≤y each (_ , ac)

  limitError : ∀ f v → (∀ n → R._≤_ (∣ f n ∣) (b n)) →
    Seq._ConvergesTo_ (Seq.SeriesOf f) v →
    (k : Nat) → .{{_ : NonZero k}} →
    R._≤_ (∣ v - Seq.SeriesOf f (cutoff k) ∣) ((+ 1 / k) ⋆)
  limitError f v h cv k = limitErrorAfter f v h cv k (cutoff k) NP.≤-refl

-- Sequence-indexed version of the existing real three-leg theorem.
-- Works on a dependent disk membership witness without pretending
-- the function is defined outside the disk.
sequenceUniform : ∀ (f : Nat → ℝ) v (a : Nat → Nat → ℝ) (c : Nat → ℝ) →
  (∀ m → Seq._ConvergesTo_ (a m) (c m)) →
  ((k : Nat) → .{{_ : NonZero k}} → Σ Nat (λ m →
    (∀ n → R._≤_ (∣ f n - a m n ∣) ((+ 1 / k) ⋆)) ×
    R._≤_ (∣ v - c m ∣) ((+ 1 / k) ⋆))) →
  Seq._ConvergesTo_ f v
sequenceUniform f v a c finite uniform = Seq.con* λ { (suc k0) →
  let k = suc k0
      fine = 2 * (2 * k)
      receipt = uniform fine
      m = proj₁ receipt
      mid = Seq.convergence-getter (c m , finite m) (2 * k)
      q = (+ 1 / fine) ⋆
      h = (+ 1 / (2 * k)) ⋆
  in proj₁ mid , λ { (suc n) past →
    P.≤-trans (Uniform.threeLegTriangle (f (suc n)) (a m (suc n)) (c m) v)
      (P.≤-respʳ-≃
        (P.≃-trans
          (let open P.ℝ-Solver in solve 2 (λ q h → q ⊕ (h ⊕ q) ⊜ (q ⊕ q) ⊕ h) P.≃-refl q h)
          (P.≃-trans (P.+-cong (Uniform.halfPlusHalf (2 * k)) P.≃-refl)
            (Uniform.halfPlusHalf k)))
        (P.+-mono-≤ (proj₁ (proj₂ receipt) (suc n))
          (P.+-mono-≤ (proj₂ mid (suc n) past)
            (P.≤-respˡ-≃ (P.∣x-y∣≃∣y-x∣ v (c m)) (proj₂ (proj₂ receipt)))))) } }

powContinuous : ∀ {t : Nat → BishopComplex} {z} → Lim.Conv t z → ∀ n →
  Lim.Conv (λ k → powC (t k) n) (powC z n)
powContinuous cv zero = Lim.constantC A.oneC
powContinuous cv (suc n) = Conv.mulConv cv (powContinuous cv n)

complexPrefix : (Nat → BishopComplex) → Nat → BishopComplex
complexPrefix f n = C.complex (Seq.SeriesOf (C.realTerms f) n) (Seq.SeriesOf (C.imagTerms f) n)

prefixContinuous : ∀ (f : N.SeriesC) {t : Nat → BishopComplex} {z} →
  Lim.Conv t z → ∀ m → Lim.Conv
    (λ k → complexPrefix (N.twist (t k) f) m) (complexPrefix (N.twist z f) m)
prefixContinuous f cv zero = Lim.constantC A.zeroC
prefixContinuous f cv (suc m) = Lim.addConv (prefixContinuous f cv m)
  (Conv.mulConv (Lim.constantC (f m)) (powContinuous cv m))

module Disk (r : BishopComplex) (nz : Rec.BishopComplexNonzero r)
  (f : N.SeriesC) (reference : Eval.Eval r f) where

  module D = Bound.Disk r nz f reference
  module B = Budget D.budget D.budgetConvergent
  Inside : BishopComplex → Set
  Inside t = R._≤_ (Norm.normSqC t) (Norm.normSqC r)

  -- Same finite cutoff controls both coordinates for ALL actual
  -- evaluations, even with distinct proof-relevant convergence data.
  realError : ∀ t → Inside t → (ev : Eval.Eval t f) →
    (k : Nat) → .{{_ : NonZero k}} →
    R._≤_ (∣ C.re (Eval.value ev) - C.re (complexPrefix (N.twist t f) (B.cutoff k)) ∣)
      ((+ 1 / k) ⋆)
  realError t h ev = B.limitError (C.realTerms (N.twist t f)) (C.re (Eval.value ev))
    (λ n → proj₁ (D.termBound t h n)) (C.realConverges (Eval.converges ev))

  imagError : ∀ t → Inside t → (ev : Eval.Eval t f) →
    (k : Nat) → .{{_ : NonZero k}} →
    R._≤_ (∣ C.im (Eval.value ev) - C.im (complexPrefix (N.twist t f) (B.cutoff k)) ∣)
      ((+ 1 / k) ⋆)
  imagError t h ev = B.limitError (C.imagTerms (N.twist t f)) (C.im (Eval.value ev))
    (λ n → proj₂ (D.termBound t h n)) (C.imagConverges (Eval.converges ev))

  continuous : ∀ (t : Nat → BishopComplex) z →
    (∀ n → Inside (t n)) → Inside z → Lim.Conv t z →
    (ev : ∀ n → Eval.Eval (t n) f) → (ez : Eval.Eval z f) →
    Lim.Conv (λ n → Eval.value (ev n)) (Eval.value ez)
  continuous t z inside hz cv ev ez = original-bishop-pointwise-complex-converges
    (sequenceUniform (λ n → C.re (Eval.value (ev n))) (C.re (Eval.value ez))
      (λ m n → C.re (complexPrefix (N.twist (t n) f) m))
      (λ m → C.re (complexPrefix (N.twist z f) m))
      (λ m → realConverges (prefixContinuous f cv m))
      (λ k → B.cutoff k , (λ n → realError (t n) (inside n) (ev n) k) , realError z hz ez k))
    (sequenceUniform (λ n → C.im (Eval.value (ev n))) (C.im (Eval.value ez))
      (λ m n → C.im (complexPrefix (N.twist (t n) f) m))
      (λ m → C.im (complexPrefix (N.twist z f) m))
      (λ m → imaginaryConverges (prefixContinuous f cv m))
      (λ k → B.cutoff k , (λ n → imagError (t n) (inside n) (ev n) k) , imagError z hz ez k))
