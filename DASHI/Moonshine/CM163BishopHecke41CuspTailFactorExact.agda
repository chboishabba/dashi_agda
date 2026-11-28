module DASHI.Moonshine.CM163BishopHecke41CuspTailFactorExact where

-- SOURCE-WRITTEN, kernel pending. Removing a finite zero prefix
-- gives an absolutely convergent shifted coefficient series at any
-- nonzero t. Division uses only the actual nonzero phase, never j or
-- a branch difference. A uniform cusp bound is a separate theorem.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _+_; _-_; _*_; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as Ring
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowClosureExact as Close
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Const
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as Power
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.JInvariantBishopRamanujanComplexReadoutExact as Read
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41SparseRingExact as Sparse
import DASHI.Moonshine.CM163BishopHecke41LiteralNormalizedCoefficientsExact as Coeff
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; powC)
open N using (SeriesC; _≈cs_; _⊗c_; twist)
open Comp using (complexTrans; complexSym)

drop : ∀ {X : Set} → Nat → (Nat → X) → Nat → X
drop zero f n = f n
drop (suc k) f = drop k (λ n → f (suc n))

pad : Nat → SeriesC → SeriesC
pad zero f n = f n
pad (suc k) f zero = A.zeroC
pad (suc k) f (suc n) = pad k f n

headZero : ∀ f k → (∀ n → n ≤ k → f n ≈C A.zeroC) → f ≈cs pad (suc k) (drop (suc k) f)
headZero f zero h zero = h zero z≤n
headZero f zero h (suc n) = C.≈C-refl _
headZero f (suc k) h zero = h zero z≤n
headZero f (suc k) h (suc n) =
  headZero (λ n → f (suc n)) k (λ j hj → h (suc j) (s≤s hj)) n

prefixDrop : ∀ f n → Seq.SeriesOf f (suc n) ≃ (f zero + Seq.SeriesOf (λ k → f (suc k)) n)
prefixDrop f zero = P.≃-trans (P.+-identityˡ (f zero)) (P.≃-symm (P.+-identityʳ (f zero)))
prefixDrop f (suc n) = P.≃-trans (P.+-cong (prefixDrop f n) P.≃-refl)
  (P.+-assoc (f zero) (Seq.SeriesOf (λ k → f (suc k)) n) (f (suc n)))

dropOneConv : ∀ f v → Seq._ConvergesTo_ (Seq.SeriesOf f) v →
  Seq._ConvergesTo_ (Seq.SeriesOf (λ n → f (suc n))) (v - f zero)
dropOneConv f v cv = Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
  (λ {(suc n) → P.≃-trans
    (P.+-cong (prefixDrop f (suc n)) P.≃-refl)
    (let open P.ℝ-Solver in solve 2 (λ a b → (a ⊕ b) ⊖ a ⊜ b)
      P.≃-refl (f zero) (Seq.SeriesOf (λ k → f (suc k)) (suc n)))})
  (_ , Conv.subR (Close.shiftReal cv) (constantReal (f zero)))
  where
  constantReal : ∀ a → Seq._ConvergesTo_ (λ _ → a) a
  constantReal a = Const.constantConverges a

dropAbs : ∀ f k → Seq.SeriesOf_ConvergesAbsolutely f →
  Seq.SeriesOf_ConvergesAbsolutely (drop k f)
dropAbs f zero ab = ab
dropAbs f (suc k) ab = dropAbs (λ n → f (suc n)) k
  (_ , dropOneConv (λ n → ∣ f n ∣) (proj₁ ab) (proj₂ ab))

dropComplexAbs : ∀ f k → C.ComponentwiseAbsoluteSeriesConvergent f →
  C.ComponentwiseAbsoluteSeriesConvergent (drop k f)
dropComplexAbs f zero ab = ab
dropComplexAbs f (suc k) ab = dropComplexAbs (λ n → f (suc n)) k
  (C.componentwise-absolute-series-convergent
    (dropAbs (C.realTerms f) 1 (C.realAbsolute ab))
    (dropAbs (C.imagTerms f) 1 (C.imagAbsolute ab)))

scalePrefix : ∀ a f n → Seq.SeriesOf (λ k → a * f k) n ≃ a * Seq.SeriesOf f n
scalePrefix a f zero = P.≃-symm (P.*-zeroʳ a)
scalePrefix a f (suc n) = P.≃-trans (P.+-cong (scalePrefix a f n) P.≃-refl)
  (P.≃-symm (P.*-distribˡ-+ a (Seq.SeriesOf f n) (f n)))

scaleAbs : ∀ a f → Seq.SeriesOf_ConvergesAbsolutely f →
  Seq.SeriesOf_ConvergesAbsolutely (λ k → a * f k)
scaleAbs a f ab =
  let c = ∣ a ∣
      g = λ n → ∣ f n ∣
      cv = Conv.mulR (Const.constantConverges c) (proj₂ ab)
      scaled = Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
        (λ {(suc n) → P.≃-symm (scalePrefix c g (suc n))}) (_ , cv)
      eq : ∀ n → c * g n ≃ ∣ a * f n ∣
      eq n = P.≃-symm (P.∣x*y∣≃∣x∣*∣y∣ a (f n))
      prefixCong : ∀ n → Seq.SeriesOf (λ k → c * g k) n ≃ Seq.SeriesOf (λ k → ∣ a * f k ∣) n
      prefixCong zero = P.≃-refl
      prefixCong (suc n) = P.+-cong (prefixCong n) (eq n)
  in _ , Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) → prefixCong (suc n)}) (_ , scaled)

mulAbs : ∀ a f → C.ComponentwiseAbsoluteSeriesConvergent f →
  C.ComponentwiseAbsoluteSeriesConvergent (λ n → a *C f n)
mulAbs a f ab = C.componentwise-absolute-series-convergent
  (CP.minusAbs _ _ (scaleAbs (C.re a) (C.realTerms f) (C.realAbsolute ab))
    (scaleAbs (C.im a) (C.imagTerms f) (C.imagAbsolute ab)))
  (CP.plusAbs _ _ (scaleAbs (C.re a) (C.imagTerms f) (C.imagAbsolute ab))
    (scaleAbs (C.im a) (C.realTerms f) (C.realAbsolute ab)))

-- Drop a coefficient and its geometric degree together. The original
-- t^k factor is reconstructed at every index, not only at the limit.
dropStep : ∀ {X : Set} (f : Nat → X) k n →
  drop k (λ j → f (suc j)) n ≡ drop k f (suc n)
dropStep f zero n = refl
dropStep f (suc k) n = dropStep (λ j → f (suc j)) k n

dropTwist : ∀ t f k n → drop k (twist t f) n ≈C (powC t k *C twist t (drop k f) n)
dropTwist t f zero n = complexSym (L.complexMultiplyLeftIdentity _)
dropTwist t f (suc k) n rewrite dropStep (twist t f) k n | dropStep f k n =
  complexTrans (dropTwist t f k (suc n))
    (complexTrans (A.mulCCongruent (C.≈C-refl _)
      (complexTrans (complexSym (L.complexMultiplyAssociative (drop k f (suc n)) t (powC t n)))
        (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative _ t) (C.≈C-refl _))
          (L.complexMultiplyAssociative t _ _))))
      (complexTrans (complexSym (L.complexMultiplyAssociative (powC t k) t _))
        (A.mulCCongruent (L.complexMultiplyCommutative _ t) (C.≈C-refl _))))

unscale : ∀ t (nz : Rec.BishopComplexNonzero t) z →
  (Rec.reciprocalC t nz *C (t *C z)) ≈C z
unscale t nz z = complexTrans (complexSym (L.complexMultiplyAssociative _ t z))
  (complexTrans (A.mulCCongruent
    (complexTrans (L.complexMultiplyCommutative _ t) (Rec.multiplyReciprocal t nz)) (C.≈C-refl _))
    (L.complexMultiplyLeftIdentity z))

tailRead : ∀ {t f} → Rec.BishopComplexNonzero t → (k : Nat) →
  Eval.Eval t f → Eval.Eval t (drop k f)
tailRead {t} {f} nz k ev =
  let w = powC t k
      wnz = J.nonzeroPower nz k
      v = Rec.reciprocalC w wnz
      ab = dropComplexAbs (twist t f) k (Eval.absolute ev)
      read : ∀ n → (v *C drop k (twist t f) n) ≈C twist t (drop k f) n
      read n = complexTrans (A.mulCCongruent (C.≈C-refl _) (dropTwist t f k n))
        (unscale w wnz _)
      abs = CP.complexAbsTransport read (mulAbs v _ ab)
  in record { value = C.complexSeriesLimit (twist t (drop k f)) abs
    ; absolute = abs ; converges = C.complexSeriesLimitConvergence _ abs }

monoPad : ∀ k f → (E.lift (Sparse.mono k) ⊗c f) ≈cs pad k f
monoPad k f n =
  let a = C.realTerms f; b = C.imagTerms f
      reRead = P.≃-trans (P.+-cong (Sparse.monoMul k a n) (P.-‿cong (Ring.rowZeroLeft b n)))
        (let open P.ℝ-Solver in solve 1 (λ x → x ⊖ Κ 0ℚᵘ ⊜ x) P.≃-refl (Coeff.delay k a n))
      imRead = P.≃-trans (P.+-cong (Sparse.monoMul k b n) (Ring.rowZeroLeft a n))
        (P.+-identityʳ _)
  in P.≃-trans reRead (padReal k f n) , P.≃-trans imRead (padImag k f n)
  where
  padReal : ∀ k f n → Coeff.delay k (C.realTerms f) n ≃ C.re (pad k f n)
  padReal zero f n = P.≃-refl
  padReal (suc k) f zero = P.≃-refl
  padReal (suc k) f (suc n) = padReal k f n
  padImag : ∀ k f n → Coeff.delay k (C.imagTerms f) n ≃ C.im (pad k f n)
  padImag zero f n = P.≃-refl
  padImag (suc k) f zero = P.≃-refl
  padImag (suc k) f (suc n) = padImag k f n

sameEval : ∀ {t f} (a b : Eval.Eval t f) → Eval.value a ≈C Eval.value b
sameEval a b = Seq.uniqueness-of-limits (C.realConverges (Eval.converges a)) (C.realConverges (Eval.converges b)) ,
  Seq.uniqueness-of-limits (C.imagConverges (Eval.converges a)) (C.imagConverges (Eval.converges b))

factor : ∀ {t f} (nz : Rec.BishopComplexNonzero t) k (ev : Eval.Eval t f) →
  (∀ n → n ≤ k → f n ≈C A.zeroC) →
  Eval.value ev ≈C (powC t (suc k) *C Eval.value (tailRead nz (suc k) ev))
factor {t} {f} nz k ev hz =
  let a = tailRead nz (suc k) ev
      b = Eval.product (Eval.fromReal (Eval.monoRead t (suc k))) a
      read = Eval.transport (N.transCs (monoPad (suc k) (drop (suc k) f))
        (N.symCs (headZero f k hz))) b
  in complexTrans (sameEval ev read)
    (A.mulCCongruent (Eval.monoValue t (suc k)) (C.≈C-refl _))
