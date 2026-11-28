module DASHI.Moonshine.JInvariantBishopRamanujanComplexReadoutExact where

-- SOURCE-WRITTEN, kernel pending. Generalize the original integer
-- theta weighted row to the original real coefficient ring. No new
-- convergence axiom or analytic identity theorem.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin; toℕ)
import Data.Fin.Properties as FP
import Data.Nat.Base as Nat
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Relation.Binary.PropositionalEquality using (cong)
import Real as R
open R using (ℝ; _≃_; _+_; _-_; _*_)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopSignTwistedFiniteCauchyCoefficientExact as Twist
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as Ring
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.JInvariantBishopThetaSignedReadoutExact as Sp
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as L
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowClosureExact as Close
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.JInvariantBishopDiskSetoidTransportExact as Same
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open G using (Series; _≈s_; _⊗s_; _⊖s_; scale)
open C using (BishopComplex; _≈C_)
open A using (_*C_; _+C_; _-C_; scaleC; powC)
open Comp using (complexTrans; complexSym)

weight : BishopComplex → Series → Nat → BishopComplex
weight q f n = scaleC (f n) (powC q n)

weightCong : ∀ q {f g} → f ≈s g → ∀ n → weight q f n ≈C weight q g n
weightCong q h n = P.*-congʳ (h n) , P.*-congʳ (h n)

weightedSummand : ∀ q f g n (i : Fin (suc n)) →
  (weight q f (toℕ i) *C weight q g (n Nat.∸ toℕ i)) ≈C
    scaleC (f (toℕ i) * g (n Nat.∸ toℕ i)) (powC q n)
weightedSummand q f g n i =
  let k = toℕ i; j = n Nat.∸ k
  in complexTrans (CP.scaleProduct (f k) (g j) (powC q k) (powC q j))
    (A.scaleCCongruent (complexTrans (L.powAdd q k j)
      (P.≃-refl₂ (cong (λ x → C.re (powC q x)) (Twist.indexPlusTruncatedComplement n k (FP.toℕ≤pred[n] i))) ,
       P.≃-refl₂ (cong (λ x → C.im (powC q x)) (Twist.indexPlusTruncatedComplement n k (FP.toℕ≤pred[n] i)))))
      (f k * g j))

weightedRow : ∀ q f g n → CP.complexRow (weight q f) (weight q g) n ≈C weight q (f ⊗s g) n
weightedRow q f g n =
  let a = C.realTerms (weight q f); b = C.imagTerms (weight q f)
      c = C.realTerms (weight q g); d = C.imagTerms (weight q g)
      j = λ (i : Fin (suc n)) → n Nat.∸ toℕ i
      k = λ (i : Fin (suc n)) → f (toℕ i) * g (j i)
      x = C.re (powC q n); y = C.im (powC q n)
      collapse : ∀ u → Row.BishopSum.sum (λ i → k i * u) ≃ ((f ⊗s g) n * u)
      collapse u = P.≃-trans
        (Row.BishopSum.sum-cong-≋ (λ i → P.*-comm (k i) u))
        (P.≃-trans (P.≃-symm (Row.BishopSum.*-distribˡ-sum u k))
          (P.*-comm u (Row.BishopSum.sum k)))
  in P.≃-trans (P.≃-symm (CP.sumSub (suc n) (λ i → a (toℕ i) * c (j i)) (λ i → b (toℕ i) * d (j i))))
      (P.≃-trans (Row.BishopSum.sum-cong-≋ (λ i → proj₁ (weightedSummand q f g n i))) (collapse x)) ,
     P.≃-trans (P.≃-symm (Row.BishopSum.∑-distrib-+ (λ i → a (toℕ i) * d (j i)) (λ i → b (toℕ i) * c (j i))))
      (P.≃-trans (Row.BishopSum.sum-cong-≋ (λ i → proj₂ (weightedSummand q f g n i))) (collapse y))

record Readout (q : BishopComplex) (f : Series) : Set where
  field
    value : BishopComplex
    absolute : C.ComponentwiseAbsoluteSeriesConvergent (weight q f)
    converges : C.ComplexSeriesConvergesTo (weight q f) value
open Readout public

fromAbsolute : ∀ {q f} → C.ComponentwiseAbsoluteSeriesConvergent (weight q f) → Readout q f
fromAbsolute {q} {f} h = record
  { value = C.complexSeriesLimit (weight q f) h
  ; absolute = h
  ; converges = C.complexSeriesLimitConvergence (weight q f) h }

transport : ∀ {q f g} → f ≈s g → Readout q f → Readout q g
transport {q} h x = record
  { value = value x
  ; absolute = CP.complexAbsTransport (weightCong q h) (absolute x)
  ; converges = CP.complexLimitTransport (weightCong q h) (converges x) }

same : ∀ {q f} (a b : Readout q f) → value a ≈C value b
same {q} {f} a b = Same.sameSeries (weight q f) (weight q f) (value a) (value b)
  (λ _ → C.≈C-refl _) (converges a) (converges b)

product : ∀ {q f g} → Readout q f → Readout q g → Readout q (f ⊗s g)
product {q} {f} {g} a b = record
  { value = value a *C value b
  ; absolute = CP.complexAbsTransport (weightedRow q f g)
      (CP.productAbsolute _ _ (absolute a) (absolute b))
  ; converges = CP.complexLimitTransport (weightedRow q f g)
      (CP.productLimit _ _ _ _ (absolute a) (absolute b) (converges a) (converges b)) }

subWeight : ∀ q f g n → (weight q f n -C weight q g n) ≈C weight q (f ⊖s g) n
subWeight q f g n =
  (let open P.ℝ-Solver in solve 3 (λ a b x → a ⊗ x ⊖ b ⊗ x ⊜ (a ⊖ b) ⊗ x)
    P.≃-refl (f n) (g n) (C.re (powC q n))) ,
  (let open P.ℝ-Solver in solve 3 (λ a b x → a ⊗ x ⊖ b ⊗ x ⊜ (a ⊖ b) ⊗ x)
    P.≃-refl (f n) (g n) (C.im (powC q n)))

subtract : ∀ {q f g} → Readout q f → Readout q g → Readout q (f ⊖s g)
subtract {q} {f} {g} a b =
  let x = weight q f; y = weight q g
      cv = C.complex-series-converges-to
        (CP.minusConv (C.realConverges (converges a)) (C.realConverges (converges b)))
        (CP.minusConv (C.imagConverges (converges a)) (C.imagConverges (converges b)))
      ab = C.componentwise-absolute-series-convergent
        (CP.minusAbs (C.realTerms x) (C.realTerms y) (C.realAbsolute (absolute a)) (C.realAbsolute (absolute b)))
        (CP.minusAbs (C.imagTerms x) (C.imagTerms y) (C.imagAbsolute (absolute a)) (C.imagAbsolute (absolute b)))
  in record { value = value a -C value b
            ; absolute = CP.complexAbsTransport (subWeight q f g) ab
            ; converges = CP.complexLimitTransport (subWeight q f g) cv }

prepend : ∀ {X : Set} → X → (Nat → X) → Nat → X
prepend a f zero = a
prepend a f (suc n) = f n

prependPrefix : ∀ a f n → Seq.SeriesOf (prepend a f) (suc n) ≃ (a + Seq.SeriesOf f n)
prependPrefix a f zero = P.≃-trans (P.+-identityˡ a) (P.≃-symm (P.+-identityʳ a))
prependPrefix a f (suc n) = P.≃-trans (P.+-cong (prependPrefix a f n) P.≃-refl)
  (P.+-assoc a (Seq.SeriesOf f n) (f n))

prependConv : ∀ a f v → Seq._ConvergesTo_ (Seq.SeriesOf f) v →
  Seq._ConvergesTo_ (Seq.SeriesOf (prepend a f)) (a + v)
prependConv a f v cv = Close.unshiftReal
  (Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) → P.≃-symm (prependPrefix a f (suc n))})
    (_ , Conv.addR (Power.constantConverges a) cv))

prependAbs : ∀ a f → Seq.SeriesOf_ConvergesAbsolutely f →
  Seq.SeriesOf_ConvergesAbsolutely (prepend a f)
prependAbs a f h = _ , prependConv R.∣ a ∣ (λ n → R.∣ f n ∣) (Seq.lim h) (proj₂ h)

prependComplex : ∀ a f v → C.ComponentwiseAbsoluteSeriesConvergent f →
  C.ComplexSeriesConvergesTo f v →
  C.ComponentwiseAbsoluteSeriesConvergent (prepend a f) →
  C.ComplexSeriesConvergesTo (prepend a f) (a +C v)
prependComplex a f v h cv ha = C.complex-series-converges-to
  (prependConv (C.re a) (C.realTerms f) (C.re v) (C.realConverges cv))
  (prependConv (C.im a) (C.imagTerms f) (C.im v) (C.imagConverges cv))

zeroConv : Seq._ConvergesTo_ (Seq.SeriesOf (λ _ → R.0ℝ)) R.0ℝ
zeroConv = proj₂ Sp.zeroConvergent

zeroAbs : Seq.SeriesOf_ConvergesAbsolutely (λ _ → R.0ℝ)
zeroAbs = CP.absTransport (λ _ → P.≃-refl)
  (Seq.proposition-3-5 Sp.zeroConvergent
    (zero , λ _ _ → P.≤-reflexive (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ R.0ℝ))))

-- A degree-zero scalar is evaluated on the literal coefficient spike.
constantRead : ∀ q a → Readout q (G.constant a)
constantRead q a =
  let head = C.complex a R.0ℝ
      f = prepend head (λ _ → A.zeroC)
      h : ∀ n → f n ≈C weight q (G.constant a) n
      h zero = complexSym ((P.*-identityʳ a) , P.*-zeroʳ a)
      h (suc n) = complexSym (P.*-zeroˡ _ , P.*-zeroˡ _)
      ab = C.componentwise-absolute-series-convergent
        (prependAbs a (λ _ → R.0ℝ) zeroAbs) (prependAbs R.0ℝ (λ _ → R.0ℝ) zeroAbs)
      cv = C.complex-series-converges-to
        (Seq.xₙ→x∧x≃y⇒xₙ→y (prependConv a (λ _ → R.0ℝ) R.0ℝ zeroConv) (P.+-identityʳ a))
        (Seq.xₙ→x∧x≃y⇒xₙ→y (prependConv R.0ℝ (λ _ → R.0ℝ) R.0ℝ zeroConv) (P.+-identityʳ R.0ℝ))
  in record { value = head ; absolute = CP.complexAbsTransport h ab
            ; converges = CP.complexLimitTransport h cv }

monomial : Series
monomial zero = R.0ℝ
monomial (suc zero) = R.1ℝ
monomial (suc (suc n)) = R.0ℝ

monomialRead : ∀ q → Readout q monomial
monomialRead q =
  let f = λ n → C.complex (Sp.spike (C.re q) n) (Sp.spike (C.im q) n)
      h : ∀ n → f n ≈C weight q monomial n
      h zero = complexSym (P.*-zeroˡ _ , P.*-zeroˡ _)
      h (suc zero) = complexSym (complexTrans
        (A.scaleCCongruent (Laws.complexMultiplyRightIdentity q) R.1ℝ)
        (P.*-identityˡ _ , P.*-identityˡ _))
      h (suc (suc n)) = complexSym (P.*-zeroˡ _ , P.*-zeroˡ _)
      ab = C.componentwise-absolute-series-convergent (Sp.spikeAbs (C.re q)) (Sp.spikeAbs (C.im q))
      cv = C.complex-series-converges-to (Sp.spikeConv (C.re q)) (Sp.spikeConv (C.im q))
  in record { value = q ; absolute = CP.complexAbsTransport h ab
            ; converges = CP.complexLimitTransport h cv }
