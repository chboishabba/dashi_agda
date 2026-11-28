module DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact where

-- Source-written, kernel pending. Lift the existing absolute scalar
-- Cauchy product to the actual complex coefficient streams, using the
-- four Cartesian products (no independent complex completeness axiom).
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
import Data.Fin.Properties as FP
import Data.Nat.Base as N
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ)
open import Relation.Binary.PropositionalEquality using (cong)
import Real as R
open R using (ℝ; _≃_; _+_; _-_; _*_; ∣_∣)
import RealProperties as P
import Sequence as S
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopAbsoluteCauchyProductSpecializationExact as Abs
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopSignTwistedFiniteCauchyCoefficientExact as T
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Moonshine.JInvariantBishopCenteredDyadicLatticeReadoutExact as L
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_*C_; scaleC; powC)
open Comp using (complexTrans; complexSym)

Terms = Nat → ℝ
CTerms = Nat → BishopComplex

plusPrefix : ∀ (f g : Terms) n →
  S.SeriesOf (λ k → f k + g k) n ≃ (S.SeriesOf f n + S.SeriesOf g n)
plusPrefix f g zero = P.≃-symm (P.+-identityʳ R.0ℝ)
plusPrefix f g (suc n) =
  P.≃-trans (P.+-cong (plusPrefix f g n) P.≃-refl)
    (let open P.ℝ-Solver in solve 4
      (λ a b c d → (a ⊕ b) ⊕ (c ⊕ d) ⊜ (a ⊕ c) ⊕ (b ⊕ d))
      P.≃-refl (S.SeriesOf f n) (S.SeriesOf g n) (f n) (g n))

minusPrefix : ∀ (f g : Terms) n →
  S.SeriesOf (λ k → f k - g k) n ≃ (S.SeriesOf f n - S.SeriesOf g n)
minusPrefix f g zero = P.≃-symm (P.+-inverseʳ R.0ℝ)
minusPrefix f g (suc n) =
  P.≃-trans (P.+-cong (minusPrefix f g n) P.≃-refl)
    (let open P.ℝ-Solver in solve 4
      (λ a b c d → (a ⊖ b) ⊕ (c ⊖ d) ⊜ (a ⊕ c) ⊖ (b ⊕ d))
      P.≃-refl (S.SeriesOf f n) (S.SeriesOf g n) (f n) (g n))

plusConv : ∀ {f g : Terms} {x y} →
  S._ConvergesTo_ (S.SeriesOf f) x → S._ConvergesTo_ (S.SeriesOf g) y →
  S._ConvergesTo_ (S.SeriesOf (λ k → f k + g k)) (x + y)
plusConv {f} {g} cf cg = S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
  (λ {(suc n) → P.≃-symm (plusPrefix f g (suc n))}) (_ , Conv.addR cf cg)

minusConv : ∀ {f g : Terms} {x y} →
  S._ConvergesTo_ (S.SeriesOf f) x → S._ConvergesTo_ (S.SeriesOf g) y →
  S._ConvergesTo_ (S.SeriesOf (λ k → f k - g k)) (x - y)
minusConv {f} {g} cf cg = S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
  (λ {(suc n) → P.≃-symm (minusPrefix f g (suc n))}) (_ , Conv.subR cf cg)

absBudget : ∀ f g → S.SeriesOf_ConvergesAbsolutely f → S.SeriesOf_ConvergesAbsolutely g →
  S._isConvergent (S.SeriesOf (λ k → ∣ f k ∣ + ∣ g k ∣))
absBudget f g hf hg = _ , plusConv (proj₂ hf) (proj₂ hg)

plusAbs : ∀ f g → S.SeriesOf_ConvergesAbsolutely f → S.SeriesOf_ConvergesAbsolutely g →
  S.SeriesOf_ConvergesAbsolutely (λ k → f k + g k)
plusAbs f g hf hg = S.proposition-3-5 (absBudget f g hf hg)
  (zero , λ n _ → P.≤-respˡ-≃
    (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ (f n + g n)))
    (P.∣x+y∣≤∣x∣+∣y∣ (f n) (g n)))

minusAbs : ∀ f g → S.SeriesOf_ConvergesAbsolutely f → S.SeriesOf_ConvergesAbsolutely g →
  S.SeriesOf_ConvergesAbsolutely (λ k → f k - g k)
minusAbs f g hf hg = S.proposition-3-5 (absBudget f g hf hg)
  (zero , λ n _ → P.≤-respˡ-≃
    (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ (f n - g n)))
    (P.≤-respʳ-≃ (P.+-cong P.≃-refl P.∣-x∣≃∣x∣)
      (P.∣x+y∣≤∣x∣+∣y∣ (f n) (R.- g n))))

complexRow : CTerms → CTerms → CTerms
complexRow f g n = C.complex
  (Abs.conv (C.realTerms f) (C.realTerms g) n - Abs.conv (C.imagTerms f) (C.imagTerms g) n)
  (Abs.conv (C.realTerms f) (C.imagTerms g) n + Abs.conv (C.imagTerms f) (C.realTerms g) n)

productAbsolute : ∀ f g → C.ComponentwiseAbsoluteSeriesConvergent f →
  C.ComponentwiseAbsoluteSeriesConvergent g → C.ComponentwiseAbsoluteSeriesConvergent (complexRow f g)
productAbsolute f g hf hg =
  let a = C.realTerms f; b = C.imagTerms f; c = C.realTerms g; d = C.imagTerms g
      ac = Abs.productAbsolute a c (C.realAbsolute hf) (C.realAbsolute hg)
      bd = Abs.productAbsolute b d (C.imagAbsolute hf) (C.imagAbsolute hg)
      ad = Abs.productAbsolute a d (C.realAbsolute hf) (C.imagAbsolute hg)
      bc = Abs.productAbsolute b c (C.imagAbsolute hf) (C.realAbsolute hg)
  in C.componentwise-absolute-series-convergent (minusAbs _ _ ac bd) (plusAbs _ _ ad bc)

productLimit : ∀ f g x y → C.ComponentwiseAbsoluteSeriesConvergent f →
  C.ComponentwiseAbsoluteSeriesConvergent g → C.ComplexSeriesConvergesTo f x →
  C.ComplexSeriesConvergesTo g y → C.ComplexSeriesConvergesTo (complexRow f g) (x *C y)
productLimit f g x y hf hg fx gy =
  let a = C.realTerms f; b = C.imagTerms f; c = C.realTerms g; d = C.imagTerms g
      ac = Abs.productConverges a c (C.re x) (C.re y) (C.realAbsolute hf) (C.realAbsolute hg) (C.realConverges fx) (C.realConverges gy)
      bd = Abs.productConverges b d (C.im x) (C.im y) (C.imagAbsolute hf) (C.imagAbsolute hg) (C.imagConverges fx) (C.imagConverges gy)
      ad = Abs.productConverges a d (C.re x) (C.im y) (C.realAbsolute hf) (C.imagAbsolute hg) (C.realConverges fx) (C.imagConverges gy)
      bc = Abs.productConverges b c (C.im x) (C.re y) (C.imagAbsolute hf) (C.realAbsolute hg) (C.imagConverges fx) (C.realConverges gy)
  in C.complex-series-converges-to (minusConv ac bd) (plusConv ad bc)

-- Termwise equality transports BOTH convergence and absolute convergence.
absTransport : ∀ {f g : Terms} → (∀ n → f n ≃ g n) →
  S.SeriesOf_ConvergesAbsolutely f → S.SeriesOf_ConvergesAbsolutely g
absTransport eq h = proj₁ h , S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
  (λ {(suc n) → Ext.seriesPartialSumsCongruent (λ k → P.∣-∣-cong (eq k)) (suc n)}) h

complexAbsTransport : ∀ {f g : CTerms} → (∀ n → f n ≈C g n) →
  C.ComponentwiseAbsoluteSeriesConvergent f → C.ComponentwiseAbsoluteSeriesConvergent g
complexAbsTransport eq h = C.componentwise-absolute-series-convergent
  (absTransport (λ n → proj₁ (eq n)) (C.realAbsolute h))
  (absTransport (λ n → proj₂ (eq n)) (C.imagAbsolute h))

complexLimitTransport : ∀ {f g : CTerms} {x} → (∀ n → f n ≈C g n) →
  C.ComplexSeriesConvergesTo f x → C.ComplexSeriesConvergesTo g x
complexLimitTransport eq h = C.complex-series-converges-to
  (S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) → Ext.seriesPartialSumsCongruent (λ k → proj₁ (eq k)) (suc n)}) (_ , C.realConverges h))
  (S.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) → Ext.seriesPartialSumsCongruent (λ k → proj₂ (eq k)) (suc n)}) (_ , C.imagConverges h))

-- The integer coefficient carrier is the original Ramanujan row,
-- not another convolution. Weight by the same half-phase t.
weight : BishopComplex → I.SeriesZ → CTerms
weight t f n = scaleC (I.embed (f n)) (powC t n)

scaleProduct : ∀ a b z w → (scaleC a z *C scaleC b w) ≈C scaleC (a * b) (z *C w)
scaleProduct a b (C.complex x y) (C.complex u v) =
  (let open P.ℝ-Solver in solve 6
    (λ a b x y u v → (a ⊗ x) ⊗ (b ⊗ u) ⊖ (a ⊗ y) ⊗ (b ⊗ v)
      ⊜ (a ⊗ b) ⊗ (x ⊗ u ⊖ y ⊗ v)) P.≃-refl a b x y u v) ,
  (let open P.ℝ-Solver in solve 6
    (λ a b x y u v → (a ⊗ x) ⊗ (b ⊗ v) ⊕ (a ⊗ y) ⊗ (b ⊗ u)
      ⊜ (a ⊗ b) ⊗ (x ⊗ v ⊕ y ⊗ u)) P.≃-refl a b x y u v)

weightedSummand : ∀ t f g n (i : Fin (suc n)) →
  (weight t f (toℕ i) *C weight t g (n N.∸ toℕ i)) ≈C
  scaleC (I.embed (f (toℕ i)) * I.embed (g (n N.∸ toℕ i))) (powC t n)
weightedSummand t f g n i =
  let k = toℕ i; j = n N.∸ k
  in complexTrans (scaleProduct (I.embed (f k)) (I.embed (g j)) (powC t k) (powC t j))
    (A.scaleCCongruent (complexTrans (L.powAdd t k j)
      (P.≃-refl₂ (cong (λ x → C.re (powC t x)) (T.indexPlusTruncatedComplement n k (FP.toℕ≤pred[n] i))) ,
       P.≃-refl₂ (cong (λ x → C.im (powC t x)) (T.indexPlusTruncatedComplement n k (FP.toℕ≤pred[n] i)))))
      (I.embed (f k) * I.embed (g j)))

sumSub : ∀ n (f g : Fin n → ℝ) →
  Row.BishopSum.sum (λ i → f i - g i) ≃ (Row.BishopSum.sum f - Row.BishopSum.sum g)
sumSub zero f g = P.≃-symm (P.+-inverseʳ R.0ℝ)
sumSub (suc n) f g = P.≃-trans
  (P.+-cong P.≃-refl (sumSub n (λ i → f (fsuc i)) (λ i → g (fsuc i))))
  (let open P.ℝ-Solver in solve 4
    (λ a b c d → (a ⊖ b) ⊕ (c ⊖ d) ⊜ (a ⊕ c) ⊖ (b ⊕ d))
    P.≃-refl (f fzero) (g fzero) (Row.BishopSum.sum (λ i → f (fsuc i))) (Row.BishopSum.sum (λ i → g (fsuc i))))

-- Finite coefficient transport: scalar powers combine before the
-- original integer row is reflected. No infinite rearrangement here.
weightedRow : ∀ t f g n → complexRow (weight t f) (weight t g) n ≈C weight t (I.rowZ f g) n
weightedRow t f g n =
  let a = C.realTerms (weight t f); b = C.imagTerms (weight t f)
      c = C.realTerms (weight t g); d = C.imagTerms (weight t g)
      j = λ (i : Fin (suc n)) → n N.∸ toℕ i
      k = λ (i : Fin (suc n)) → I.embed (f (toℕ i)) * I.embed (g (j i))
      x = C.re (powC t n); y = C.im (powC t n)
      foldRead : Row.BishopSum.sum k ≃ I.embed (I.rowZ f g n)
      foldRead = P.≃-symm (I.rowEmbed f g n)
      collapse : ∀ u → Row.BishopSum.sum (λ i → k i * u) ≃ (I.embed (I.rowZ f g n) * u)
      collapse u = P.≃-trans
        (Row.BishopSum.sum-cong-≋ (λ i → P.*-comm (k i) u))
        (P.≃-trans (P.≃-symm (Row.BishopSum.*-distribˡ-sum u k))
          (P.≃-trans (P.*-comm u (Row.BishopSum.sum k)) (P.*-congʳ foldRead)))
  in P.≃-trans
      (P.≃-symm (sumSub (suc n) (λ i → a (toℕ i) * c (j i)) (λ i → b (toℕ i) * d (j i))))
      (P.≃-trans (Row.BishopSum.sum-cong-≋ (λ i → proj₁ (weightedSummand t f g n i))) (collapse x)) ,
     P.≃-trans
      (P.≃-symm (Row.BishopSum.∑-distrib-+ (λ i → a (toℕ i) * d (j i)) (λ i → b (toℕ i) * c (j i))))
      (P.≃-trans (Row.BishopSum.sum-cong-≋ (λ i → proj₂ (weightedSummand t f g n i))) (collapse y))

record Readout (t : BishopComplex) (f : I.SeriesZ) : Set where
  field
    value : BishopComplex
    absolute : C.ComponentwiseAbsoluteSeriesConvergent (weight t f)
    converges : C.ComplexSeriesConvergesTo (weight t f) value
open Readout public

product : ∀ {t f g} → Readout t f → Readout t g → Readout t (I.rowZ f g)
product {t} {f} {g} hf hg = record
  { value = value hf *C value hg
  ; absolute = complexAbsTransport (weightedRow t f g)
      (productAbsolute _ _ (absolute hf) (absolute hg))
  ; converges = complexLimitTransport (weightedRow t f g)
      (productLimit _ _ _ _ (absolute hf) (absolute hg) (converges hf) (converges hg))
  }

fourth : ∀ {t f} → Readout t f → Readout t (I.rowZ (I.rowZ f f) (I.rowZ f f))
fourth h = product (product h h) (product h h)
