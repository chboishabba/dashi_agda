module DASHI.Moonshine.CM163BishopHecke41UniformCuspBoundExact where

-- SOURCE-WRITTEN, kernel pending. The absolute series at ONE fixed
-- nonzero reference phase bounds the SAME coefficient stream on the
-- entire smaller disk. No reciprocal of the variable cusp phase.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (z≤n)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_) 
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (from-yes)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _*_; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41CuspResidualExact as Residual
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.CM163BishopHecke41SelectedFixedChartsExact as Fixed
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; powC)
open N using (SeriesC; twist)
open Comp using (complexTrans; complexSym)

normCong : ∀ {a b} → a ≈C b → Norm.normSqC a ≃ Norm.normSqC b
normCong (h , k) = P.+-cong (P.*-cong h h) (P.*-cong k k)

powRealOne : ∀ n → R.pow R.1ℝ n ≃ R.1ℝ
powRealOne zero = P.≃-refl
powRealOne (suc n) = P.≃-trans (P.*-congʳ (powRealOne n)) (P.*-identityʳ R.1ℝ)

-- Closed unit disk quotient, including the zero phase.
relative : ∀ t r → Rec.BishopComplexNonzero r → BishopComplex
relative t r nz = t *C Rec.reciprocalC r nz

relativeRead : ∀ t r nz → (r *C relative t r nz) ≈C t
relativeRead t r nz =
  complexTrans (complexSym (L.complexMultiplyAssociative r t (Rec.reciprocalC r nz)))
    (complexTrans (A.mulCCongruent (L.complexMultiplyCommutative r t) (C.≈C-refl _))
      (complexTrans (L.complexMultiplyAssociative t r (Rec.reciprocalC r nz))
        (complexTrans (A.mulCCongruent (C.≈C-refl _) (Rec.multiplyReciprocal r nz))
          (L.complexMultiplyRightIdentity t))))

relativeUpper : ∀ t r nz → Norm.normSqC t ≤ Norm.normSqC r →
  Upper.BishopComplexNormSquareUpperRadius (relative t r nz) R.1ℝ
relativeUpper t r nz h =
  let v = Rec.reciprocalC r nz
      nv = Norm.normSqC v
      bound = P.*-mono-≤ (Upper.normSquareNonnegative t) (Upper.normSquareNonnegative v) h P.≤-refl
      one = P.≃-trans (P.≃-symm (Norm.normSqMultiply r v))
        (P.≃-trans (normCong (Rec.multiplyReciprocal r nz)) Norm.normSqOne)
  in record
    { Upper.radiusNonnegative = P.0≤x⇒nonNegx (P.<⇒≤ (P.p<q⇒p⋆<q⋆ 0ℚᵘ 1ℚᵘ (from-yes (0ℚᵘ QP.<? 1ℚᵘ))))
    ; Upper.normSqBelowRadiusSquare = P.≤-respˡ-≃ (P.≃-symm (Norm.normSqMultiply t v))
      (P.≤-respʳ-≃ (P.≃-trans one (P.≃-symm (P.*-identityʳ R.1ℝ))) bound) }

realUnit : ∀ {w} → Upper.BishopComplexNormSquareUpperRadius w R.1ℝ →
  ∀ n → ∣ C.re (powC w n) ∣ ≤ R.1ℝ
realUnit u n = P.≤-respʳ-≃ (powRealOne n) (Upper.realPowerUpper u n)

imagUnit : ∀ {w} → Upper.BishopComplexNormSquareUpperRadius w R.1ℝ →
  ∀ n → ∣ C.im (powC w n) ∣ ≤ R.1ℝ
imagUnit u n = P.≤-respʳ-≃ (powRealOne n) (Upper.imagPowerUpper u n)

absProduct : ∀ x y → ∣ x * y ∣ ≃ ∣ x ∣ * ∣ y ∣
absProduct = P.∣x*y∣≃∣x∣*∣y∣

absSubBound : ∀ a b → ∣ R._-_ a b ∣ ≤ (∣ a ∣ + ∣ b ∣)
absSubBound a b = P.≤-respʳ-≃ (P.+-cong P.≃-refl P.∣-x∣≃∣x∣)
  (P.∣x+y∣≤∣x∣+∣y∣ a (R.- b))

productBound : ∀ a b x y M →
  ∣ a ∣ ≤ M → ∣ b ∣ ≤ M →
  ∣ C.re (C.complex x y *C C.complex a b) ∣ ≤ ((∣ x ∣ + ∣ y ∣) * M) ×
  ∣ C.im (C.complex x y *C C.complex a b) ∣ ≤ ((∣ x ∣ + ∣ y ∣) * M)
productBound a b x y M ha hb =
  let term : ∀ u v → ∣ v ∣ ≤ M → ∣ u * v ∣ ≤ ∣ u ∣ * M
      term u v h = P.≤-respˡ-≃ (P.≃-symm (absProduct u v))
        (P.*-mono-≤ (P.nonNeg∣x∣ u) (P.nonNeg∣x∣ v) P.≤-refl h)
      dist = P.≃-symm (P.*-distribʳ-+ M ∣ x ∣ ∣ y ∣)
  in P.≤-trans (absSubBound (x * a) (y * b))
      (P.≤-respʳ-≃ dist (P.+-mono-≤ (term x a ha) (term y b hb))) ,
     P.≤-trans (P.∣x+y∣≤∣x∣+∣y∣ (x * b) (y * a))
      (P.≤-respʳ-≃ dist (P.+-mono-≤ (term x b hb) (term y a ha)))

-- Absolute series budget at a reference t0. This is a finite real
-- bound even if the coefficient stream is complex.
module Disk (r : BishopComplex) (nz : Rec.BishopComplexNonzero r)
  (f : SeriesC) (reference : Eval.Eval r f) where

  refTerms = twist r f
  budget : Nat → ℝ
  budget n = ∣ C.re (refTerms n) ∣ + ∣ C.im (refTerms n) ∣

  ab = Eval.absolute reference
  budgetConvergent : Seq._isConvergent (Seq.SeriesOf budget)
  budgetConvergent = CP.absBudget (C.realTerms refTerms) (C.imagTerms refTerms)
    (C.realAbsolute ab) (C.imagAbsolute ab)

  M : ℝ
  M = proj₁ budgetConvergent

  Mnonnegative : R.NonNegative M
  Mnonnegative = P.0≤x⇒nonNegx (Seq.0≤xₙ⇒0≤limxₙ
    (λ n → prefixNonnegative n) budgetConvergent)
    where
    prefixNonnegative : ∀ n → R.0ℝ ≤ Seq.SeriesOf budget n
    prefixNonnegative zero = P.≤-refl
    prefixNonnegative (suc n) = Seq.0≤x,y⇒0≤x+y (prefixNonnegative n)
      (Seq.0≤x,y⇒0≤x+y (P.0≤∣x∣ _) (P.0≤∣x∣ _))

  termRead : ∀ t n → twist (relative t r nz) refTerms n ≈C twist t f n
  termRead t n = N.transCs
    (N.twistCompose (relative t r nz) r f)
    (N.twistPhaseCong (relativeRead t r nz) f) n

  termBound : ∀ t → Norm.normSqC t ≤ Norm.normSqC r → ∀ n →
    ∣ C.re (twist t f n) ∣ ≤ budget n × ∣ C.im (twist t f n) ∣ ≤ budget n
  termBound t h n =
    let w = relative t r nz
        u = relativeUpper t r nz h
        a = refTerms n
        b = powC w n
        p = productBound (C.re b) (C.im b) (C.re a) (C.im a) R.1ℝ
          (realUnit u n) (imagUnit u n)
        read = termRead t n
    in P.≤-respˡ-≃ (P.∣-∣-cong (proj₁ read))
      (P.≤-respʳ-≃ (P.*-identityʳ (budget n)) (proj₁ p)) ,
       P.≤-respˡ-≃ (P.∣-∣-cong (proj₂ read))
      (P.≤-respʳ-≃ (P.*-identityʳ (budget n)) (proj₂ p))

  absoluteOn : ∀ t → Norm.normSqC t ≤ Norm.normSqC r →
    C.ComponentwiseAbsoluteSeriesConvergent (twist t f)
  absoluteOn t h = C.componentwise-absolute-series-convergent
    (Seq.proposition-3-5 budgetConvergent (zero , λ n _ →
      P.≤-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ _))) (proj₁ (termBound t h n))))
    (Seq.proposition-3-5 budgetConvergent (zero , λ n _ →
      P.≤-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ _))) (proj₂ (termBound t h n))))

  -- Value bound from finite prefix triangle inequality and the
  -- pinned real limit order. Uniform constant independent of t.
  valueBound : ∀ t h (ev : Eval.Eval t f) →
    ∣ C.re (Eval.value ev) ∣ ≤ M × ∣ C.im (Eval.value ev) ∣ ≤ M
  valueBound t h ev =
    let bound : ∀ g v → Seq._ConvergesTo_ (Seq.SeriesOf g) v →
          (∀ n → ∣ g n ∣ ≤ budget n) → ∣ v ∣ ≤ M
        bound g v cv hb = Seq.xₙ≤yₙ⇒x₀≤y₀ (Seq.∣xₙ∣→∣x₀∣ (v , cv))
          (proj₂ budgetConvergent) (λ n →
            P.≤-trans (Seq.∑-triangle-inequality g zero n z≤n)
              (Seq.∑₀-mono-≤ hb n))
    in bound (C.realTerms (twist t f)) (C.re (Eval.value ev))
        (C.realConverges (Eval.converges ev)) (λ n → proj₁ (termBound t h n)) ,
       bound (C.imagTerms (twist t f)) (C.im (Eval.value ev))
        (C.imagConverges (Eval.converges ev)) (λ n → proj₂ (termBound t h n))

  -- In particular the shifted coefficient series converges at t=0
  -- as well, without using the nonzero variable-phase tailRead.
  evaluate : ∀ t → Norm.normSqC t ≤ Norm.normSqC r → Eval.Eval t f
  evaluate t h = record
    { value = C.complexSeriesLimit (twist t f) (absoluteOn t h)
    ; absolute = absoluteOn t h
    ; converges = C.complexSeriesLimitConvergence _ (absoluteOn t h) }

module At (inputs : Round11.BishopCutset) where
  module R0 = Residual.At inputs
  open R0 using (t; dTail; sTail)
  reference = t Fixed.p

  module D = Disk reference (R0.V.Rm.tNZ Fixed.p) _ (dTail Fixed.p)
  module S = Disk reference (R0.V.Rm.tNZ Fixed.p) _ (sTail Fixed.p)

  diagonalBound : R0.R.W.UnitGate → R0.R.W.DiagonalGate → ∀ p →
    Norm.normSqC (t p) ≤ Norm.normSqC reference →
    ∣ C.re (R0.d p) ∣ ≤ ((∣ C.re (t p) ∣ + ∣ C.im (t p) ∣) * D.M) ×
    ∣ C.im (R0.d p) ∣ ≤ ((∣ C.re (t p) ∣ + ∣ C.im (t p) ∣) * D.M)
  diagonalBound hu hd p h =
    let b = D.valueBound (t p) h (dTail p)
        e = R0.diagonalFactor hu hd p
        z = Eval.value (dTail p)
        p0 = productBound (C.re z) (C.im z) (C.re (t p)) (C.im (t p)) D.M (proj₁ b) (proj₂ b)
    in P.≤-respˡ-≃ (P.∣-∣-cong (P.≃-symm (proj₁ e))) (proj₁ p0) ,
       P.≤-respˡ-≃ (P.∣-∣-cong (P.≃-symm (proj₂ e))) (proj₂ p0)

  sliceBound : R0.R.W.UnitGate → R0.R.W.SliceGate → ∀ p →
    Norm.normSqC (t p) ≤ Norm.normSqC reference →
    ∣ C.re (R0.s p) ∣ ≤ ((∣ C.re (t p) ∣ + ∣ C.im (t p) ∣) * S.M) ×
    ∣ C.im (R0.s p) ∣ ≤ ((∣ C.re (t p) ∣ + ∣ C.im (t p) ∣) * S.M)
  sliceBound hu hs p h =
    let b = S.valueBound (t p) h (sTail p)
        e = R0.sliceFactor hu hs p
        z = Eval.value (sTail p)
        p0 = productBound (C.re z) (C.im z) (C.re (t p)) (C.im (t p)) S.M (proj₁ b) (proj₂ b)
    in P.≤-respˡ-≃ (P.∣-∣-cong (P.≃-symm (proj₁ e))) (proj₁ p0) ,
       P.≤-respˡ-≃ (P.∣-∣-cong (P.≃-symm (proj₂ e))) (proj₂ p0)
