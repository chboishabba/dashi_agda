module DASHI.Moonshine.JInvariantBishopComplexOriginQuadraticRemainderExact where

-- SOURCE-WRITTEN, UNCOMPILED. Directional origin expansion on the original
-- Cartesian exponential, without division by the perturbation.
-- exp(h z) = 1 + h z + h² R(h,z), |h| <= 1.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Data.Nat.Base as N
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Analysis.BishopComplexExpFactEqualsNativeExpExact as Native
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopOriginalExpOriginDerivativeClosedExact as Orig
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopComplexConstantMultiplicationConvergenceExact as Mul
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Recip
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as Axis
import DASHI.Moonshine.AbelBishopFactorialComplexExpDiskExact as Fact
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
open C using (BishopComplex; _≈C_)
open A using (_+C_; _*C_; scaleC; powC)
open Comp using (complexTrans; complexSym)
open Completion using (original-bishop-pointwise-complex-converges; realConverges; imaginaryConverges)

F = Axis.originalBishopFactorialComplexTerm

scaleAxis : ∀ h z → scaleC h z ≈C (Axis.realAxis h *C z)
scaleAxis h (C.complex x y) =
  (let open P.ℝ-Solver in solve 3 (λ h x y → h ⊗ x ⊜ h ⊗ x ⊖ Κ 0ℚᵘ ⊗ y) P.≃-refl h x y) ,
  (let open P.ℝ-Solver in solve 3 (λ h x y → h ⊗ y ⊜ h ⊗ y ⊕ Κ 0ℚᵘ ⊗ x) P.≃-refl h x y)

scalePower : ∀ h z n → powC (scaleC h z) n ≈C scaleC (R.pow h n) (powC z n)
scalePower h z n = complexTrans (A.powCCongruent (scaleAxis h z) n)
  (complexTrans (G.powProduct (Axis.realAxis h) z n)
    (complexTrans (A.mulCCongruent (Axis.realAxisPower h n) (C.≈C-refl _))
      (complexSym (scaleAxis (R.pow h n) (powC z n)))))

scaleNest : ∀ a b z → scaleC a (scaleC b z) ≈C scaleC (R._*_ a b) z
scaleNest a b (C.complex x y) =
  P.≃-symm (P.*-assoc a b x) , P.≃-symm (P.*-assoc a b y)

scaleAdd : ∀ a z w → scaleC a (z +C w) ≈C (scaleC a z +C scaleC a w)
scaleAdd a (C.complex x y) (C.complex u v) =
  (let open P.ℝ-Solver in solve 3 (λ a x u → a ⊗ (x ⊕ u) ⊜ a ⊗ x ⊕ a ⊗ u) P.≃-refl a x u) ,
  (let open P.ℝ-Solver in solve 3 (λ a y v → a ⊗ (y ⊕ v) ⊜ a ⊗ y ⊕ a ⊗ v) P.≃-refl a y v)

tailTerm : R.ℝ → BishopComplex → Nat → BishopComplex
tailTerm h z n = scaleC (R.pow h n) (F z (suc (suc n)))

factorTerm : ∀ h z n → F (scaleC h z) (suc (suc n)) ≈C
  scaleC (R._*_ h h) (tailTerm h z n)
factorTerm h z n =
  let a = Fact.factorialCoefficient (suc (suc n))
      p = R.pow h n
      w = powC z (suc (suc n))
      eq = let open P.ℝ-Solver in solve 3
             (λ a p h → a ⊗ ((p ⊗ h) ⊗ h) ⊜ (h ⊗ h) ⊗ (p ⊗ a))
             P.≃-refl a p h
  in complexTrans (A.scaleCCongruent (scalePower h z (suc (suc n))) a)
    (complexTrans (scaleNest a (R.pow h (suc (suc n))) w)
      (complexTrans (P.*-congʳ eq , P.*-congʳ eq)
        (complexSym (complexTrans (scaleNest (R._*_ h h) p (scaleC a w))
          (scaleNest (R._*_ (R._*_ h h) p) a w)))))

partial : (Nat → BishopComplex) → Nat → BishopComplex
partial t n = C.complex (Seq.SeriesOf (C.realTerms t) n)
                          (Seq.SeriesOf (C.imagTerms t) n)

scaleZero : ∀ h → scaleC h A.zeroC ≈C A.zeroC
scaleZero h =
  (let open P.ℝ-Solver in solve 1 (λ h → h ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl h) ,
  (let open P.ℝ-Solver in solve 1 (λ h → h ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl h)

head0 : ∀ z → F z zero ≈C A.oneC
head0 z = complexTrans
  (P.*-congʳ Fact.factorialCoefficientZeroIsOne , P.*-congʳ Fact.factorialCoefficientZeroIsOne)
  (Lim.scaleOne A.oneC)

head1 : ∀ z → F z (suc zero) ≈C z
head1 z = complexTrans
  (A.scaleCCongruent (L.complexMultiplyRightIdentity z) (Fact.factorialCoefficient 1))
  (complexTrans (P.*-congʳ eq , P.*-congʳ eq) (Lim.scaleOne z))
  where
  eq : R._≃_ (Fact.factorialCoefficient 1) R.1ℝ
  eq = let open P.ℝ-Solver in solve 0 (Κ 1ℚᵘ ⊜ Κ 1ℚᵘ) P.≃-refl

partialFactor : ∀ h z n →
  partial (F (scaleC h z)) (suc (suc n)) ≈C
  ((A.oneC +C scaleC h z) +C scaleC (R._*_ h h) (partial (tailTerm h z) n))
partialFactor h z zero =
  complexTrans
    (A.addCCongruent (complexTrans (L.complexAddLeftIdentity _) (head0 _)) (head1 _))
    (complexSym (complexTrans
      (A.addCCongruent (C.≈C-refl _) (scaleZero (R._*_ h h)))
      (L.complexAddRightIdentity _)))
partialFactor h z (suc n) =
  complexTrans (A.addCCongruent (partialFactor h z n) (factorTerm h z n))
    (complexTrans (L.complexAddAssociative _ _ _)
      (A.addCCongruent (C.≈C-refl _)
        (complexSym (scaleAdd (R._*_ h h) (partial (tailTerm h z) n) (tailTerm h z n)))))

scaledPartial : ∀ a t n →
  R._≃_ (Seq.SeriesOf (λ k → R._*_ a (t k)) n)
        (R._*_ a (Seq.SeriesOf t n))
scaledPartial a t zero =
  let open P.ℝ-Solver in solve 1 (λ a → Κ 0ℚᵘ ⊜ a ⊗ Κ 0ℚᵘ) P.≃-refl a
scaledPartial a t (suc n) =
  P.≃-trans (P.+-cong (scaledPartial a t n) P.≃-refl)
    (let open P.ℝ-Solver in solve 3
      (λ a s x → a ⊗ s ⊕ a ⊗ x ⊜ a ⊗ (s ⊕ x))
      P.≃-refl a (Seq.SeriesOf t n) (t n))

scaleConv : ∀ a {f : Nat → BishopComplex} {z} →
  Lim.Conv f z → Lim.Conv (λ n → scaleC a (f n)) (scaleC a z)
scaleConv a cv = original-bishop-pointwise-complex-converges
  (Mul.originalBishopMultiplyConstantConverges a _ _ (realConverges cv))
  (Mul.originalBishopMultiplyConstantConverges a _ _ (imaginaryConverges cv))

module AtDirection (z : BishopComplex) (M : R.ℝ)
  (upper : Upper.BishopComplexNormSquareUpperRadius z M) where
  nn = Upper.radiusNonnegative upper
  M2 = R._*_ M M
  majorant : Nat → R.ℝ
  majorant n = R._*_ M2 (Exp.expTerm M n)
  budget = R._*_ M2 (Exp.bishopExp M)

  majorantNN : ∀ n → R.NonNegative (majorant n)
  majorantNN n = P.nonNegx,y⇒nonNegx*y (P.nonNegx,y⇒nonNegx*y nn nn)
    (P.nonNegx,y⇒nonNegx*y (Seq.nonNegx⇒nonNegxⁿ n nn)
      (Exp.embeddedInverseFactorialNonnegative n))

  majorantConverges : Seq._ConvergesTo_ (Seq.SeriesOf majorant) budget
  majorantConverges = Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) → P.≃-symm (scaledPartial M2 (Exp.expTerm M) (suc n))})
    (budget , Mul.originalBishopMultiplyConstantConverges M2 _ _ (Exp.bishopExpConverges M))

  majorantAbsolute : Seq.SeriesOf_ConvergesAbsolutely majorant
  majorantAbsolute = budget , Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc n) → Ext.seriesPartialSumsCongruent
      (λ k → P.≃-symm (P.nonNegx⇒∣x∣≃x (majorantNN k))) (suc n)})
    (budget , majorantConverges)

  module AtStep (h : R.ℝ) (small : R._≤_ (R.∣ h ∣) R.1ℝ) where
    hPowerBound : ∀ n → R._≤_ (R.∣ R.pow h n ∣) R.1ℝ
    hPowerBound n = P.≤-respˡ-≃ (Seq.∣xⁿ∣≃∣x∣ⁿ h n)
      (P.≤-respʳ-≃ (Recip.oneToAnyNatPower n)
        (Seq.x≤y∧nonNegx⇒xⁿ≤yⁿ n small (P.nonNeg∣x∣ h)))

    factorialBound : ∀ n u →
      R._≤_ (R.∣ u ∣) (R.pow M (suc (suc n))) →
      R._≤_ (R.∣ R._*_ (Fact.factorialCoefficient (suc (suc n))) u ∣) (majorant n)
    factorialBound n u b =
      P.≤-respʳ-≃
        (let open P.ℝ-Solver in solve 3
          (λ f p m → f ⊗ ((p ⊗ m) ⊗ m) ⊜ (m ⊗ m) ⊗ (p ⊗ f))
          P.≃-refl (Fact.factorialCoefficient n) (R.pow M n) M)
        (E.scaledComponentAbsoluteBound
          (Exp.embeddedInverseFactorialNonnegative (suc (suc n)))
          (Seq.nonNegx⇒nonNegxⁿ (suc (suc n)) nn)
          (P.≤-trans (Orig.originalInverseFactorialNonIncreasing (suc n))
                     (Orig.originalInverseFactorialNonIncreasing n)) b)

    stepBound : ∀ n u → R._≤_ (R.∣ u ∣) (majorant n) →
      R._≤_ (R.∣ R._*_ (R.pow h n) u ∣) (majorant n)
    stepBound n u b = P.≤-respˡ-≃ (P.∣x*y∣≃∣x∣*∣y∣ (R.pow h n) u)
      (P.≤-respʳ-≃ (P.*-identityˡ (majorant n))
        (P.*-mono-≤ (P.nonNeg∣x∣ (R.pow h n)) (P.nonNeg∣x∣ u) (hPowerBound n) b))

    realBound : ∀ n → R._≤_ (R.∣ C.re (tailTerm h z n) ∣) (majorant n)
    realBound n = stepBound n _ (factorialBound n _ (Upper.realPowerUpper upper (suc (suc n))))
    imagBound : ∀ n → R._≤_ (R.∣ C.im (tailTerm h z n) ∣) (majorant n)
    imagBound n = stepBound n _ (factorialBound n _ (Upper.imagPowerUpper upper (suc (suc n))))

    absolute : C.ComponentwiseAbsoluteSeriesConvergent (tailTerm h z)
    absolute = C.componentwise-absolute-series-convergent
      (E.absoluteSeriesFromMajorant (C.realTerms (tailTerm h z)) majorant majorantAbsolute realBound)
      (E.absoluteSeriesFromMajorant (C.imagTerms (tailTerm h z)) majorant majorantAbsolute imagBound)

    remainder : BishopComplex
    remainder = C.complexSeriesLimit (tailTerm h z) absolute

    remainderConv : Lim.Conv (partial (tailTerm h z)) remainder
    remainderConv = let cv = C.complexSeriesLimitConvergence (tailTerm h z) absolute
      in original-bishop-pointwise-complex-converges (C.realConverges cv) (C.imagConverges cv)

    boundedLimit : ∀ (t : Nat → R.ℝ) l →
      Seq._ConvergesTo_ (Seq.SeriesOf t) l →
      (∀ n → R._≤_ (R.∣ t n ∣) (majorant n)) →
      R._≤_ (R.∣ l ∣) budget
    boundedLimit t l cv b =
      Seq.xₙ≤yₙ⇒limxₙ≤limyₙ
        (λ n → P.≤-trans (Seq.∑-triangle-inequality t zero (suc n) N.z≤n)
          (Seq.∑-mono-≤ b zero (suc n) N.z≤n))
        (R.∣ l ∣ , Seq.∣xₙ∣→∣x₀∣
          (l , Seq.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y (Seq.shift-is-subsequence (Seq.SeriesOf t) 1) (l , cv)))
        (budget , Seq.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
          (Seq.shift-is-subsequence (Seq.SeriesOf majorant) 1) (budget , majorantConverges))

    remainderRealBound = boundedLimit (C.realTerms (tailTerm h z)) (C.re remainder)
      (realConverges remainderConv) realBound
    remainderImagBound = boundedLimit (C.imagTerms (tailTerm h z)) (C.im remainder)
      (imaginaryConverges remainderConv) imagBound

    expansion : (T : Cartesian.BishopSetoidComplexTranscendentals) →
      Weld.originalBishopExpOnSeries T (scaleC h z) ≈C
      ((A.oneC +C scaleC h z) +C scaleC (R._*_ h h) remainder)
    expansion T =
      let w = scaleC h z
          exp = Weld.originalBishopExpOnSeries T w
          cv = Native.originalBishopExpFactComplexSeriesConvergesToNativeExp T (C.re w) (C.im w)
          shifted = original-bishop-pointwise-complex-converges
            (Seq.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
              (Seq.shift-is-subsequence (Seq.SeriesOf (C.realTerms (F w))) 2) (C.re exp , C.realConverges cv))
            (Seq.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
              (Seq.shift-is-subsequence (Seq.SeriesOf (C.imagTerms (F w))) 2) (C.im exp , C.imagConverges cv))
      in Lim.convUnique shifted
        (Lim.convTransport (λ n → complexSym (partialFactor h z n))
          (Lim.addConv (Lim.constantC (A.oneC +C w))
            (scaleConv (R._*_ h h) remainderConv)))
