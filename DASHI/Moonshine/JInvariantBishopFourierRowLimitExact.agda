module DASHI.Moonshine.JInvariantBishopFourierRowLimitExact where

-- SOURCE-WRITTEN, UNCOMPILED. On the original disk, all Fourier
-- polynomial tails vanish. The finite cleared telescope is carried to
-- its actual componentwise Bishop series limit, not a formal germ.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as NZ
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexConstantMultiplicationConvergenceExact as Mul
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as Poly
import DASHI.Analysis.BishopVanishingDifferenceConvergenceExact as Vanish
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopCubicTranslationIteratedExact as N
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as Dyadic
import DASHI.Moonshine.JInvariantBishopFourierRowFiniteTailExact as F
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_+C_; _-C_; _*C_; powC; scaleC)
open Comp using (complexTrans; complexSym)
open Completion using (OriginalBishopPointwiseComplexConverges; original-bishop-pointwise-complex-converges; realConverges; imaginaryConverges)

Conv = OriginalBishopPointwiseComplexConverges

constantC : ∀ z → Conv (λ _ → z) z
constantC z = original-bishop-pointwise-complex-converges
  (Power.constantConverges (C.re z)) (Power.constantConverges (C.im z))

convTransport : ∀ {f g : Nat → BishopComplex} {z} →
  (∀ n → f n ≈C g n) → Conv f z → Conv g z
convTransport eq conv = original-bishop-pointwise-complex-converges
  (Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ {(suc n) → proj₁ (eq (suc n))}) (_ , realConverges conv))
  (Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ {(suc n) → proj₂ (eq (suc n))}) (_ , imaginaryConverges conv))

limitTransport : ∀ {f : Nat → BishopComplex} {z w} →
  z ≈C w → Conv f z → Conv f w
limitTransport eq conv = original-bishop-pointwise-complex-converges
  (Seq.xₙ→x∧x≃y⇒xₙ→y (realConverges conv) (proj₁ eq))
  (Seq.xₙ→x∧x≃y⇒xₙ→y (imaginaryConverges conv) (proj₂ eq))

convUnique : ∀ {f : Nat → BishopComplex} {a b} →
  Conv f a → Conv f b → a ≈C b
convUnique a b =
  Seq.uniqueness-of-limits (realConverges a) (realConverges b) ,
  Seq.uniqueness-of-limits (imaginaryConverges a) (imaginaryConverges b)

addConv : ∀ {f g : Nat → BishopComplex} {a b} →
  Conv f a → Conv g b → Conv (λ n → f n +C g n) (a +C b)
addConv f g = original-bishop-pointwise-complex-converges
  (Seq.xₙ+yₙ→x₀+y₀ (_ , realConverges f) (_ , realConverges g))
  (Seq.xₙ+yₙ→x₀+y₀ (_ , imaginaryConverges f) (_ , imaginaryConverges g))

subConv : ∀ {f g : Nat → BishopComplex} {a b} →
  Conv f a → Conv g b → Conv (λ n → f n -C g n) (a -C b)
subConv f g = original-bishop-pointwise-complex-converges
  (Mul.originalBishopSubtractConverges _ _ _ _ (realConverges f) (realConverges g))
  (Mul.originalBishopSubtractConverges _ _ _ _ (imaginaryConverges f) (imaginaryConverges g))

mulConst : ∀ a {f : Nat → BishopComplex} {b} →
  Conv f b → Conv (λ n → a *C f n) (a *C b)
mulConst a f = Mul.originalBishopConstantComplexMultiplyConverges a _ _ f

rightMulNull : ∀ a {f : Nat → BishopComplex} →
  Conv f A.zeroC → Conv (λ n → f n *C a) A.zeroC
rightMulNull a {f} conv =
  convTransport (λ n → L.complexMultiplyCommutative a (f n))
    (limitTransport (L.complexMultiplyRightZero a) (mulConst a conv))

seriesTermNull : (t : Nat → R.ℝ) → (L : R.ℝ) →
  Seq._ConvergesTo_ (Seq.SeriesOf t) L → Seq._ConvergesTo_ t R.0ℝ
seriesTermNull t l conv =
  let shifted = Seq.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y
        (Seq.shift-is-subsequence (Seq.SeriesOf t) 1) (l , conv)
      dif = Mul.originalBishopSubtractConverges
        (λ n → Seq.SeriesOf t (suc n)) (Seq.SeriesOf t) l l shifted conv
  in Seq.xₙ→x∧x≃y⇒xₙ→y
    (Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ {(suc n) → let open P.ℝ-Solver in solve 2
        (λ s t → (s ⊕ t) ⊖ s ⊜ t) P.≃-refl
        (Seq.SeriesOf t (suc n)) (t (suc n))})
      (R._-_ l l , dif))
    (P.+-inverseʳ l)

dominatedNull : ∀ {f b : Nat → R.ℝ} →
  Seq._ConvergesTo_ b R.0ℝ →
  (∀ n → R.NonNegative (b n)) →
  (∀ n → R._≤_ (R.∣ f n ∣) (b n)) →
  Seq._ConvergesTo_ f R.0ℝ
dominatedNull {f} {b} conv nn bound =
  Vanish.vanishingDifferenceConvergence
    (Power.constantConverges R.0ℝ) conv
    (λ n → P.≤-respʳ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x (nn n)))
      (P.≤-respˡ-≃ (P.∣-∣-cong
        (let open P.ℝ-Solver in solve 1 (λ x → x ⊖ Κ 0ℚᵘ ⊜ x)
          P.≃-refl (f n))) (bound n)))

scaleOne : ∀ z → scaleC R.1ℝ z ≈C z
scaleOne (C.complex a b) = P.*-identityˡ a , P.*-identityˡ b

scaleShuffle : ∀ m n z a →
  (scaleC m z *C scaleC n a) ≈C (scaleC (R._*_ m n) z *C a)
scaleShuffle m n (C.complex x y) (C.complex a b) =
  (let open P.ℝ-Solver in solve 6
    (λ m n x y a b → (m ⊗ x) ⊗ (n ⊗ a) ⊖ (m ⊗ y) ⊗ (n ⊗ b)
      ⊜ ((m ⊗ n) ⊗ x) ⊗ a ⊖ ((m ⊗ n) ⊗ y) ⊗ b)
    P.≃-refl m n x y a b)
  ,
  (let open P.ℝ-Solver in solve 6
    (λ m n x y a b → (m ⊗ x) ⊗ (n ⊗ b) ⊕ (m ⊗ y) ⊗ (n ⊗ a)
      ⊜ ((m ⊗ n) ⊗ x) ⊗ b ⊕ ((m ⊗ n) ⊗ y) ⊗ a)
    P.≃-refl m n x y a b)

powOne : ∀ n → powC A.oneC n ≈C A.oneC
powOne zero = C.≈C-refl _
powOne (suc n) = complexTrans
  (A.mulCCongruent (C.≈C-refl _) (powOne n))
  (L.complexMultiplyLeftIdentity A.oneC)

cancelPower : ∀ z (nz : Rec.BishopComplexNonzero z) k →
  (powC z k *C powC (Rec.reciprocalC z nz) k) ≈C A.oneC
cancelPower z nz k = complexTrans
  (complexSym (G.powProduct z (Rec.reciprocalC z nz) k))
  (complexTrans (A.powCCongruent (Rec.multiplyReciprocal z nz) k) (powOne k))

-- A literal unit-disk certificate supplies both signs of gap guards.
module AtDisk {q : BishopComplex} {r : R.ℝ} (input : Disk.BishopUnitDiskQ q r) where
  unit = Disk.unitInterval input
  envelope = Disk.powerEnvelope input
  rNN = Unit.ratioNonnegative unit
  rLt = Unit.ratioBelowOne unit

  gapGuard : Rec.BishopComplexNonzero (Dyadic.gapMinus q)
  gapGuard = NZ.complexNonzeroFromRealApart (inj₂
    (P.x<y⇒0<y-x (C.re q) R.1ℝ
      (P.≤-<-trans
        (P.≤-trans P.x≤∣x∣
          (P.≤-respˡ-≃
            (P.∣-∣-cong (P.≃-symm (proj₁ (L.complexMultiplyRightIdentity q))))
            (Norm.realPowerBound envelope zero))) rLt)))

  majorant : Nat → Nat → R.ℝ
  majorant k n = Poly.shiftedScaledPolynomialGeometricTerm R.1ℝ r k n

  majorantAbs : ∀ k → Seq.SeriesOf_ConvergesAbsolutely (majorant k)
  majorantAbs k = Poly.shiftedScaledPolynomialGeometricSeriesAbsolutelyConvergent
    r R.1ℝ k rNN rLt (Poly.natRealNonnegative 1)

  majorantNN : ∀ k n → R.NonNegative (majorant k n)
  majorantNN k n = Poly.shiftedScaledPolynomialGeometricTermNonnegative rNN
    (Poly.natRealNonnegative 1) k n

  majorantNull : ∀ k → Seq._ConvergesTo_ (majorant k) R.0ℝ
  majorantNull k =
    let conv = Seq.absolute⇒isConvergent (majorantAbs k)
    in seriesTermNull (majorant k) (proj₁ conv) (proj₂ conv)

  componentBound : ∀ k n z →
    R._≤_ (R.∣ z ∣) (R.pow r (suc n)) →
    R._≤_ (R.∣ R._*_ (R.pow (N.natReal (suc n)) k) z ∣) (majorant k n)
  componentBound k n z b = P.≤-respʳ-≃
    (P.≃-symm (P.*-identityˡ (Poly.polynomialGeometricTerm r k (suc n))))
    (E.scaledComponentAbsoluteBound
      (Seq.nonNegx⇒nonNegxⁿ k (Poly.natRealNonnegative (suc n)))
      (Unit.ratioPowerNonnegative unit (suc n)) P.≤-refl b)

  realBound : ∀ k n → R._≤_ (R.∣ C.re (F.term k q n) ∣) (majorant k n)
  realBound k n = componentBound k n (C.re (powC q (suc n))) (Norm.realPowerBound envelope n)

  imagBound : ∀ k n → R._≤_ (R.∣ C.im (F.term k q n) ∣) (majorant k n)
  imagBound k n = componentBound k n (C.im (powC q (suc n))) (Norm.imagPowerBound envelope n)

  rowAbsolute : ∀ k → C.ComponentwiseAbsoluteSeriesConvergent (F.term k q)
  rowAbsolute k = C.componentwise-absolute-series-convergent
    (E.absoluteSeriesFromMajorant (C.realTerms (F.term k q)) (majorant k)
      (majorantAbs k) (realBound k))
    (E.absoluteSeriesFromMajorant (C.imagTerms (F.term k q)) (majorant k)
      (majorantAbs k) (imagBound k))

  row : Nat → BishopComplex
  row k = C.complexSeriesLimit (F.term k q) (rowAbsolute k)

  rowConverges : ∀ k → Conv (F.partial k q) (row k)
  rowConverges k =
    let conv = C.complexSeriesLimitConvergence (F.term k q) (rowAbsolute k)
    in original-bishop-pointwise-complex-converges
      (C.realConverges conv) (C.imagConverges conv)

  termNull : ∀ k → Conv (F.term k q) A.zeroC
  termNull k = original-bishop-pointwise-complex-converges
    (dominatedNull (majorantNull k) (majorantNN k) (realBound k))
    (dominatedNull (majorantNull k) (majorantNN k) (imagBound k))

  -- Horner induction: every polynomial in the actual positive index,
  -- times the original q^(n+1), vanishes, for arbitrary fixed degree.
  polynomialTailNull : ∀ k (cs : List BishopComplex) →
    Conv (λ n → F.term k q n *C F.evalR (N.natReal (suc n)) cs) A.zeroC
  polynomialTailNull k [] =
    convTransport (λ n → complexSym (L.complexMultiplyRightZero (F.term k q n)))
      (constantC A.zeroC)
  polynomialTailNull k (a ∷ as) =
    convTransport (λ n → complexSym (step n))
      (limitTransport (L.complexAddLeftIdentity A.zeroC)
        (addConv (rightMulNull a (termNull k)) (polynomialTailNull (suc k) as)))
    where
    step : ∀ n →
      (F.term k q n *C F.evalR (N.natReal (suc n)) (a ∷ as)) ≈C
      ((F.term k q n *C a) +C
        (F.term (suc k) q n *C F.evalR (N.natReal (suc n)) as))
    step n =
      let x = N.natReal (suc n)
          z = powC q (suc n)
          b = F.evalR x as
      in complexTrans (L.complexMultiplyDistributesLeft (F.term k q n) a (scaleC x b))
        (A.addCCongruent (C.≈C-refl _)
          (scaleShuffle (R.pow x k) x z b))

  tailNull : ∀ cs →
    Conv (λ n → powC q (suc n) *C F.evalR (N.natReal (suc n)) cs) A.zeroC
  tailNull cs = convTransport
    (λ n → A.mulCCongruent (scaleOne (powC q (suc n))) (C.≈C-refl _))
    (polynomialTailNull zero cs)

  module Closed (k : Nat) (cs : List BishopComplex)
    (recurrence : ∀ n →
      (F.evalR n cs -C (q *C F.evalR (R._+_ n R.1ℝ) cs)) ≈C
      scaleC (R.pow n k) (powC (Dyadic.gapMinus q) (suc k))) where
    module Fin = F.Finite q k cs recurrence
    den = Fin.den
    inv = powC (Rec.reciprocalC (Dyadic.gapMinus q) gapGuard) (suc k)

    clearedLimit : (den *C row k) ≈C Fin.tail zero
    clearedLimit = convUnique (mulConst den (rowConverges k))
      (convTransport (λ n → complexSym (Fin.finiteRead n))
        (limitTransport
          (let z = Fin.tail zero in
            (let open P.ℝ-Solver in solve 1 (λ x → x ⊖ Κ 0ℚᵘ ⊜ x) P.≃-refl (C.re z)) ,
            (let open P.ℝ-Solver in solve 1 (λ x → x ⊖ Κ 0ℚᵘ ⊜ x) P.≃-refl (C.im z)))
          (subConv (constantC (Fin.tail zero)) (tailNull cs))))

    -- Bidirectional cancellation on the literal nonzero disk denominator.
    evaluated : row k ≈C (inv *C Fin.tail zero)
    evaluated =
      complexTrans (complexSym (L.complexMultiplyLeftIdentity (row k)))
        (complexTrans
          (A.mulCCongruent
            (complexSym (complexTrans (L.complexMultiplyCommutative inv den)
              (cancelPower (Dyadic.gapMinus q) gapGuard (suc k))))
            (C.≈C-refl _))
          (complexTrans (L.complexMultiplyAssociative inv den (row k))
            (A.mulCCongruent (C.≈C-refl inv) clearedLimit)))

  module Row4 = Closed 3 (F.coeff3 q) (λ n → F.recurrence3 n q)
  module Row6 = Closed 5 (F.coeff5 q) (λ n → F.recurrence5 n q)
