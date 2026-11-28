module DASHI.Moonshine.CM163BishopHecke41StrictDiskDerivativeExact where

-- SOURCE-WRITTEN, kernel pending. Construct the first coefficient
-- moment from an actual absolute outer series and a strictly smaller
-- reference phase. Then transport the exact divided-difference sum
-- back to the original coordinate. No derivative-interchange oracle.
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as Nat
open Nat using (z≤n; s≤s)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _+_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as PG
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Const
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.CM163BishopHecke41CuspTailFactorExact as Tail
import DASHI.Moonshine.CM163BishopHecke41UniformCuspBoundExact as B
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41PowerDifferenceSeriesExact as D
import DASHI.Moonshine.CM163BishopHeckeProductAlgebraExact as Alg
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_-C_; _*C_; powC)
open Comp using (complexTrans; complexSym)

four : ℝ
four = (+ 4 / 1) ⋆

-- Inner/outer reference is a relative complex phase. The stronger
-- bound |inner/outer|<=s<1 is what pays the coefficient moment.
module Shrink (outer inner : BishopComplex)
  (onz : Rec.BishopComplexNonzero outer) (inz : Rec.BishopComplexNonzero inner)
  (s : ℝ) (s0 : R.0ℝ ≤ s) (s1 : s < R.1ℝ)
  (upper : Upper.BishopComplexNormSquareUpperRadius (B.relative inner outer onz) s)
  (f : N.SeriesC) (outerEval : Eval.Eval outer f) where

  module Outer = B.Disk outer onz f outerEval
  g = N.twist inner f
  rel = B.relative inner outer onz

  massBound : ∀ n → D.mass (g n) ≤ (D.two * Outer.budget n * R.pow s n)
  massBound n =
    let a = N.twist outer f n
        p = powC rel n
        h = B.productBound (C.re p) (C.im p) (C.re a) (C.im a) (R.pow s n)
          (Upper.realPowerUpper upper n) (Upper.imagPowerUpper upper n)
        eq = Outer.termRead inner n
        reB = P.≤-respˡ-≃ (P.∣-∣-cong (proj₁ eq)) (proj₁ h)
        imB = P.≤-respˡ-≃ (P.∣-∣-cong (proj₂ eq)) (proj₂ h)
    in P.≤-respʳ-≃
      (let open P.ℝ-Solver in solve 2
        (λ b p → b ⊗ p ⊕ b ⊗ p ⊜ Κ (+ 2 / 1) ⊗ b ⊗ p)
        P.≃-refl (Outer.budget n) (R.pow s n))
      (P.+-mono-≤ reB imB)

  weight : Nat → ℝ
  weight n = PG.polynomialGeometricTerm s 1 n

  weightConv : Seq._isConvergent (Seq.SeriesOf weight)
  weightConv = PG.polynomialGeometricSeriesConvergent s 1 s0 s1

  weightNull : Seq._ConvergesTo_ weight R.0ℝ
  weightNull = Lim.seriesTermNull weight (proj₁ weightConv) (proj₂ weightConv)

  momentRead : ∀ n → (NR.natReal n * R.pow s n) ≃ weight n
  momentRead n = P.*-congʳ
    (P.≃-symm (P.*-identityˡ (NR.natReal n)))

  budgetNN : ∀ n → R.NonNegative (Outer.budget n)
  budgetNN n = P.nonNegx,y⇒nonNegx+y (P.nonNeg∣x∣ _) (P.nonNeg∣x∣ _)

  momentNN : ∀ n → R.NonNegative (D.moment g n)
  momentNN n = P.nonNegx,y⇒nonNegx*y
    (P.nonNegx,y⇒nonNegx+y (P.nonNeg∣x∣ _) (P.nonNeg∣x∣ _))
    (P.nonNegx,y⇒nonNegx*y
      (PG.natRealNonnegative 2) (PG.natRealNonnegative n))

  -- Obtain a single finite bound on n*s^n from the original
  -- polynomial-geometric convergence, rather than a fitted constant.
  momentSummable : Seq._isConvergent (Seq.SeriesOf (D.moment g))
  momentSummable with Seq.convergent⇒bounded (R.0ℝ , weightNull)
  ... | M , Seq.bound* hb =
    let scale = four * M
        scaled : Seq._isConvergent (Seq.SeriesOf (λ n → scale * Outer.budget n))
        scaled = _ , Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
          (λ {(suc n) → P.≃-symm (Tail.scalePrefix scale Outer.budget (suc n))})
          (_ , Conv.mulR (Const.constantConverges scale) (proj₂ Outer.budgetConvergent))
        bound : ∀ n → suc zero Nat.≤ n →
          ∣ D.moment g n ∣ ≤ scale * Outer.budget n
        bound zero ()
        bound (suc n) hn =
          let k = suc n
              w = NR.natReal k
              b = Outer.budget k
              p = R.pow s k
              weightLe = P.≤-respˡ-≃
                (P.≃-trans (P.nonNegx⇒∣x∣≃x (PG.polynomialGeometricTermNonnegative s 1 k (P.0≤x⇒nonNegx s0)))
                  (P.≃-symm (momentRead k))) (hb k)
              raw = P.*-monoʳ-≤-nonNeg (massBound k)
                (P.nonNegx,y⇒nonNegx*y (PG.natRealNonnegative 2) (PG.natRealNonnegative k))
              read = let open P.ℝ-Solver in solve 3
                (λ b p w → (Κ (+ 2 / 1) ⊗ b ⊗ p) ⊗ (Κ (+ 2 / 1) ⊗ w)
                  ⊜ (Κ (+ 4 / 1) ⊗ b) ⊗ (w ⊗ p)) P.≃-refl b p w
              monotone = P.*-monoˡ-≤-nonNeg weightLe (P.nonNegx,y⇒nonNegx*y (PG.natRealNonnegative 4) (budgetNN k))
              finish = let open P.ℝ-Solver in solve 2
                (λ b M → (Κ (+ 4 / 1) ⊗ b) ⊗ M ⊜ (Κ (+ 4 / 1) ⊗ M) ⊗ b) P.≃-refl b M
          in P.≤-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x (momentNN k)))
            (P.≤-trans (P.≤-respʳ-≃ read raw) (P.≤-respʳ-≃ finish monotone))
    in Seq.proposition-3-5 scaled (zero , bound)

  module Derivative = D.Factorization g momentSummable

  Inside : BishopComplex → Set
  Inside q = Norm.normSqC q ≤ Norm.normSqC inner

  normal : BishopComplex → BishopComplex
  normal q = B.relative q inner inz

  normalUpper : ∀ q → Inside q → D.UnitDisk (normal q)
  normalUpper q h = B.relativeUpper q inner inz h

  normalEval : ∀ q → Eval.Eval q f → Eval.Eval (normal q) g
  normalEval q ev = Eval.phase (complexSym (B.relativeRead q inner inz)) ev

  diffRead : ∀ q v → (normal v -C normal q) ≈C ((v -C q) *C Rec.reciprocalC inner inz)
  diffRead q v =
    complexTrans (A.subCCongruent (L.complexMultiplyCommutative v _) (L.complexMultiplyCommutative q _))
      (complexTrans (complexSym (Alg.mulSub (Rec.reciprocalC inner inz) v q))
        (L.complexMultiplyCommutative _ _))

  quotient : ∀ q v → Inside q → Inside v → BishopComplex
  quotient q v hq hv = Rec.reciprocalC inner inz *C
    Derivative.D.value (normal q) (normal v) (normalUpper q hq) (normalUpper v hv)

  increment : ∀ q v hq hv → (eq : Eval.Eval q f) → (ev : Eval.Eval v f) →
    (Eval.value ev -C Eval.value eq) ≈C ((v -C q) *C quotient q v hq hv)
  increment q v hq hv eq ev = complexTrans
    (Derivative.increment (normal q) (normal v) (normalUpper q hq) (normalUpper v hv) (normalEval q eq) (normalEval v ev))
    (complexTrans (A.mulCCongruent (diffRead q v) (C.≈C-refl _))
      (L.complexMultiplyAssociative (v -C q) (Rec.reciprocalC inner inz) _))

  quotientLimit : ∀ q (hq : Inside q) (v : Nat → BishopComplex) (hv : ∀ n → Inside (v n)) →
    Lim.Conv v q → Lim.Conv (λ n → quotient q (v n) hq (hv n)) (quotient q q hq hq)
  quotientLimit q hq v hv cv = Lim.mulConst (Rec.reciprocalC inner inz)
    (Derivative.D.continuous (normal q) (normalUpper q hq) (λ n → normal (v n)) (normal q)
      (λ n → normalUpper (v n) (hv n)) (normalUpper q hq)
      (Conv.mulConv cv (Lim.constantC (Rec.reciprocalC inner inz))))
