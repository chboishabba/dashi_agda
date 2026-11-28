module DASHI.Moonshine.CM163BishopHecke41StrictDiskSecondMomentExact where

-- SOURCE-WRITTEN, kernel pending. Pay the second coefficient moment
-- from the actual outer evaluation using the existing relative phase
-- contraction and polynomial-geometric convergence, now degree two.
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as Nat
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _+_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as PG
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Const
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Moonshine.CM163BishopHecke41PowerDifferenceSeriesExact as D
import DASHI.Moonshine.CM163BishopHecke41SecondPowerWingLimitExact as T
import DASHI.Moonshine.CM163BishopHecke41StrictDiskDerivativeExact as First
import DASHI.Moonshine.CM163BishopHecke41CuspTailFactorExact as Tail
import DASHI.Moonshine.CM163BishopHecke41UniformCuspBoundExact as B
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.CM163BishopHecke41SecondJetCalculusExact as J2
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex)
open A using (_-C_; _*C_; _+C_)
open Comp using (complexTrans)

squareBudget : Nat → ℝ
squareBudget n = D.two * (NR.natReal n * NR.natReal n)

squareNN : ∀ n → R.NonNegative (squareBudget n)
squareNN n = P.nonNegx,y⇒nonNegx*y (PG.natRealNonnegative 2)
  (P.nonNegx,y⇒nonNegx*y (PG.natRealNonnegative n) (PG.natRealNonnegative n))

triNN : ∀ n → R.NonNegative (T.tri n)
triNN zero = P.nonNeg0
triNN (suc n) = P.nonNegx,y⇒nonNegx+y
  (P.nonNegx,y⇒nonNegx*y (PG.natRealNonnegative 2)
    (P.nonNegx,y⇒nonNegx*y (PG.natRealNonnegative 2) (PG.natRealNonnegative n)))
  (triNN n)

triLeSquare : ∀ n → T.tri n ≤ squareBudget n
triLeSquare zero = P.nonNegx⇒0≤x (squareNN zero)
triLeSquare (suc n) =
  let w = NR.natReal n
      t = (D.two * (D.two * w)) + squareBudget n
      h : T.tri (suc n) ≤ t
      h = P.+-mono-≤ P.≤-refl (triLeSquare n)
      inc : t ≤ t + D.two
      inc = P.≤-respˡ-≃ (P.+-identityʳ t)
        (P.+-mono-≤ P.≤-refl (P.nonNegx⇒0≤x (PG.natRealNonnegative 2)))
      eq : (t + D.two) ≃ squareBudget (suc n)
      eq = P.≃-trans
        (let open P.ℝ-Solver in solve 1 (λ w →
          (Κ (+ 2 / 1) ⊗ (Κ (+ 2 / 1) ⊗ w) ⊕ Κ (+ 2 / 1) ⊗ (w ⊗ w)) ⊕ Κ (+ 2 / 1)
          ⊜ Κ (+ 2 / 1) ⊗ ((w ⊕ Κ 1ℚᵘ) ⊗ (w ⊕ Κ 1ℚᵘ))) P.≃-refl w)
        (P.*-congˡ (P.*-cong (P.≃-symm (NR.natRealSuccessor n))
                             (P.≃-symm (NR.natRealSuccessor n))))
  in P.≤-trans h (P.≤-respʳ-≃ eq inc)

module Shrink (outer inner : BishopComplex)
  (onz : Rec.BishopComplexNonzero outer) (inz : Rec.BishopComplexNonzero inner)
  (s : ℝ) (s0 : R.0ℝ ≤ s) (s1 : s < R.1ℝ)
  (upper : Upper.BishopComplexNormSquareUpperRadius (B.relative inner outer onz) s)
  (f : N.SeriesC) (outerEval : Eval.Eval outer f) where

  module S = First.Shrink outer inner onz inz s s0 s1 upper f outerEval
  g = S.g
  weight : Nat → ℝ
  weight n = PG.polynomialGeometricTerm s 2 n

  weightConv : Seq._isConvergent (Seq.SeriesOf weight)
  weightConv = PG.polynomialGeometricSeriesConvergent s 2 s0 s1

  weightNull : Seq._ConvergesTo_ weight R.0ℝ
  weightNull = Lim.seriesTermNull weight (proj₁ weightConv) (proj₂ weightConv)

  momentNN : ∀ n → R.NonNegative (T.moment g n)
  momentNN n = P.nonNegx,y⇒nonNegx*y
    (P.nonNegx,y⇒nonNegx+y (P.nonNeg∣x∣ _) (P.nonNeg∣x∣ _)) (triNN n)

  weightRead : ∀ n → ((NR.natReal n * NR.natReal n) * R.pow s n) ≃ weight n
  weightRead n = P.*-congʳ
    (P.≃-symm (P.*-congʳ (P.*-identityˡ (NR.natReal n))))

  secondMoment : Seq._isConvergent (Seq.SeriesOf (T.moment g))
  secondMoment with Seq.convergent⇒bounded (R.0ℝ , weightNull)
  ... | M , Seq.bound* hb =
    let scale = First.four * M
        scaled : Seq._isConvergent (Seq.SeriesOf (λ n → scale * S.Outer.budget n))
        scaled = _ , Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
          (λ {(suc n) → P.≃-symm (Tail.scalePrefix scale S.Outer.budget (suc n))})
          (_ , Conv.mulR (Const.constantConverges scale) (proj₂ S.Outer.budgetConvergent))
        bound : ∀ n → suc zero Nat.≤ n → ∣ T.moment g n ∣ ≤ scale * S.Outer.budget n
        bound zero ()
        bound (suc n) hn =
          let k = suc n
              w = NR.natReal k
              b = S.Outer.budget k
              p = R.pow s k
              weightLe = P.≤-respˡ-≃
                (P.≃-trans (P.nonNegx⇒∣x∣≃x (PG.polynomialGeometricTermNonnegative s0 2 k))
                  (P.≃-symm (weightRead k))) (hb k)
              triLe = P.*-monoˡ-≤-nonNeg (triLeSquare k)
                (P.nonNegx,y⇒nonNegx+y (P.nonNeg∣x∣ _) (P.nonNeg∣x∣ _))
              massLe = P.*-monoʳ-≤-nonNeg (S.massBound k) (squareNN k)
              read = let open P.ℝ-Solver in solve 3
                (λ b p w → (Κ (+ 2 / 1) ⊗ b ⊗ p) ⊗ (Κ (+ 2 / 1) ⊗ (w ⊗ w))
                  ⊜ (Κ (+ 4 / 1) ⊗ b) ⊗ ((w ⊗ w) ⊗ p)) P.≃-refl b p w
              monotone = P.*-monoˡ-≤-nonNeg weightLe
                (P.nonNegx,y⇒nonNegx*y (PG.natRealNonnegative 4) (S.budgetNN k))
              finish = let open P.ℝ-Solver in solve 2
                (λ b M → (Κ (+ 4 / 1) ⊗ b) ⊗ M ⊜ (Κ (+ 4 / 1) ⊗ M) ⊗ b) P.≃-refl b M
          in P.≤-respˡ-≃ (P.≃-symm (P.nonNegx⇒∣x∣≃x (momentNN k)))
            (P.≤-trans triLe (P.≤-trans (P.≤-respʳ-≃ read massLe)
              (P.≤-respʳ-≃ finish monotone)))
    in Seq.proposition-3-5 scaled (zero , bound)

  -- Both coefficients are evaluated from the same normalized actual
  -- source stream. The outer evaluation constructs both budgets.
  module Jet = T.TwoJet g S.momentSummable secondMoment

  inv : BishopComplex
  inv = Rec.reciprocalC inner inz

  firstCoefficient : ∀ q → S.Inside q → BishopComplex
  firstCoefficient q hq = Jet.First.D.value (S.normal q) (S.normal q)
    (S.normalUpper q hq) (S.normalUpper q hq)

  secondCoefficient : ∀ q → S.Inside q → BishopComplex
  secondCoefficient q hq = Jet.Second.value (S.normal q) (S.normal q) (S.normal q)
    (S.normalUpper q hq) (S.normalUpper q hq) (S.normalUpper q hq)

  -- Undo normalization by the actual affine coordinate. No independently
  -- chosen center, phase, or quotient. Taylor coefficient scales by inv^2.
  originalTwoJet : ∀ q (hq : S.Inside q) (v : Nat → BishopComplex) →
    (hv : ∀ n → S.Inside (v n)) → Lim.Conv v q →
    (eq : Eval.Eval q f) → (ev : ∀ n → Eval.Eval (v n) f) →
    J2.Jet2 (λ n → v n -C q) (λ n → Eval.value (ev n)) (Eval.value eq)
      (inv *C firstCoefficient q hq) (inv *C (inv *C secondCoefficient q hq))
  originalTwoJet q hq v hv cv eq ev =
    let delta = λ n → v n -C q
        dc = Lim.limitTransport (J.sameSub q) (Lim.subConv cv (Lim.constantC q))
        affine : J2.Jet2 delta (λ n → S.normal (v n)) (S.normal q) inv A.zeroC
        affine = record
          { J2.first = record
              { J.quotient = λ _ → inv
              ; J.factor = λ n → S.diffRead q (v n)
              ; J.limit = Lim.constantC inv }
          ; J2.second = J.constant delta inv }
        actual = Jet.actual (S.normal q) (S.normalUpper q hq) (λ n → S.normal (v n))
          (λ n → S.normalUpper (v n) (hv n))
          (Conv.mulConv cv (Lim.constantC inv))
          (S.normalEval q eq) (λ n → S.normalEval (v n) (ev n))
        composed = J2.compose dc affine actual
    in J2.cong2 (λ _ → C.≈C-refl _) (C.≈C-refl _) (C.≈C-refl _)
      (complexTrans (A.addCCongruent (L.complexMultiplyLeftZero _) (C.≈C-refl _))
        (L.complexAddLeftIdentity _)) composed
