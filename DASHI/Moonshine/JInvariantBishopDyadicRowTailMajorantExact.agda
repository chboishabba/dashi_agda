module DASHI.Moonshine.JInvariantBishopDyadicRowTailMajorantExact where

-- SOURCE-WRITTEN, UNCOMPILED. Actual signed half-angle gap estimate.
-- An integer-tail cell supplies u >= 0, theta = +/-u, u <= 2,
-- and h*j <= 2*u/3. The lower bound is then rho0*h²*j².
-- These are geometric range inputs, not analytic domination assumptions.
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Inverse as I
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopPositiveCrossReciprocalUpperExact as Cross
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopSinePositiveTwoBallFromCubicExact as SinLower
import DASHI.Analysis.BishopImaginaryProductPythagoreanReuseExact as Trig
import DASHI.Analysis.BishopMachinCayleyNativeProductFirstZeroExact as Native
import DASHI.Analysis.BishopOriginalMachinAtanSmallPhaseExact as Bounds
import DASHI.Foundations.BishopSquareNonnegativeExact as Sq
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpOrder
import DASHI.Foundations.BishopExponentialCauchyProductExact as ExpProduct
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as ExpCong
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as Cong
import DASHI.Analysis.BishopOriginalNonnegativeNegativeExpBoundExact as NegExp
import DASHI.Physics.YangMills.BalabanBishopSineTwoBallCubicLowerExact as TwoBall
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as Parity
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopCenteredDyadicSummandLimitExact as Leaf
import DASHI.Moonshine.JInvariantBishopDyadicScaledRowLimitExact as S
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as Row
import DASHI.Moonshine.JInvariantBishopFourierRowRationalExact as Rat
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open C using (BishopComplex; _≈C_)
open A using (_*C_; _+C_; scaleC; powC)
open Comp using (complexTrans; complexSym)

square = Norm.square

squareMono : ∀ {a b} → R.NonNegative a → a ≤ b → square a ≤ square b
squareMono an le = P.*-mono-≤ an an le le

plusNN : ∀ {a b} → R.NonNegative b → a ≤ a + b
plusNN {a} bn = P.≤-respˡ-≃ (P.≃-symm (P.+-identityʳ a))
  (P.+-mono-≤ P.≤-refl (P.nonNegx⇒0≤x bn))

cancelPositive : ∀ {a b c} → R._<_ R.0ℝ a → (a * b) ≤ (a * c) → b ≤ c
cancelPositive {a} {b} {c} pos le =
  let i = Cross.positiveInverse pos
      law = I.*-inverseʳ a (Cross.positiveNonzero pos)
      cancel : ∀ x → (a * x) * i ≃ x
      cancel x = P.≃-trans
        (let open P.ℝ-Solver in solve 3 (λ a x i → (a ⊗ x) ⊗ i ⊜ (a ⊗ i) ⊗ x) P.≃-refl a x i)
        (P.≃-trans (P.*-congʳ law) (P.*-identityˡ x))
  in P.≤-respʳ-≃ (cancel c)
    (P.≤-respˡ-≃ (P.≃-symm (cancel b))
      (P.*-monoʳ-≤-nonNeg le (Cross.positiveInverseNonnegative pos)))

-- Uniform radial floor on 0 <= u <= a, derived from the original
-- positive exponential tail and its native additive product.
negativeExpFloor : ∀ a u → R.NonNegative a → R.NonNegative u → u ≤ a →
  Exp.bishopExp (R.- a) ≤ Exp.bishopExp (R.- u)
negativeExpFloor a u an un ua =
  let d = a - u
      dn = P.0≤x⇒nonNegx (P.≤-respʳ-≃
        (let open P.ℝ-Solver in solve 2 (λ a u → a ⊕ (⊝ u) ⊜ a ⊖ u) P.≃-refl a u)
        (P.≤-respˡ-≃ (P.+-inverseʳ u) (P.+-mono-≤ ua P.≤-refl)))
      r = Exp.bishopExp (R.- a)
      rNN = P.pos⇒nonNeg (P.0<x⇒posx (NegExp.originalNegativeExpPositiveForNonnegative a an))
      eq = let open P.ℝ-Solver in solve 2
        (λ a u → (⊝ a) ⊕ (a ⊖ u) ⊜ ⊝ u) P.≃-refl a u
  in P.≤-respˡ-≃ (P.≃-symm (P.*-identityʳ r))
    (P.≤-respʳ-≃
      (P.≃-trans (P.≃-symm (ExpProduct.bishopExpAdd (R.- a) d)) (ExpCong.bishopExpCongruent eq))
      (P.*-monoˡ-≤-nonNeg (ExpOrder.bishopExpAtLeastOneOnNonnegative dn) rNN))

module At (inputs : Round11.BishopCutset) where
  module Rw = D.At inputs
  sin = Trig.sinB inputs
  cos = Trig.cosB inputs
  product = Native.originalNativeImaginaryExpProduct inputs

  sinLower : ∀ u → R.NonNegative u → ∣ u ∣ ≤ TwoBall.bishopTwo →
    (TwoBall.bishopOneThird * u) ≤ sin u
  sinLower u un inside = P.≤-trans
    (P.≤-respˡ-≃ (P.*-comm TwoBall.bishopOneThird u)
      (P.≤-respʳ-≃ (P.≃-symm (SinLower.cubicSineLowerFactors u))
        (P.*-monoˡ-≤-nonNeg (SinLower.oneThirdBelowSineFactor u un inside) un)))
    (TwoBall.sineCubicLowerTwoBall record
      { termIdentification = Round11.concreteTermIdentification inputs
      ; valueNonnegative = un
      ; insideTwo = inside })

  signedSinSquare : ∀ t u → (t ≃ u) ⊎ (t ≃ R.- u) →
    square (sin t) ≃ square (sin u)
  signedSinSquare t u (inj₁ eq) =
    let e = Cong.bishopSinCongruent (Round11.concreteTermIdentification inputs) eq
    in P.*-cong e e
  signedSinSquare t u (inj₂ eq) =
    let e = P.≃-trans (Cong.bishopSinCongruent (Round11.concreteTermIdentification inputs) eq)
          (Parity.bishopSinNeg (Round11.round11ParityInputs inputs) u)
    in P.≃-trans (P.*-cong e e)
      (let open P.ℝ-Solver in solve 1 (λ s → (⊝ s) ⊗ (⊝ s) ⊜ s ⊗ s) P.≃-refl (sin u))

  cosDouble : ∀ t → cos (t + t) ≃ (R.1ℝ - ((+ 2 / 1) ⋆) * square (sin t))
  cosDouble t =
    let add = proj₂ (Cartesian.imaginaryExponentialProductGivesAddition Rw.T t t (product t t))
        unit = Trig.round11PythagoreanFromImaginaryProduct inputs product t
    in P.≃-trans add
      (P.≃-trans
        (let open P.ℝ-Solver in solve 2
          (λ c s → c ⊗ c ⊖ s ⊗ s ⊜ (c ⊗ c ⊕ s ⊗ s) ⊖ Κ (+ 2 / 1) ⊗ (s ⊗ s))
          P.≃-refl (cos t) (sin t))
        (P.+-cong unit P.≃-refl))

  -- Literal Cartesian phase, with radius not silently set to one.
  phase : ℝ → ℝ → BishopComplex
  phase rho t = C.complex (rho * cos (t + t)) (rho * sin (t + t))

  gapNorm : ∀ rho t → Norm.normSqC (Row.gapMinus (phase rho t)) ≃
    (square (R.1ℝ - rho) + ((+ 4 / 1) ⋆) * rho * square (sin t))
  gapNorm rho t =
    let c = cos (t + t)
        s = sin (t + t)
        p = sin t
        unit = Trig.round11PythagoreanFromImaginaryProduct inputs product (t + t)
    in P.≃-trans
      (let open P.ℝ-Solver in solve 3
        (λ r c s → (Κ 1ℚᵘ ⊖ r ⊗ c) ⊗ (Κ 1ℚᵘ ⊖ r ⊗ c)
          ⊕ (Κ 0ℚᵘ ⊖ r ⊗ s) ⊗ (Κ 0ℚᵘ ⊖ r ⊗ s)
          ⊜ (Κ 1ℚᵘ ⊖ Κ (+ 2 / 1) ⊗ r ⊗ c) ⊕ (r ⊗ r) ⊗ (c ⊗ c ⊕ s ⊗ s))
        P.≃-refl rho c s)
      (P.≃-trans (P.+-cong
          (P.+-cong P.≃-refl (P.-‿cong (P.*-congˡ (cosDouble t))))
          (P.*-congˡ unit))
        (let open P.ℝ-Solver in solve 2
          (λ r p → (Κ 1ℚᵘ ⊖ Κ (+ 2 / 1) ⊗ r ⊗ (Κ 1ℚᵘ ⊖ Κ (+ 2 / 1) ⊗ (p ⊗ p)))
            ⊕ (r ⊗ r) ⊗ Κ 1ℚᵘ
            ⊜ (Κ 1ℚᵘ ⊖ r) ⊗ (Κ 1ℚᵘ ⊖ r) ⊕ Κ (+ 4 / 1) ⊗ r ⊗ (p ⊗ p))
          P.≃-refl rho p))

  -- h*J <= (2/3)*u is the centred signed lattice distance estimate.
  -- It implies h*J <= 2*sin(u), so no loss of the negative sheet.
  gapLower : ∀ rho rho0 t u h J →
    R.NonNegative rho0 → rho0 ≤ rho → R.NonNegative u →
    ∣ u ∣ ≤ TwoBall.bishopTwo → (t ≃ u) ⊎ (t ≃ R.- u) →
    R.NonNegative (h * J) →
    (h * J) ≤ ((+ 2 / 3) ⋆) * u →
    (rho0 * square (h * J)) ≤ Norm.normSqC (Row.gapMinus (phase rho t))
  gapLower rho rho0 t u h J r0n r0r un inside sign hjNN dist =
    let s = sin u
        lo = sinLower u un inside
        twoS = ((+ 2 / 1) ⋆) * s
        hjTwoS = P.≤-trans dist
          (P.≤-respˡ-≃
            (let open P.ℝ-Solver in solve 1
              (λ u → Κ (+ 2 / 3) ⊗ u ⊜ Κ (+ 2 / 1) ⊗ (Κ (+ 1 / 3) ⊗ u))
              P.≃-refl u)
            (P.*-monoˡ-≤-nonNeg lo Bounds.twoNN))
        raw = P.*-mono-≤ r0n (Sq.bishopSquareNonnegative (h * J)) r0r
                (squareMono hjNN hjTwoS)
        signed = P.*-congˡ (P.≃-symm (signedSinSquare t u sign))
        radial = square (R.1ℝ - rho)
        expr = ((+ 4 / 1) ⋆) * rho * square (sin t)
    in P.≤-trans
      (P.≤-respʳ-≃
        (P.≃-trans
          (let open P.ℝ-Solver in solve 2
            (λ r s → r ⊗ ((Κ (+ 2 / 1) ⊗ s) ⊗ (Κ (+ 2 / 1) ⊗ s))
              ⊜ Κ (+ 4 / 1) ⊗ r ⊗ (s ⊗ s)) P.≃-refl rho s) signed) raw)
      (P.≤-respʳ-≃ (P.≃-symm (gapNorm rho t))
        (P.≤-respʳ-≃ (P.+-comm expr radial) (plusNN (Sq.bishopSquareNonnegative (R.1ℝ - rho)))))

-- Algebraic bridge from the gap estimate to the actual scaled inverse.
-- No evaluation of the unscaled inverse at h=0.
scaledInverseBound : ∀ q (nz : Rec.BishopComplexNonzero (Row.gapMinus q)) h b →
  R._<_ R.0ℝ h → R.NonNegative b →
  square h ≤ b * Norm.normSqC (Row.gapMinus q) →
  Norm.normSqC (scaleC (R.- h) (Rec.reciprocalC (Row.gapMinus q) nz)) ≤ b
scaledInverseBound q nz h b hp bn cross =
  let g = Row.gapMinus q
      i = Rec.reciprocalC g nz
      v = scaleC (R.- h) i
      d = Norm.normSqC g
      law = Inv.normInverse g i (Rec.multiplyReciprocal g nz)
      raw = P.*-monoʳ-≤-nonNeg cross (Inv.normNN i)
      left = P.≃-trans (Rec.normSquareScale (R.- h) i)
        (P.*-congʳ (let open P.ℝ-Solver in solve 1
          (λ h → (⊝ h) ⊗ (⊝ h) ⊜ h ⊗ h) P.≃-refl h))
      right = P.≃-trans (P.*-assoc b d (Norm.normSqC i))
        (P.≃-trans (P.*-congˡ law) (P.*-identityʳ b))
  in P.≤-respʳ-≃ right (P.≤-respˡ-≃ left raw)
