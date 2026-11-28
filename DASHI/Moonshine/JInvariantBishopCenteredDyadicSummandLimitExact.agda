module DASHI.Moonshine.JInvariantBishopCenteredDyadicSummandLimitExact where

-- SOURCE-WRITTEN, UNCOMPILED.
-- Fixed integer j in the original upper-half-plane carrier. Discharge
-- the directional nonzero guard, size envelope, dyadic null sequence,
-- and q-gap guard from the existing native source owners.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_)
open import Data.Rational.Unnormalised as Q using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁)
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _+_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Data.Rational.Unnormalised.Properties as QP
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as One
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as NZ
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Analysis.BishopOriginalMachinAtanSmallPhaseExact as Bounds
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as RealPow
import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as Pi
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopCenteredDyadicAddressExact as Addr
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowExact as Chart
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as Row
import DASHI.Moonshine.JInvariantBishopDyadicScaledRowLimitExact as S
import DASHI.Moonshine.JInvariantBishopFourierRowRationalExact as Rat
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (scaleC)
open Comp using (complexTrans; complexSym)
open Chart using (h; weight)

hPow : ∀ n → h n ≃ R.pow D.half n
hPow zero = P.≃-refl
hPow (suc n) = P.*-congʳ (hPow n)

positiveProduct : ∀ {a b : ℝ} → R._<_ R.0ℝ a → R._<_ R.0ℝ b → R._<_ R.0ℝ (a * b)
positiveProduct a b = P.posx⇒0<x (P.posx,y⇒posx*y (P.0<x⇒posx a) (P.0<x⇒posx b))

halfNN : R.NonNegative D.half
halfNN = P.pos⇒nonNeg (P.0<x⇒posx D.halfPositive)

hPositive : ∀ n → R._<_ R.0ℝ (h n)
hPositive zero = One.onePositive
hPositive (suc n) = positiveProduct (hPositive n) D.halfPositive

hNN : ∀ n → R.NonNegative (h n)
hNN n = P.pos⇒nonNeg (P.0<x⇒posx (hPositive n))

hSmall : ∀ n → ∣ h n ∣ ≤ R.1ℝ
hSmall n = P.≤-respˡ-≃ (P.≃-trans (P.nonNegx⇒∣x∣≃x (hNN n)) (hPow n))
  (P.≤-respʳ-≃ (RealPow.oneToAnyNatPower n)
    (Seq.x≤y∧nonNegx⇒xⁿ≤yⁿ n Bounds.half≤one halfNN))

hNull : Seq._ConvergesTo_ h R.0ℝ
hNull = Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
  (λ {(suc n) → P.≃-symm (hPow (suc n))})
  (R.0ℝ , Seq.∣r∣<1⇒rⁿ→0
    (P.<-respˡ-≃ (P.nonNegx⇒∣x∣≃x halfNN) Exp.halfBelowOne))

weight4 : ∀ n → weight ((+ 1 / 16) ⋆) n ≃ S.fourthR (h n)
weight4 zero = let open P.ℝ-Solver in solve 0
  (Κ 1ℚᵘ ⊜ (Κ 1ℚᵘ ⊗ Κ 1ℚᵘ) ⊗ (Κ 1ℚᵘ ⊗ Κ 1ℚᵘ)) P.≃-refl
weight4 (suc n) = P.≃-trans (P.*-congˡ (weight4 n))
  (let open P.ℝ-Solver in solve 1
    (λ a → Κ (+ 1 / 16) ⊗ ((a ⊗ a) ⊗ (a ⊗ a))
      ⊜ ((a ⊗ Κ (+ 1 / 2)) ⊗ (a ⊗ Κ (+ 1 / 2))) ⊗
         ((a ⊗ Κ (+ 1 / 2)) ⊗ (a ⊗ Κ (+ 1 / 2)))) P.≃-refl (h n))

weight6 : ∀ n → weight ((+ 1 / 64) ⋆) n ≃ S.sixthR (h n)
weight6 zero = let open P.ℝ-Solver in solve 0
  (Κ 1ℚᵘ ⊜ ((Κ 1ℚᵘ ⊗ Κ 1ℚᵘ) ⊗ (Κ 1ℚᵘ ⊗ Κ 1ℚᵘ)) ⊗
    (Κ 1ℚᵘ ⊗ Κ 1ℚᵘ)) P.≃-refl
weight6 (suc n) = P.≃-trans (P.*-congˡ (weight6 n))
  (let open P.ℝ-Solver in solve 1
    (λ a → Κ (+ 1 / 64) ⊗ (((a ⊗ a) ⊗ (a ⊗ a)) ⊗ (a ⊗ a))
      ⊜ (((a ⊗ Κ (+ 1 / 2)) ⊗ (a ⊗ Κ (+ 1 / 2))) ⊗
          ((a ⊗ Κ (+ 1 / 2)) ⊗ (a ⊗ Κ (+ 1 / 2)))) ⊗
         ((a ⊗ Κ (+ 1 / 2)) ⊗ (a ⊗ Κ (+ 1 / 2)))) P.≃-refl (h n))

scaleCong : ∀ {a b : ℝ} {z w : BishopComplex} →
  a ≃ b → z ≈C w → scaleC a z ≈C scaleC b w
scaleCong {z = C.complex _ _} {w = C.complex _ _} eq (re , im) =
  P.*-cong eq re , P.*-cong eq im

radius : BishopComplex → ℝ
radius z = ∣ C.re z ∣ + ∣ C.im z ∣

upperRadius : ∀ z → Upper.BishopComplexNormSquareUpperRadius z (radius z)
upperRadius (C.complex a b) = record
  { radiusNonnegative = P.nonNegx,y⇒nonNegx+y (P.nonNeg∣x∣ a) (P.nonNeg∣x∣ b)
  ; normSqBelowRadiusSquare = bound
  }
  where
  x = ∣ a ∣
  y = ∣ b ∣
  nonneg = P.nonNegx,y⇒nonNegx*y (P.nonNeg∣x∣ a) (P.nonNeg∣x∣ b)
  bound : (a * a + b * b) ≤ (x + y) * (x + y)
  bound = P.≤-respˡ-≃ (P.+-cong (P.≃-symm (Norm.absoluteSquare a))
                                  (P.≃-symm (Norm.absoluteSquare b)))
    (P.≤-respʳ-≃
      (let open P.ℝ-Solver in solve 2
        (λ x y → (x ⊗ x ⊕ y ⊗ y) ⊕ (x ⊗ y ⊕ x ⊗ y)
          ⊜ (x ⊕ y) ⊗ (x ⊕ y)) P.≃-refl x y)
      (P.≤-respˡ-≃ (P.≃-symm (P.+-identityʳ (x * x + y * y)))
        (P.+-mono-≤ P.≤-refl
          (P.nonNegx⇒0≤x (P.nonNegx,y⇒nonNegx+y nonneg nonneg)))))

shifted : U.BishopUpperHalfPlanePoint → ℤ → U.BishopUpperHalfPlanePoint
shifted p j = U.bishop-upper-half-plane-point
  (C.complex (C.re (U.tau p) + K.embedInteger j) (C.im (U.tau p)))
  (U.imaginaryPositive p)

scaledPoint : U.BishopUpperHalfPlanePoint → ℤ → Nat → U.BishopUpperHalfPlanePoint
scaledPoint p j n = U.bishop-upper-half-plane-point
  (scaleC (h n) (U.tau (shifted p j)))
  (positiveProduct (hPositive n) (U.imaginaryPositive p))

module At (inputs : Round11.BishopCutset) where
  module Rows = D.At inputs

  exponentCong : ∀ p q → U.tau p ≈C U.tau q → Rows.exponent p ≈C Rows.exponent q
  exponentCong p q (re , im) = P.-‿cong (P.*-congˡ im) , P.*-congˡ re

  qCong : ∀ p q → U.tau p ≈C U.tau q → Rows.q p ≈C Rows.q q
  qCong p q eq = Weld.originalBishopExpOnSeriesCongruent Rows.T (exponentCong p q eq)

  row4Cong : ∀ p q → U.tau p ≈C U.tau q → Rows.row4 p ≈C Rows.row4 q
  row4Cong p q eq = D.P4Cong (D.XC (Rows.gapNZ p) (Rows.gapNZ q) (qCong p q eq))

  row6Cong : ∀ p q → U.tau p ≈C U.tau q → Rows.row6 p ≈C Rows.row6 q
  row6Cong p q eq = D.P6Cong (D.XC (Rows.gapNZ p) (Rows.gapNZ q) (qCong p q eq))

  module Fixed (p : U.BishopUpperHalfPlanePoint) (j : ℤ) where
    z = Rows.exponent (shifted p j)
    directionNZ : Rec.BishopComplexNonzero z
    directionNZ = NZ.complexNonzeroFromRealApart (inj₁
      (NZ.positiveNegatesNegative
        (positiveProduct (positiveProduct twoPositive Pi.machinPiPositive)
          (U.imaginaryPositive p))))
      where
      twoPositive : R._<_ R.0ℝ D.two
      twoPositive = P.p<q⇒p⋆<q⋆ Q.0ℚᵘ (+ 2 / 1)
        (QP.positive⁻¹ (+ 2 / 1))


    exponentScale : ∀ n → Rows.exponent (scaledPoint p j n) ≈C scaleC (h n) z
    exponentScale n =
      (let open P.ℝ-Solver in solve 3
        (λ h p y → ⊝ ((Κ (+ 2 / 1) ⊗ p) ⊗ (h ⊗ y))
          ⊜ h ⊗ (⊝ ((Κ (+ 2 / 1) ⊗ p) ⊗ y))) P.≃-refl
        (h n) D.pi (C.im (U.tau p)))
      ,
      (let open P.ℝ-Solver in solve 3
        (λ h p x → (Κ (+ 2 / 1) ⊗ p) ⊗ (h ⊗ x)
          ⊜ h ⊗ ((Κ (+ 2 / 1) ⊗ p) ⊗ x)) P.≃-refl
        (h n) D.pi (C.re (U.tau (shifted p j))))

    expRead : ∀ n → Rows.q (scaledPoint p j n) ≈C
      Weld.originalBishopExpOnSeries Rows.T (scaleC (h n) z)
    expRead n = Weld.originalBishopExpOnSeriesCongruent Rows.T (exponentScale n)

    gap : ∀ n → Rec.BishopComplexNonzero
      (Row.gapMinus (Weld.originalBishopExpOnSeries Rows.T (scaleC (h n) z)))
    gap n = D.guardCong (D.gapCong (expRead n)) (Rows.gapNZ (scaledPoint p j n))

    module Limit = S.AtDirection Rows.T z directionNZ (radius z) (upperRadius z)
      h hSmall hNull gap

    row4Read : ∀ n → scaleC (weight ((+ 1 / 16) ⋆) n) (Rows.row4 (scaledPoint p j n)) ≈C Limit.scaled4 n
    row4Read n = scaleCong (weight4 n) (D.P4Cong
      (D.XC (Rows.gapNZ (scaledPoint p j n)) (gap n) (expRead n)))

    row6Read : ∀ n → scaleC (weight ((+ 1 / 64) ⋆) n) (Rows.row6 (scaledPoint p j n)) ≈C Limit.scaled6 n
    row6Read n = scaleCong (weight6 n) (D.P6Cong
      (D.XC (Rows.gapNZ (scaledPoint p j n)) (gap n) (expRead n)))

    actualLimit4 : Lim.Conv
      (λ n → scaleC (weight ((+ 1 / 16) ⋆) n) (Rows.row4 (scaledPoint p j n)))
      (Row.scale 6 (Rat.square (S.square Limit.V)))
    actualLimit4 = Lim.convTransport (λ n → complexSym (row4Read n)) Limit.limit4

    actualLimit6 : Lim.Conv
      (λ n → scaleC (weight ((+ 1 / 64) ⋆) n) (Rows.row6 (scaledPoint p j n)))
      (Row.scale 120 (Rat.cube (S.square Limit.V)))
    actualLimit6 = Lim.convTransport (λ n → complexSym (row6Read n)) Limit.limit6

  -- The actual finite tree summand is the corresponding fixed-integer
  -- family at that depth, with the same sign and zero index.
  leaf4 : ∀ {n} (r : Addr.SignedIndex n) p →
    scaleC (weight ((+ 1 / 16) ⋆) (suc n)) (Rows.row4 (Chart.walk (Addr.uncenter r) p))
    ≈C scaleC (weight ((+ 1 / 16) ⋆) (suc n))
      (Rows.row4 (scaledPoint p (Addr.integerRead r) (suc n)))
  leaf4 {n} r p = A.scaleCCongruent
    (row4Cong _ _ (Chart.centeredChart r p)) (weight ((+ 1 / 16) ⋆) (suc n))

  leaf6 : ∀ {n} (r : Addr.SignedIndex n) p →
    scaleC (weight ((+ 1 / 64) ⋆) (suc n)) (Rows.row6 (Chart.walk (Addr.uncenter r) p))
    ≈C scaleC (weight ((+ 1 / 64) ⋆) (suc n))
      (Rows.row6 (scaledPoint p (Addr.integerRead r) (suc n)))
  leaf6 {n} r p = A.scaleCCongruent
    (row6Cong _ _ (Chart.centeredChart r p)) (weight ((+ 1 / 64) ⋆) (suc n))
