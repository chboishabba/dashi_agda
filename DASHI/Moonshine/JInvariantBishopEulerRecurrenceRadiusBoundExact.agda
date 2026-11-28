module DASHI.Moonshine.JInvariantBishopEulerRecurrenceRadiusBoundExact where

-- SOURCE-WRITTEN, kernel pending. A quantitative bound for *both*
-- normalized Delta solutions. Once the weighted driving-series prefix
-- mass is below a positive integer threshold, no coefficient beyond
-- the finite initial prefix can increase the uniform weighted bound.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Relation.Nullary using (yes; no)
import Real as R
open R using (ℝ; _≃_; _+_; _*_; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopNatEmbeddingMonotoneExact as Mono
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Analysis.BishopAbsoluteCauchyProductSpecializationExact as Abs
import DASHI.Moonshine.JInvariantBishopWeightedCauchyEvaluationExact as W
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
import DASHI.Moonshine.JInvariantBishopEulerDefectUniquenessExact as Pos
import DASHI.Moonshine.JInvariantBishopCM163HyperMajorantsExact as Order
import DASHI.Moonshine.JInvariantBishopLiteralRamanujanExact as Ram
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as D
open G

mass : Series → Nat → ℝ
mass f n = Seq.SeriesOf (λ k → ∣ f k ∣) n

massNN : ∀ f n → R.NonNegative (mass f n)
massNN f zero = P.nonNeg0
massNN f (suc n) = P.nonNegx,y⇒nonNegx+y (massNN f n) (P.nonNeg∣x∣ (f n))

termBelowMass : ∀ f n k → k ≤ n → R._≤_ ∣ f k ∣ (mass f (suc n))
termBelowMass f zero zero h =
  P.≤-respʳ-≃ (P.≃-symm (P.+-identityˡ ∣ f zero ∣)) P.≤-refl
termBelowMass f zero (suc k) ()
termBelowMass f (suc n) k h with k NP.≟ suc n
... | yes refl = P.≤-respˡ-≃ (P.+-identityˡ ∣ f (suc n) ∣)
  (P.+-mono-≤ (P.nonNegx⇒0≤x (massNN f (suc n))) P.≤-refl)
... | no ne = P.≤-respˡ-≃ (P.+-identityʳ ∣ f k ∣)
  (P.+-mono-≤ (termBelowMass f n k (NP.≤-pred (NP.≤∧≢⇒< h ne)))
    (P.nonNegx⇒0≤x (P.nonNeg∣x∣ (f (suc n)))))

-- Bound a Cauchy row using a uniform bound ONLY on the degrees read
-- from its second factor. The bound itself never consumes a future
-- coefficient of that factor.
rowUniform : ∀ a f C n →
  (∀ k → k ≤ n → R._≤_ ∣ f k ∣ C) →
  R._≤_ (Abs.conv (Abs.abs a) (Abs.abs f) n) (mass a (suc n) * C)
rowUniform a f C zero h =
  P.≤-respˡ-≃ (P.≃-symm (Row.cauchyCoefficientZero (Abs.abs a) (Abs.abs f)))
    (P.≤-respʳ-≃ (P.*-congʳ (P.≃-symm (P.+-identityˡ ∣ a zero ∣)))
      (P.*-monoˡ-≤-nonNeg (P.nonNeg∣x∣ (a zero)) (h zero z≤n)))
rowUniform a f C (suc n) h =
  P.≤-respˡ-≃ (P.≃-symm (Row.cauchyCoefficientSuccessor (Abs.abs a) (Abs.abs f) n))
    (P.≤-respʳ-≃
      (P.≃-trans (P.≃-symm (P.*-distribʳ-+ C ∣ a zero ∣ (mass (Row.shift a) (suc n))))
        (P.*-congʳ (P.≃-symm (massHead a (suc n)))))
      (P.+-mono-≤
        (P.*-monoˡ-≤-nonNeg (P.nonNeg∣x∣ (a zero)) (h (suc n) NP.≤-refl))
        (rowUniform (Row.shift a) f C n (λ k hk → h k (NP.≤-step hk)))))
  where
  massHead : ∀ a n → mass a (suc n) ≃ (∣ a zero ∣ + mass (Row.shift a) n)
  massHead a zero = P.≃-trans (P.+-identityˡ _) (P.≃-symm (P.+-identityʳ _))
  massHead a (suc n) = P.≃-trans (P.+-cong (massHead a n) P.≃-refl)
    (P.+-assoc _ _ _)

module Uniform
  (a f : Series) (M : Nat) (B : ℝ)
  (recurrence : ∀ n → NR.natReal (suc n) * f (suc n) ≃ Abs.conv a f n)
  (massBound : ∀ n → R._≤_ (mass a (suc n)) B)
  (threshold : R._≤_ B (NR.natReal (suc M))) where

  C : ℝ
  C = mass f (suc M)

  initial : ∀ k → k ≤ M → R._≤_ ∣ f k ∣ C
  initial k hk = termBelowMass f M k hk

  step : ∀ n → M ≤ n → (∀ k → k ≤ n → R._≤_ ∣ f k ∣ C) →
    R._≤_ ∣ f (suc n) ∣ C
  step n hM h =
    let d = NR.natReal (suc n)
        pos = Pos.positiveNat n
        absRead = P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ d (f (suc n)))
          (P.*-congʳ (P.nonNegx⇒∣x∣≃x (P.pos⇒nonNeg pos)))
        eq = P.≃-trans (P.≃-symm absRead) (P.∣-∣-cong (recurrence n))
        bnd = P.≤-trans (Abs.rowBound a f n)
          (P.≤-trans (rowUniform a f C n h)
            (P.*-monoʳ-≤-nonNeg
              (P.≤-trans (massBound n) (P.≤-trans threshold (Mono.natRealMonotone (s≤s hM))))
              (massNN f (suc M))))
    in Order.cancelOrder d pos (P.≤-respˡ-≃ (P.≃-symm eq) bnd)

  prefix : ∀ n k → k ≤ n → R._≤_ ∣ f k ∣ C
  prefix zero zero h = initial zero z≤n
  prefix zero (suc k) ()
  prefix (suc n) k hk with k NP.≟ suc n
  ... | yes refl with suc n NP.≤? M
  ...   | yes h = initial (suc n) h
  ...   | no h = step n (NP.≤-pred (NP.<⇒≤ (NP.≰⇒> h))) (prefix n)
  prefix (suc n) k hk | no h = prefix n k (NP.≤-pred (NP.≤∧≢⇒< hk h))

  all : ∀ n → R._≤_ ∣ f n ∣ C
  all n = prefix n n NP.≤-refl

-- Actual radius-scaled recurrence on the existing real weighted Cauchy
-- ring. No inverse of the radius is needed for this transport.
weightedFlow : ∀ rho a f → a zero ≃ R.0ℝ →
  F.δ f ≈s (a ⊗s f) → ∀ n →
  NR.natReal (suc n) * W.weighted rho f (suc n) ≃
    Abs.conv (Row.shift (W.weighted rho a)) (W.weighted rho f) n
weightedFlow rho a f a0 flow n =
  let d = NR.natReal (suc n)
      p = R.pow rho (suc n)
      z = f (suc n)
      w0 : W.weighted rho a zero ≃ R.0ℝ
      w0 = U.right0 a0
  in P.≃-trans (let open P.ℝ-Solver in solve 3
    (λ d p z → d ⊗ (p ⊗ z) ⊜ p ⊗ (d ⊗ z)) P.≃-refl d p z)
    (P.≃-trans (P.*-congˡ (P.≃-trans (P.≃-symm (Ram.dPositive f n)) (flow (suc n))))
      (P.≃-trans (P.≃-symm (W.weightedCauchy rho a f (suc n)))
        (U.zeroHead (W.weighted rho a) (W.weighted rho f) w0 n)))

negativeFlow : F.δ D.reciprocal ≈s (neg D.Eplus ⊗s D.reciprocal)
negativeFlow = transS D.inverseFlow (let open G.Solver in solve 2
  (λ a v → ⊝ (a ⊗ v) ⊜ (⊝ a) ⊗ v) reflS D.Eplus D.reciprocal)

negative0 : neg D.Eplus zero ≃ R.0ℝ
negative0 = P.≃-trans (P.-‿cong D.Eplus0) (P.≃-symm P.0≃-0)

module AtRadius (rho B : ℝ) (M : Nat)
  (massPlus : ∀ n → R._≤_ (mass (Row.shift (W.weighted rho D.Eplus)) (suc n)) B)
  (massMinus : ∀ n → R._≤_ (mass (Row.shift (W.weighted rho (neg D.Eplus))) (suc n)) B)
  (threshold : R._≤_ B (NR.natReal (suc M))) where
  module U0 = Uniform (Row.shift (W.weighted rho D.Eplus)) (W.weighted rho D.unit) M B
    (weightedFlow rho D.Eplus D.unit D.Eplus0 D.unitFlow) massPlus threshold
  module V0 = Uniform (Row.shift (W.weighted rho (neg D.Eplus))) (W.weighted rho D.reciprocal) M B
    (weightedFlow rho (neg D.Eplus) D.reciprocal negative0 negativeFlow) massMinus threshold
  unitBound : ∀ n → R._≤_ ∣ W.weighted rho D.unit n ∣ U0.C
  unitBound = U0.all
  inverseBound : ∀ n → R._≤_ ∣ W.weighted rho D.reciprocal n ∣ V0.C
  inverseBound = V0.all
