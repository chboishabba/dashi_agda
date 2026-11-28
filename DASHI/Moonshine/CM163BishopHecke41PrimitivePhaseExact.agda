module DASHI.Moonshine.CM163BishopHecke41PrimitivePhaseExact where

-- SOURCE-WRITTEN, kernel pending. Use the original native Machin
-- sine-sign proof, including its locatedness and quarter-angle donor.
-- No algebraic primitive-root assumption and no numerical phase test.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin as Fin using (Fin)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (ℚᵘ; _/_; 0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
open import Data.Product.Base using (_,_; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Nullary.Decidable.Core using (from-yes)
import Real as R
open R using (ℝ; 0ℝ; _⋆; _*_; _+_; _≃_; _<_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as NZ
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopSetoidComplexExact as Exp
import DASHI.Analysis.BishopMachinPiGlobalSineSignFromTwoBallExact as Sign
import DASHI.Analysis.BishopOriginalMachinCayleyEndpointExact as Endpoint
import DASHI.Analysis.BishopImaginaryProductPythagoreanReuseExact as Product
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as MP
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open A using (_-C_; powC)
open Comp using (complexTrans; complexSym)

module At (inputs : Round11.BishopCutset) where
  module Rm = Ram.At inputs
  module Ph = Rm.Ph

  quarter = Endpoint.originalQuarterEquality inputs
  sine = Product.sinB inputs
  sign = Sign.round11SinePositiveBeforeMachinPi inputs Ph.product quarter

  gap : Nat → C.BishopComplex
  gap k = powC Rm.zeta k -C A.oneC

  angleRead : ∀ k x → C.im (Rm.rotation k) ≃ x →
    C.im (gap k) ≃ sine x
  angleRead k x h =
    P.≃-trans (let open P.ℝ-Solver in solve 1 (λ x → x ⊖ Κ 0ℚᵘ ⊜ x) P.≃-refl (C.im (powC Rm.zeta k)))
      (proj₂ (complexTrans (Rm.phaseRead k)
        (complexTrans (Rm.expCong (P.≃-refl , h))
          (Weld.originalExpEquivalenceToSeries (Exp.expImaginaryIsTrigPair Ph.T x)))))

  positiveAngle : ∀ c → Q._<_ 0ℚᵘ c → 0ℝ < ((c ⋆) * Phase.pi)
  positiveAngle c h = J.positiveMul (P.p<q⇒p⋆<q⋆ 0ℚᵘ c h) MP.machinPiPositive

  belowPi : ∀ c → Q._<_ c 1ℚᵘ → ((c ⋆) * Phase.pi) < Phase.pi
  belowPi c h = P.<-respʳ-≃ (P.*-identityˡ Phase.pi)
    (P.*-monoʳ-<-pos (P.0<x⇒posx MP.machinPiPositive) (P.p<q⇒p⋆<q⋆ c 1ℚᵘ h))

  small : ∀ k c → Q._<_ 0ℚᵘ c → Q._<_ c 1ℚᵘ →
    C.im (Rm.rotation k) ≃ ((c ⋆) * Phase.pi) → Rec.BishopComplexNonzero (gap k)
  small k c hc hd h = NZ.complexNonzeroFromImagApart
    (inj₂ (P.<-respʳ-≃ (P.≃-symm (angleRead k ((c ⋆) * Phase.pi) h))
      (sign ((c ⋆) * Phase.pi) (positiveAngle c hc) (belowPi c hd))))

  large : ∀ k c → Q._<_ 0ℚᵘ c → Q._<_ c 1ℚᵘ →
    C.im (Rm.rotation k) ≃ (((c ⋆) * Phase.pi) + Phase.pi) →
    Rec.BishopComplexNonzero (gap k)
  large k c hc hd h =
    let x = (c ⋆) * Phase.pi
        read = P.≃-trans (angleRead k (x + Phase.pi) h)
          (Product.round11SineShiftByMachinPi inputs Ph.product quarter x)
    in NZ.complexNonzeroFromImagApart (inj₁
      (P.<-respˡ-≃ (P.≃-symm read)
        (NZ.positiveNegatesNegative (sign x (positiveAngle c hc) (belowPi c hd)))))

  -- Each entry is one exact rational angle in (0,pi) or pi+(0,pi).
  -- The 40 cases cover the actual nontrivial phases, not sampled points.
  primitive : ∀ (i : Fin 40) → Rec.BishopComplexNonzero (gap (suc (Fin.toℕ i)))
  primitive (Fin.zero) = small 1 (+ 2 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 2 / 41))) (from-yes ((+ 2 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 1 / 1))
        ⊜ Κ (+ 2 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.zero)) = small 2 (+ 4 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 4 / 41))) (from-yes ((+ 4 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 2 / 1))
        ⊜ Κ (+ 4 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.zero))) = small 3 (+ 6 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 6 / 41))) (from-yes ((+ 6 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 3 / 1))
        ⊜ Κ (+ 6 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))) = small 4 (+ 8 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 8 / 41))) (from-yes ((+ 8 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 4 / 1))
        ⊜ Κ (+ 8 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))) = small 5 (+ 10 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 10 / 41))) (from-yes ((+ 10 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 5 / 1))
        ⊜ Κ (+ 10 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))) = small 6 (+ 12 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 12 / 41))) (from-yes ((+ 12 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 6 / 1))
        ⊜ Κ (+ 12 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))) = small 7 (+ 14 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 14 / 41))) (from-yes ((+ 14 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 7 / 1))
        ⊜ Κ (+ 14 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))) = small 8 (+ 16 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 16 / 41))) (from-yes ((+ 16 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 8 / 1))
        ⊜ Κ (+ 16 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))) = small 9 (+ 18 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 18 / 41))) (from-yes ((+ 18 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 9 / 1))
        ⊜ Κ (+ 18 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))) = small 10 (+ 20 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 20 / 41))) (from-yes ((+ 20 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 10 / 1))
        ⊜ Κ (+ 20 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))) = small 11 (+ 22 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 22 / 41))) (from-yes ((+ 22 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 11 / 1))
        ⊜ Κ (+ 22 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))) = small 12 (+ 24 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 24 / 41))) (from-yes ((+ 24 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 12 / 1))
        ⊜ Κ (+ 24 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))) = small 13 (+ 26 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 26 / 41))) (from-yes ((+ 26 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 13 / 1))
        ⊜ Κ (+ 26 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))) = small 14 (+ 28 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 28 / 41))) (from-yes ((+ 28 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 14 / 1))
        ⊜ Κ (+ 28 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))) = small 15 (+ 30 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 30 / 41))) (from-yes ((+ 30 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 15 / 1))
        ⊜ Κ (+ 30 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))) = small 16 (+ 32 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 32 / 41))) (from-yes ((+ 32 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 16 / 1))
        ⊜ Κ (+ 32 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))) = small 17 (+ 34 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 34 / 41))) (from-yes ((+ 34 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 17 / 1))
        ⊜ Κ (+ 34 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))) = small 18 (+ 36 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 36 / 41))) (from-yes ((+ 36 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 18 / 1))
        ⊜ Κ (+ 36 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))) = small 19 (+ 38 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 38 / 41))) (from-yes ((+ 38 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 19 / 1))
        ⊜ Κ (+ 38 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))) = small 20 (+ 40 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 40 / 41))) (from-yes ((+ 40 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 20 / 1))
        ⊜ Κ (+ 40 / 41) ⊗ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))))) = large 21 (+ 1 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 1 / 41))) (from-yes ((+ 1 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 21 / 1))
        ⊜ Κ (+ 1 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))))) = large 22 (+ 3 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 3 / 41))) (from-yes ((+ 3 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 22 / 1))
        ⊜ Κ (+ 3 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))))))) = large 23 (+ 5 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 5 / 41))) (from-yes ((+ 5 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 23 / 1))
        ⊜ Κ (+ 5 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))))))) = large 24 (+ 7 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 7 / 41))) (from-yes ((+ 7 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 24 / 1))
        ⊜ Κ (+ 7 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))))))))) = large 25 (+ 9 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 9 / 41))) (from-yes ((+ 9 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 25 / 1))
        ⊜ Κ (+ 9 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))))))))) = large 26 (+ 11 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 11 / 41))) (from-yes ((+ 11 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 26 / 1))
        ⊜ Κ (+ 11 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))))))))))) = large 27 (+ 13 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 13 / 41))) (from-yes ((+ 13 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 27 / 1))
        ⊜ Κ (+ 13 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))))))))))) = large 28 (+ 15 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 15 / 41))) (from-yes ((+ 15 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 28 / 1))
        ⊜ Κ (+ 15 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))))))))))))) = large 29 (+ 17 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 17 / 41))) (from-yes ((+ 17 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 29 / 1))
        ⊜ Κ (+ 17 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))))))))))))) = large 30 (+ 19 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 19 / 41))) (from-yes ((+ 19 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 30 / 1))
        ⊜ Κ (+ 19 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))))))))))))))) = large 31 (+ 21 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 21 / 41))) (from-yes ((+ 21 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 31 / 1))
        ⊜ Κ (+ 21 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))))))))))))))) = large 32 (+ 23 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 23 / 41))) (from-yes ((+ 23 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 32 / 1))
        ⊜ Κ (+ 23 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))))))))))))))))) = large 33 (+ 25 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 25 / 41))) (from-yes ((+ 25 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 33 / 1))
        ⊜ Κ (+ 25 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))))))))))))))))) = large 34 (+ 27 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 27 / 41))) (from-yes ((+ 27 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 34 / 1))
        ⊜ Κ (+ 27 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))))))))))))))))))) = large 35 (+ 29 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 29 / 41))) (from-yes ((+ 29 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 35 / 1))
        ⊜ Κ (+ 29 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))))))))))))))))))) = large 36 (+ 31 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 31 / 41))) (from-yes ((+ 31 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 36 / 1))
        ⊜ Κ (+ 31 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))))))))))))))))))))) = large 37 (+ 33 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 33 / 41))) (from-yes ((+ 33 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 37 / 1))
        ⊜ Κ (+ 33 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))))))))))))))))))))) = large 38 (+ 35 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 35 / 41))) (from-yes ((+ 35 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 38 / 1))
        ⊜ Κ (+ 35 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero))))))))))))))))))))))))))))))))))))))) = large 39 (+ 37 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 37 / 41))) (from-yes ((+ 37 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 39 / 1))
        ⊜ Κ (+ 37 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
  primitive (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.zero)))))))))))))))))))))))))))))))))))))))) = large 40 (+ 39 / 41)
    (from-yes (0ℚᵘ QP.<? (+ 39 / 41))) (from-yes ((+ 39 / 41) QP.<? 1ℚᵘ))
    (let open P.ℝ-Solver in solve 1
      (λ p → (Κ (+ 2 / 1) ⊗ p) ⊗ (Κ (+ 1 / 41) ⊗ Κ (+ 40 / 1))
        ⊜ Κ (+ 39 / 41) ⊗ p ⊕ p) P.≃-refl Phase.pi)
