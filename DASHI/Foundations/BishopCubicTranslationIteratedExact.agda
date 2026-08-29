module DASHI.Foundations.BishopCubicTranslationIteratedExact where

------------------------------------------------------------------------
-- ITERATED CUBIC TRANSLATION
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; _/_)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialCubicTranslationLowerExact as Cubic
import DASHI.Foundations.BishopCubicTranslationGeometricRatioExact as Ratio
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Geometric
import DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact as NatEmbed
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Repeated addition and canonical Nat embedding.

natReal : Nat → BishopReal.ℝ
natReal n = Exp.embed (NatEmbed.natAsRational n)

natScale : Nat → BishopReal.ℝ → BishopReal.ℝ
natScale zero x = BishopReal.0ℝ
natScale (suc n) x = BishopReal._+_ (natScale n x) x

natRealSuccessor : ∀ n →
  BishopReal._≃_
    (natReal (suc n))
    (BishopReal._+_ (natReal n) BishopReal.1ℝ)
natRealSuccessor n =
  BishopP.≃-trans
    (BishopP.⋆-cong (NatEmbed.natAsRationalSuccessor n))
    (BishopP.⋆-distrib-+
      (NatEmbed.natAsRational n)
      (+ 1 / 1))

natRealMul : ∀ left right →
  BishopReal._≃_
    (natReal (left * right))
    (BishopReal._*_ (natReal left) (natReal right))
natRealMul left right =
  BishopP.≃-trans
    (BishopP.⋆-cong (NatEmbed.natAsRationalMul left right))
    (BishopP.⋆-distrib-*
      (NatEmbed.natAsRational left)
      (NatEmbed.natAsRational right))

natScaleAsEmbeddedNatMul : ∀ n x →
  BishopReal._≃_
    (natScale n x)
    (BishopReal._*_ (natReal n) x)
natScaleAsEmbeddedNatMul zero x =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ x′ → Κ 0ℚᵘ ⊜ Κ 0ℚᵘ ⊗ x′)
    BishopP.≃-refl x
natScaleAsEmbeddedNatMul (suc n) x =
  BishopP.≃-trans
    (BishopP.+-cong
      (natScaleAsEmbeddedNatMul n x)
      BishopP.≃-refl)
    (BishopP.≃-trans
      (let open BishopP.ℝ-Solver
       in solve 2
         (λ nr x′ →
           (nr ⊗ x′) ⊕ x′
           ⊜ (nr ⊕ Κ (+ 1 / 1)) ⊗ x′)
         BishopP.≃-refl (natReal n) x)
      (BishopP.*-congʳ
        (BishopP.≃-symm (natRealSuccessor n))))

nestedNatScaleProduct : ∀ outer inner x →
  BishopReal._≃_
    (natScale outer (natScale inner x))
    (natScale (outer * inner) x)
nestedNatScaleProduct outer inner x =
  BishopP.≃-trans
    (natScaleAsEmbeddedNatMul outer (natScale inner x))
    (BishopP.≃-trans
      (BishopP.*-congˡ
        (natScaleAsEmbeddedNatMul inner x))
      (BishopP.≃-trans
        (let open BishopP.ℝ-Solver
         in solve 3
           (λ outer′ inner′ x′ →
             outer′ ⊗ (inner′ ⊗ x′)
             ⊜ (outer′ ⊗ inner′) ⊗ x′)
           BishopP.≃-refl (natReal outer) (natReal inner) x)
        (BishopP.≃-trans
          (BishopP.*-congʳ
            (BishopP.≃-symm (natRealMul outer inner)))
          (BishopP.≃-symm
            (natScaleAsEmbeddedNatMul (outer * inner) x)))))

natScalePositiveSuccessor :
  ∀ {x} → BishopReal.Positive x →
  ∀ n → BishopReal.Positive (natScale (suc n) x)
natScalePositiveSuccessor xPositive zero =
  BishopP.pos-cong
    (BishopP.≃-symm (BishopP.+-identityˡ x))
    xPositive
natScalePositiveSuccessor xPositive (suc n) =
  BishopP.posx,y⇒posx+y
    (natScalePositiveSuccessor xPositive n)
    xPositive

------------------------------------------------------------------------
-- Recursive translation state.

shiftedBase : BishopReal.ℝ → BishopReal.ℝ → Nat → BishopReal.ℝ
shiftedBase z x zero = z
shiftedBase z x (suc n) =
  BishopReal._+_ (shiftedBase z x n) x

shiftedBaseAsNatScale : ∀ z x n →
  BishopReal._≃_
    (shiftedBase z x n)
    (BishopReal._+_ z (natScale n x))
shiftedBaseAsNatScale z x zero =
  BishopP.≃-symm (BishopP.+-identityʳ z)
shiftedBaseAsNatScale z x (suc n) =
  BishopP.≃-trans
    (BishopP.+-cong
      (shiftedBaseAsNatScale z x n)
      BishopP.≃-refl)
    (BishopP.≃-symm
      (BishopP.+-assoc z (natScale n x) x))

shiftedBaseNonnegative :
  ∀ {z x} → BishopReal.NonNegative z → BishopReal.NonNegative x →
  ∀ n → BishopReal.NonNegative (shiftedBase z x n)
shiftedBaseNonnegative zNN xNN zero = zNN
shiftedBaseNonnegative zNN xNN (suc n) =
  BishopP.nonNegx,y⇒nonNegx+y
    (shiftedBaseNonnegative zNN xNN n) xNN

------------------------------------------------------------------------
-- One-step and iterated cubic translation.

oneStepReciprocalTranslation :
  ∀ {z x} →
  (zNN : BishopReal.NonNegative z) →
  (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  BishopReal._≤_
    (Exp.bishopExp z)
    (BishopReal._*_
      (Ratio.q x xPositive)
      (Exp.bishopExp (BishopReal._+_ z x)))
oneStepReciprocalTranslation {z} {x} zNN xPositive =
  let
    qx = Ratio.q x xPositive
    d = Ratio.d3 x
    translated =
      Cubic.cubicTranslationLower
        zNN
        (BishopP.pos⇒nonNeg (BishopP.0<x⇒posx xPositive))
    scaled =
      BishopP.*-monoˡ-≤-nonNeg translated
        (BishopP.pos⇒nonNeg
          (BishopP.0<x⇒posx (Ratio.qPositive xPositive)))
    inverseLaw =
      BishopInverse.*-inverseˡ d (Ratio.d3Nonzero xPositive)
    leftCancel :
      BishopReal._≃_
        (BishopReal._*_ qx
          (BishopReal._*_ d (Exp.bishopExp z)))
        (Exp.bishopExp z)
    leftCancel =
      let open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 3
          (λ q′ d′ e′ → q′ ⊗ (d′ ⊗ e′) ⊜ (q′ ⊗ d′) ⊗ e′)
          BishopP.≃-refl qx d (Exp.bishopExp z))
        (BishopP.≃-trans
          (BishopP.*-congʳ inverseLaw)
          (BishopP.*-identityˡ (Exp.bishopExp z)))
  in
  BishopP.≤-respˡ-≃ leftCancel scaled

powerQ :
  ∀ {x} → BishopReal._<_ BishopReal.0ℝ x → Nat → BishopReal.ℝ
powerQ {x} xPositive n = BishopReal.pow (Ratio.q x xPositive) n

powerQNonnegative :
  ∀ {x} (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  ∀ n → BishopReal.NonNegative (powerQ xPositive n)
powerQNonnegative xPositive =
  Geometric.ratioPowerNonnegative (Ratio.cubicRatioInputs xPositive)

iteratedCubicTranslation :
  ∀ {z x} →
  (zNN : BishopReal.NonNegative z) →
  (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  ∀ r →
  BishopReal._≤_
    (Exp.bishopExp z)
    (BishopReal._*_
      (powerQ xPositive r)
      (Exp.bishopExp (shiftedBase z x r)))
iteratedCubicTranslation {z} {x} zNN xPositive zero =
  BishopP.≤-reflexive
    (BishopP.≃-symm
      (BishopP.*-identityˡ (Exp.bishopExp z)))
iteratedCubicTranslation {z} {x} zNN xPositive (suc r) =
  let
    xNN = BishopP.pos⇒nonNeg (BishopP.0<x⇒posx xPositive)
    qr = powerQ xPositive r
    qx = Ratio.q x xPositive
    current = iteratedCubicTranslation zNN xPositive r
    nextStep =
      oneStepReciprocalTranslation
        (shiftedBaseNonnegative zNN xNN r)
        xPositive
    middle =
      BishopP.*-monoˡ-≤-nonNeg
        nextStep
        (powerQNonnegative xPositive r)
    normalize :
      BishopReal._≃_
        (BishopReal._*_ qr
          (BishopReal._*_ qx
            (Exp.bishopExp (shiftedBase z x (suc r)))))
        (BishopReal._*_
          (powerQ xPositive (suc r))
          (Exp.bishopExp (shiftedBase z x (suc r))))
    normalize =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ qr′ q′ e′ → qr′ ⊗ (q′ ⊗ e′) ⊜ (qr′ ⊗ q′) ⊗ e′)
        BishopP.≃-refl qr qx
        (Exp.bishopExp (shiftedBase z x (suc r)))
  in
  BishopP.≤-respʳ-≃ normalize
    (BishopP.≤-trans current middle)

bishopCubicTranslationIteratedLevel : ProofLevel
bishopCubicTranslationIteratedLevel = machineChecked
