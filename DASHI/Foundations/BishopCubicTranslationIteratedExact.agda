module DASHI.Foundations.BishopCubicTranslationIteratedExact where

------------------------------------------------------------------------
-- ITERATED CUBIC TRANSLATION
--
-- The one-step theorem gives, for z>=0 and x>0,
--
--   D3(x) * exp(z) <= exp(z+x).
--
-- With q=D3(x)^-1 this becomes
--
--   exp(z) <= q * exp(z+x).
--
-- Iterating yields
--
--   exp(z) <= q^r * exp(z + r*x).
--
-- This is the exact translation law needed by the Erdos residual estimate and
-- does not use global exp-additivity.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialCubicTranslationLowerExact as Cubic
import DASHI.Foundations.BishopCubicTranslationGeometricRatioExact as Ratio
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Geometric
open import DASHI.Physics.YangMills.CompactLieProofLevel

natScale : Nat → BishopReal.ℝ → BishopReal.ℝ
natScale zero x = BishopReal.0ℝ
natScale (suc n) x = BishopReal._+_ (natScale n x) x

natScaleNonnegative :
  ∀ {x} → BishopReal.NonNegative x →
  ∀ n → BishopReal.NonNegative (natScale n x)
natScaleNonnegative xNN zero = BishopP.nonNeg-refl
natScaleNonnegative xNN (suc n) =
  BishopP.nonNegx,y⇒nonNegx+y
    (natScaleNonnegative xNN n) xNN

shiftedBase : BishopReal.ℝ → BishopReal.ℝ → Nat → BishopReal.ℝ
shiftedBase z x n = BishopReal._+_ z (natScale n x)

shiftedBaseNonnegative :
  ∀ {z x} → BishopReal.NonNegative z → BishopReal.NonNegative x →
  ∀ n → BishopReal.NonNegative (shiftedBase z x n)
shiftedBaseNonnegative zNN xNN n =
  BishopP.nonNegx,y⇒nonNegx+y zNN (natScaleNonnegative xNN n)

shiftedBaseSuccessor :
  ∀ z x n →
  BishopReal._≃_
    (shiftedBase z x (suc n))
    (BishopReal._+_ (shiftedBase z x n) x)
shiftedBaseSuccessor z x n =
  let open BishopP.ℝ-Solver
  in solve 3
    (λ z′ r′ x′ →
      z′ ⊕ (r′ ⊕ x′) ⊜ (z′ ⊕ r′) ⊕ x′)
    BishopP.≃-refl z (natScale n x) x

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
    xNN = BishopP.pos⇒nonNeg (BishopP.0<x⇒posx xPositive)
    qx = Ratio.q x xPositive
    d = Ratio.d3 x
    translated = Cubic.cubicTranslationLower zNN xNN
    qPositive = BishopP.0<x⇒posx (Ratio.qPositive xPositive)
    scaled = BishopP.*-monoˡ-≤-nonNeg translated
      (BishopP.pos⇒nonNeg qPositive)
    inverseLaw =
      importInverseLaw d (Ratio.d3Nonzero xPositive)
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
  where
    import Inverse as BishopInverse
    importInverseLaw :
      (value : BishopReal.ℝ) →
      (nonzero : BishopReal._≄0 value) →
      BishopReal._≃_
        (BishopReal._*_
          (BishopInverse._⁻¹ value nonzero) value)
        BishopReal.1ℝ
    importInverseLaw = BishopInverse.*-inverseˡ

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
    scaledNext =
      BishopP.*-monoˡ-≤-nonNeg
        nextStep
        (powerQNonnegative xPositive r)
    middle :
      BishopReal._≤_
        (BishopReal._*_ qr
          (Exp.bishopExp (shiftedBase z x r)))
        (BishopReal._*_ qr
          (BishopReal._*_ qx
            (Exp.bishopExp
              (BishopReal._+_ (shiftedBase z x r) x))))
    middle = scaledNext
    normalize :
      BishopReal._≃_
        (BishopReal._*_ qr
          (BishopReal._*_ qx
            (Exp.bishopExp
              (BishopReal._+_ (shiftedBase z x r) x))))
        (BishopReal._*_
          (powerQ xPositive (suc r))
          (Exp.bishopExp (shiftedBase z x (suc r))))
    normalize =
      let open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 4
          (λ qr′ q′ e′ dummy → qr′ ⊗ (q′ ⊗ e′) ⊜ (qr′ ⊗ q′) ⊗ e′)
          BishopP.≃-refl qr qx
          (Exp.bishopExp
            (BishopReal._+_ (shiftedBase z x r) x))
          BishopReal.0ℝ)
        (BishopP.*-cong
          BishopP.≃-refl
          (Exp.bishopExpCongruent
            (BishopP.≃-symm (shiftedBaseSuccessor z x r))))
  in
  BishopP.≤-respʳ-≃ normalize
    (BishopP.≤-trans current middle)

bishopCubicTranslationIteratedLevel : ProofLevel
bishopCubicTranslationIteratedLevel = machineChecked
