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
--   exp(z) <= q^r * exp(z_r),
--   z_0=z, z_{r+1}=z_r+x.
--
-- This is the exact translation law needed by the Erdos residual estimate and
-- does not use global exp-additivity.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialCubicTranslationLowerExact as Cubic
import DASHI.Foundations.BishopCubicTranslationGeometricRatioExact as Ratio
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Geometric
open import DASHI.Physics.YangMills.CompactLieProofLevel

shiftedBase : BishopReal.ℝ → BishopReal.ℝ → Nat → BishopReal.ℝ
shiftedBase z x zero = z
shiftedBase z x (suc n) =
  BishopReal._+_ (shiftedBase z x n) x

shiftedBaseNonnegative :
  ∀ {z x} → BishopReal.NonNegative z → BishopReal.NonNegative x →
  ∀ n → BishopReal.NonNegative (shiftedBase z x n)
shiftedBaseNonnegative zNN xNN zero = zNN
shiftedBaseNonnegative zNN xNN (suc n) =
  BishopP.nonNegx,y⇒nonNegx+y
    (shiftedBaseNonnegative zNN xNN n) xNN

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
