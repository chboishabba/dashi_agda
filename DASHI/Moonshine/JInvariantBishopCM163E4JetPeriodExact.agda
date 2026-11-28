module DASHI.Moonshine.JInvariantBishopCM163E4JetPeriodExact where

-- SOURCE-WRITTEN, UNCOMPILED. Eliminate E2 at the terminal cut.
-- U is the actual coefficient jet 3 D E4, not a freely chosen value.
-- Derivative interpretation and actual CM identities remain producers.
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Moonshine.JInvariantBishopEisensteinEulerJetExact as Jets
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM
import DASHI.Moonshine.JInvariantBishopCM163RealSlicePeriodExact as Slice
import DASHI.Foundations.BishopChudnovskyNativeEulerLimitsExact as Euler
import DASHI.Foundations.BishopChudnovskyNativeFactorialLimitExact as F
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as N
import DASHI.Foundations.BishopChudnovskyNativePeriodProductExact as End
import DASHI.Foundations.BishopMachinArctanConstructionExact as M

X Y U : ℝ
X = CM.Selected.X
Y = CM.Selected.Y
module J = Jets.AtDisk CM.input
U = ((+ 3 / 1) ⋆) * C.re (J.e4EulerJet (suc zero))

V : ℝ
V = N.B * U + N.six * N.A * Y

-- E2 elimination is reversible as an equation substitution;
-- no proof of the Ramanujan identity is smuggled into the definition.
jetFlowCoordinate : (e : ℝ) → U ≃ (e * X - Y) →
  V ≃ (N.B * X * e - N.D * Y)
jetFlowCoordinate e hu =
  P.≃-trans (P.+-cong (P.*-congˡ hu) P.≃-refl)
    (let open P.ℝ-Solver in
      solve 3 (λ e x y →
        Κ (+ 545140134 / 1) ⊗ (e ⊗ x ⊖ y) ⊕
          Κ (+ 6 / 1) ⊗ Κ (+ 13591409 / 1) ⊗ y
        ⊜ Κ (+ 545140134 / 1) ⊗ x ⊗ e ⊖ Κ (+ 463591680 / 1) ⊗ y)
        P.≃-refl e X Y)

Flow : Set
Flow = (N.six * Y * Euler.J₁) ≃ (Euler.H * U)

Correction : Set
Correction = ((M.bishopMachinPi * N.r) * V) ≃ (N.six * N.B * X)

Cross : Set
Cross = ((N.p * N.r) * Y) ≃ (N.B * Euler.H * X)

weightedFlow : Flow → (N.six * Y * F.seriesReal) ≃ (Euler.H * V)
weightedFlow h =
  P.≃-trans (P.*-congˡ Euler.actualWeightedLimit)
    (P.≃-trans
      (let open P.ℝ-Solver in
        solve 3 (λ y f j →
          Κ (+ 6 / 1) ⊗ y ⊗ (Κ (+ 13591409 / 1) ⊗ f ⊕ Κ (+ 545140134 / 1) ⊗ j)
          ⊜ Κ (+ 81548454 / 1) ⊗ y ⊗ f ⊕ Κ (+ 545140134 / 1) ⊗
            (Κ (+ 6 / 1) ⊗ y ⊗ j)) P.≃-refl Y Euler.H Euler.J₁)
      (P.≃-trans (P.+-cong P.≃-refl (P.*-congˡ h))
        (let open P.ℝ-Solver in
          solve 3 (λ y f u →
            Κ (+ 81548454 / 1) ⊗ y ⊗ f ⊕ Κ (+ 545140134 / 1) ⊗ (f ⊗ u)
            ⊜ f ⊗ (Κ (+ 545140134 / 1) ⊗ u ⊕
              Κ (+ 6 / 1) ⊗ Κ (+ 13591409 / 1) ⊗ y))
            P.≃-refl Y Euler.H U)))

crossLeft : Flow →
  (N.six * ((N.p * N.r) * Y)) ≃ (Euler.H * ((M.bishopMachinPi * N.r) * V))
crossLeft h =
  P.≃-trans
    (let open P.ℝ-Solver in
      solve 4 (λ p s r y →
        Κ (+ 6 / 1) ⊗ (((p ⊗ s) ⊗ r) ⊗ y)
        ⊜ (p ⊗ r) ⊗ (Κ (+ 6 / 1) ⊗ y ⊗ s))
        P.≃-refl M.bishopMachinPi F.seriesReal N.r Y)
    (P.≃-trans (P.*-congˡ (weightedFlow h))
      (let open P.ℝ-Solver in
        solve 3 (λ a f v → a ⊗ (f ⊗ v) ⊜ f ⊗ (a ⊗ v))
          P.≃-refl (M.bishopMachinPi * N.r) Euler.H V))

crossRight : (Euler.H * (N.six * N.B * X)) ≃
  (N.six * (N.B * Euler.H * X))
crossRight = let open P.ℝ-Solver in
  solve 2 (λ f x →
    f ⊗ (Κ (+ 6 / 1) ⊗ Κ (+ 545140134 / 1) ⊗ x)
    ⊜ Κ (+ 6 / 1) ⊗ (Κ (+ 545140134 / 1) ⊗ f ⊗ x))
    P.≃-refl Euler.H X

correctionToCross : Flow → Correction → Cross
correctionToCross h hc = N.cancelLeft N.six N.sixPos
  (P.≃-trans (crossLeft h) (P.≃-trans (P.*-congˡ hc) crossRight))

-- Reverse solve: same signed cross reopens the correction, provided
-- the original H is strictly positive (not merely square nonnegative).
crossToCorrection : R.Positive Euler.H → Flow → Cross → Correction
crossToCorrection ph h hc = N.cancelLeft Euler.H ph
  (P.≃-trans (P.≃-symm (crossLeft h))
    (P.≃-trans (P.*-congˡ hc) (P.≃-symm crossRight)))

periodFromCubicAndE4Jet : R.Positive X → N.sq Euler.H ≃ X →
  N.sq Y ≃ (N.t * N.cube X) → Flow → Correction → End.NativePeriod
periodFromCubicAndE4Jet px hf hy h hc = N.squareToNativePeriod
  (N.normalizedSquare X Y Euler.H px hf hy (correctionToCross h hc))

-- No independent E2, no division by Y or new radical.
-- The guarded root route and the direct cubic route coexist.
periodFromRootAndE4Jet : (negative : R._<_ CM.Selected.d R.0ℝ) →
  R.Positive X →
  let module Root = CM.Selected.AtNegativeDelta negative in
  Root.j ≃ Slice.negC →
  N.sq Euler.H ≃ X → Flow → Correction → End.NativePeriod
periodFromRootAndE4Jet negative px hj hf h hc =
  periodFromCubicAndE4Jet px hf
    (CM.Selected.AtNegativeDelta.rootToCubic negative hj) h hc
