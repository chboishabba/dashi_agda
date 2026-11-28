module DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact where

-- SOURCE-WRITTEN, UNCOMPILED. Native terminal elimination of the signed
-- CM163 correction, following Paper9SignedCMPeriod.lean at 204c52d2.
-- All hypotheses refer to the original CM slice; no claim that the
-- analytic producers of these equations have yet been transported.
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as QP
open import Data.Sum.Base using (inj₂)
open import Data.Nat.Base using (s≤s; z≤n)
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆)
import RealProperties as P
import Inverse as Inv
import DASHI.Foundations.BishopNonnegativeSquareReflectionExact as Reflect
import DASHI.Foundations.BishopNatSquareRootRegularFloorExact as Root
import DASHI.Foundations.BishopNatSquareRootSemanticSquareExact as RootSq
import DASHI.Foundations.BishopNatSquareRootPositiveExact as RootPos
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Foundations.BishopMachinPiRationalWindowExact as MW
import DASHI.Foundations.BishopChudnovskyNativeFactorialLimitExact as F
import DASHI.Foundations.BishopChudnovskyNativePeriodProductExact as End

sq : ℝ → ℝ
sq x = x * x

cube : ℝ → ℝ
cube x = (x * x) * x

A B D six t a b : ℝ
A = (+ 13591409 / 1) ⋆
B = (+ 545140134 / 1) ⋆
D = (+ 463591680 / 1) ⋆
six = (+ 6 / 1) ⋆
t = (+ 262537412640769728 / 262537412640768000) ⋆
a = (+ 42793598260445465664 / 262537412640768000) ⋆
b = (+ 297177765697537956 / 1) ⋆

r : ℝ
r = Root.canonicalFloorSquareRootReal 163

p : ℝ
p = M.bishopMachinPi * F.seriesReal

sixPos : R.Positive six
sixPos = P.posp⇒posp⋆ (+ 6 / 1) (QP.positive⁻¹ (+ 6 / 1))

aPos : R.Positive a
aPos = P.posp⇒posp⋆ (+ 42793598260445465664 / 262537412640768000)
  (QP.positive⁻¹ (+ 42793598260445465664 / 262537412640768000))

cancelRight : (v : ℝ) → R.Positive v → ∀ {x y : ℝ} →
  (x * v) ≃ (y * v) → x ≃ y
cancelRight v pv {x} {y} h =
  P.≃-trans (P.≃-symm (cancel x))
    (P.≃-trans (P.*-congʳ h) (cancel y))
  where
  apart : R._≄0 v
  apart = inj₂ (P.posx⇒0<x pv)
  inv = Inv._⁻¹ v apart
  cancel : (z : ℝ) → ((z * v) * inv) ≃ z
  cancel z = P.≃-trans (P.*-assoc z v inv)
    (P.≃-trans (P.*-congˡ (Inv.*-inverseʳ v apart)) (P.*-identityʳ z))

cancelLeft : (v : ℝ) → R.Positive v → ∀ {x y : ℝ} →
  (v * x) ≃ (v * y) → x ≃ y
cancelLeft v pv {x} {y} h = cancelRight v pv
  (P.≃-trans (P.*-comm x v) (P.≃-trans h (P.*-comm v y)))

cancelCube : (x : ℝ) → R.Positive x → ∀ {u v : ℝ} →
  (u * cube x) ≃ (v * cube x) → u ≃ v
cancelCube x px {u} {v} h = cancelRight x px (cancelRight x px
  (cancelRight x px (P.≃-trans (P.≃-symm (assoc u))
    (P.≃-trans h (assoc v)))))
  where
  assoc : (z : ℝ) → (z * cube x) ≃ (((z * x) * x) * x)
  assoc z = let open P.ℝ-Solver in
    solve 2 (λ z x → z ⊗ ((x ⊗ x) ⊗ x) ⊜ ((z ⊗ x) ⊗ x) ⊗ x)
      P.≃-refl z x

-- Signed first Euler equation, after clearing the positive denominator Y.
-- The sign of E X - Y must not be replaced by its magnitude.
weightedFlow : (x y e f j : ℝ) →
  (six * y * j) ≃ (f * (e * x - y)) →
  (six * y * (A * f + B * j)) ≃ (f * (B * x * e - D * y))
weightedFlow x y e f j h = let open P.ℝ-Solver in
  P.≃-trans
    (solve 3 (λ y f j →
      Κ (+ 6 / 1) ⊗ y ⊗ (Κ (+ 13591409 / 1) ⊗ f ⊕ Κ (+ 545140134 / 1) ⊗ j)
      ⊜ Κ (+ 81548454 / 1) ⊗ y ⊗ f ⊕ Κ (+ 545140134 / 1) ⊗
        (Κ (+ 6 / 1) ⊗ y ⊗ j)) P.≃-refl y f j)
    (P.≃-trans (P.+-cong P.≃-refl (P.*-congˡ h))
      (solve 4 (λ y f e x →
        Κ (+ 81548454 / 1) ⊗ y ⊗ f ⊕ Κ (+ 545140134 / 1) ⊗
          (f ⊗ ((e ⊗ x) ⊖ y))
        ⊜ f ⊗ ((Κ (+ 545140134 / 1) ⊗ x ⊗ e) ⊖
          (Κ (+ 463591680 / 1) ⊗ y))) P.≃-refl y f e x))

-- This derives the signed period cross, not its square. The correction
-- is the actual (X/Y)(E-3/p_Lean)=D/B, multiplied by B Y pi sqrt(163).
signedCross : (x y e f j : ℝ) →
  F.seriesReal ≃ (A * f + B * j) →
  (six * y * j) ≃ (f * (e * x - y)) →
  ((M.bishopMachinPi * r) * (B * x * e - D * y)) ≃ (six * B * x) →
  ((p * r) * y) ≃ (B * f * x)
signedCross x y e f j hs hj hc = cancelLeft six sixPos
  (P.≃-trans left (P.≃-trans middle (P.≃-trans right
    (P.≃-trans (P.*-congˡ hc) finish))))
  where
  left : (six * ((p * r) * y)) ≃
    ((M.bishopMachinPi * r) * (six * y * F.seriesReal))
  left = let open P.ℝ-Solver in
    solve 4 (λ m s r y → Κ (+ 6 / 1) ⊗ (((m ⊗ s) ⊗ r) ⊗ y)
      ⊜ (m ⊗ r) ⊗ (Κ (+ 6 / 1) ⊗ y ⊗ s))
      P.≃-refl M.bishopMachinPi F.seriesReal r y
  middle : ((M.bishopMachinPi * r) * (six * y * F.seriesReal)) ≃
    ((M.bishopMachinPi * r) * (f * (B * x * e - D * y)))
  middle = P.*-congˡ (P.≃-trans (P.*-congˡ hs) (weightedFlow x y e f j hj))
  right : ((M.bishopMachinPi * r) * (f * (B * x * e - D * y))) ≃
    (f * ((M.bishopMachinPi * r) * (B * x * e - D * y)))
  right = let open P.ℝ-Solver in
    solve 3 (λ u f v → u ⊗ (f ⊗ v) ⊜ f ⊗ (u ⊗ v))
      P.≃-refl (M.bishopMachinPi * r) f (B * x * e - D * y)
  finish : (f * (six * B * x)) ≃ (six * (B * f * x))
  finish = let open P.ℝ-Solver in
    solve 2 (λ f x → f ⊗ (Κ (+ 6 / 1) ⊗ Κ (+ 545140134 / 1) ⊗ x)
      ⊜ Κ (+ 6 / 1) ⊗ (Κ (+ 545140134 / 1) ⊗ f ⊗ x))
      P.≃-refl f x

-- Use the actual canonical sqrt(163), not a new ratio square root.
-- Squaring only occurs AFTER the signed cross has been supplied.
normalizedSquare : (x y f : ℝ) → R.Positive x →
  sq f ≃ x → sq y ≃ (t * cube x) →
  ((p * r) * y) ≃ (B * f * x) →
  (a * sq p) ≃ b
normalizedSquare x y f px hf hy cross = cancelCube x px
  (P.≃-trans (P.≃-symm left) (P.≃-trans
    (P.*-cong cross cross) right))
  where
  left : sq ((p * r) * y) ≃ ((a * sq p) * cube x)
  left = let open P.ℝ-Solver in
    P.≃-trans
      (solve 3 (λ p r y → ((p ⊗ r) ⊗ y) ⊗ ((p ⊗ r) ⊗ y)
        ⊜ ((p ⊗ p) ⊗ (r ⊗ r)) ⊗ (y ⊗ y))
        P.≃-refl p r y)
      (P.≃-trans
        (P.*-cong (P.*-congˡ (RootSq.canonicalFloorSquareRootSquaresToNat 163)) hy)
        (solve 2 (λ p x →
          ((p ⊗ p) ⊗ Κ (+ 163 / 1)) ⊗
            (Κ (+ 262537412640769728 / 262537412640768000) ⊗ ((x ⊗ x) ⊗ x))
          ⊜ (Κ (+ 42793598260445465664 / 262537412640768000) ⊗ (p ⊗ p))
            ⊗ ((x ⊗ x) ⊗ x)) P.≃-refl p x))
  right : sq (B * f * x) ≃ (b * cube x)
  right = let open P.ℝ-Solver in
    P.≃-trans
      (solve 2 (λ f x →
        (Κ (+ 545140134 / 1) ⊗ f ⊗ x) ⊗ (Κ (+ 545140134 / 1) ⊗ f ⊗ x)
        ⊜ Κ (+ 297177765697537956 / 1) ⊗ ((f ⊗ f) ⊗ (x ⊗ x)))
        P.≃-refl f x)
      (P.≃-trans (P.*-congˡ (P.*-congʳ hf))
        (solve 1 (λ x → Κ (+ 297177765697537956 / 1) ⊗ (x ⊗ (x ⊗ x))
          ⊜ Κ (+ 297177765697537956 / 1) ⊗ ((x ⊗ x) ⊗ x))
          P.≃-refl x))

targetSquare : (a * sq End.target) ≃ b
targetSquare = let open P.ℝ-Solver in
  P.≃-trans
    (solve 1 (λ u →
      Κ (+ 42793598260445465664 / 262537412640768000) ⊗
        ((Κ (+ 426880 / 1) ⊗ u) ⊗ (Κ (+ 426880 / 1) ⊗ u))
      ⊜ Κ (+ 42793598260445465664 / 262537412640768000) ⊗
        (Κ (+ 182226534400 / 1) ⊗ (u ⊗ u))) P.≃-refl End.sqrtReal)
    (P.≃-trans (P.*-congˡ (P.*-congˡ
      (RootSq.canonicalFloorSquareRootSquaresToNat 10005)))
      (solve 0 (Κ (+ 42793598260445465664 / 262537412640768000) ⊗
        (Κ (+ 182226534400 / 1) ⊗ Κ (+ 10005 / 1)) ⊜
        Κ (+ 297177765697537956 / 1)) P.≃-refl))

pNN : R.NonNegative p
pNN = P.nonNegx,y⇒nonNegx*y
  (P.0≤x⇒nonNegx (P.<⇒≤ (P.<-trans
    (P.p<q⇒p⋆<q⋆ Q.0ℚᵘ MW.three (QP.positive⁻¹ MW.three))
    MW.threeBelowMachinPi)))
  (P.0≤x⇒nonNegx (P.<⇒≤ (P.posx⇒0<x F.seriesPositive)))

targetNN : R.NonNegative End.target
targetNN = P.nonNegx,y⇒nonNegx*y
  (P.0≤x⇒nonNegx (P.<⇒≤ (P.posx⇒0<x
    (P.posp⇒posp⋆ End.KQ (QP.positive⁻¹ End.KQ)))))
  (P.0≤x⇒nonNegx (P.<⇒≤ (RootPos.canonicalFloorSquareRootStrictlyPositive (s≤s z≤n))))

-- Terminal algebra on the original p and original target. The two
-- positive branch witnesses are paid by the existing native owners.
squareToNativePeriod : (a * sq p) ≃ b → End.NativePeriod
squareToNativePeriod h =
  let eq = cancelLeft a aPos (P.≃-trans h (P.≃-symm targetSquare))
  in P.≤-antisym
    (Reflect.squareReflectsOnNonnegative pNN targetNN (P.≤-reflexive eq))
    (Reflect.squareReflectsOnNonnegative targetNN pNN (P.≤-reflexive (P.≃-symm eq)))

-- Native analytic inputs remaining: actual weighted series attachment,
-- root square and first Euler flow, actual CM j value, signed Hecke jet.
-- No NativePeriod or all-index cross is a premise.
periodFromCMRealSlice : (x y e f j : ℝ) → R.Positive x →
  F.seriesReal ≃ (A * f + B * j) →
  sq f ≃ x → sq y ≃ (t * cube x) →
  (six * y * j) ≃ (f * (e * x - y)) →
  ((M.bishopMachinPi * r) * (B * x * e - D * y)) ≃ (six * B * x) →
  End.NativePeriod
periodFromCMRealSlice x y e f j px hs hf hy hj hc =
  squareToNativePeriod (normalizedSquare x y f px hf hy (signedCross x y e f j hs hj hc))
