module DASHI.Moonshine.JInvariantBishopCM163HalfUnitIsolationExact where

-- SOURCE-WRITTEN, UNCOMPILED. Constructive half-unit isolation on the
-- actual guarded j. The original diagonal identity and analytic
-- enclosure are still required. No CM integrality premise.
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised.Properties as QP
open import Data.Sum.Base using (inj₁)
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _*_; _+_; _-_; _⋆; ∣_∣)
import RealProperties as P
import DASHI.Analysis.BishopSquareZeroReflectsSetoidZeroExact as Zero
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as J
import DASHI.Moonshine.JInvariantBishopCM163DiskCrossCoefficientExact as Jet
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as Guard

half : ℝ
half = (+ 1 / 2) ⋆

halfNN : R.NonNegative half
halfNN = P.pos⇒nonNeg (P.posp⇒posp⋆ (+ 1 / 2) (QP.positive⁻¹ (+ 1 / 2)))

-- Ascending coefficient order, preserving literal zero coefficients.
horner : ℝ → List ℝ → ℝ
horner u [] = R.0ℝ
horner u (c ∷ cs) = c + u * horner u cs

majorant : List ℝ → ℝ
majorant [] = R.0ℝ
majorant (c ∷ cs) = ∣ c ∣ + half * majorant cs

productBound : (u v M : ℝ) → ∣ u ∣ ≤ half → ∣ v ∣ ≤ M →
  ∣ u * v ∣ ≤ half * M
productBound u v M hu hv =
  P.≤-respˡ-≃ (P.≃-symm (P.∣x*y∣≃∣x∣*∣y∣ u v))
    (P.≤-trans (P.*-monoʳ-≤-nonNeg hu (P.nonNeg∣x∣ v))
      (P.*-monoˡ-≤-nonNeg hv halfNN))

hornerBound : (u : ℝ) (cs : List ℝ) → ∣ u ∣ ≤ half →
  ∣ horner u cs ∣ ≤ majorant cs
hornerBound u [] hu =
  P.≤-reflexive (P.nonNegx⇒∣x∣≃x P.nonNeg0)
hornerBound u (c ∷ cs) hu =
  P.≤-trans (P.∣x+y∣≤∣x∣+∣y∣ c (u * horner u cs))
    (P.+-monoʳ-≤ ∣ c ∣
      (productBound u (horner u cs) (majorant cs) hu (hornerBound u cs hu)))

tail : ℝ → List ℝ → ℝ
tail u cs = u * horner u cs

tailBound : (u : ℝ) (cs : List ℝ) → ∣ u ∣ ≤ half →
  ∣ tail u cs ∣ ≤ half * majorant cs
tailBound u cs hu = productBound u (horner u cs) (majorant cs) hu (hornerBound u cs hu)

-- The literal shifted P2 is negative. Use the signed dominance,
-- not a replacement polynomial with erased orientation.
complementNegative : (u p2 : ℝ) (cs : List ℝ) →
  ∣ u ∣ ≤ half → half * majorant cs < R.- p2 →
  p2 + tail u cs < R.0ℝ
complementNegative u p2 cs hu hd =
  P.<-respʳ-≃
    (let open P.ℝ-Solver in solve 1 (λ p → p ⊕ (⊝ p) ⊜ Κ (+ 0 / 1)) P.≃-refl p2)
    (P.+-monoʳ-< p2 (P.≤-<-trans
      (P.≤-trans (P.x≤∣x∣ {x = tail u cs}) (tailBound u cs hu)) hd))

isolate : (u p2 : ℝ) (cs : List ℝ) →
  ∣ u ∣ ≤ half → half * majorant cs < R.- p2 →
  ((u * u) * (p2 + tail u cs)) ≃ R.0ℝ → u ≃ R.0ℝ
isolate u p2 cs hu hd h =
  Zero.squareZeroReflectsSetoidZero u
    (Jet.cancelApart (p2 + tail u cs) (inj₁ (complementNegative u p2 cs hu hd))
      (P.≃-trans (P.*-comm (p2 + tail u cs) (u * u))
        (P.≃-trans h (P.≃-symm (P.*-zeroʳ (p2 + tail u cs))))))

-- The original guarded Klein quotient, not a free real root.
offset : ℝ
offset = Guard.Root.j - J.K

rootFromShiftedDiagonal : (p2 : ℝ) (cs : List ℝ) →
  ∣ offset ∣ ≤ half → half * majorant cs < R.- p2 →
  ((offset * offset) * (p2 + tail offset cs)) ≃ R.0ℝ →
  J.CMRoot
rootFromShiftedDiagonal p2 cs hu hd h =
  P.≃-trans
    (let open P.ℝ-Solver in solve 2 (λ j k → j ⊜ (j ⊖ k) ⊕ k)
      P.≃-refl Guard.Root.j J.K)
    (P.≃-trans (P.+-cong (isolate offset p2 cs hu hd h) P.≃-refl)
      (P.+-identityˡ J.K))
