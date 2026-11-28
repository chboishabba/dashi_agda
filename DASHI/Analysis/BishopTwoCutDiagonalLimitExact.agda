module DASHI.Analysis.BishopTwoCutDiagonalLimitExact where

-- SOURCE-WRITTEN, UNCOMPILED. Constructive diagonal summation on
-- the pinned Bishop carrier. Two independent cutoffs, chosen from
-- the actual outer majorant and finitely many row-limit moduli.
-- Bounded monotonicity by itself is NOT used as convergence.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_⊔_; s≤s)
import Data.Nat.Properties as NP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised.Properties as QP
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as S
import DASHI.Foundations.BishopFiniteRectangleInsideCauchyTriangleExact as O

Rows : Set
Rows = Nat → Nat → ℝ

rowPrefix : Rows → Nat → Nat → ℝ
rowPrefix a M N = S.SeriesOf (λ k → a k N) M

diagonal : Rows → Nat → ℝ
diagonal a N = rowPrefix a N N

finiteRows : (a : Rows) (l : Nat → ℝ) →
  (∀ k → S._ConvergesTo_ (a k) (l k)) →
  (M : Nat) → S._ConvergesTo_ (rowPrefix a M) (S.SeriesOf l M)
finiteRows a l h zero = S.xₙ≃c⇒xₙ→c (λ n → P.≃-refl)
finiteRows a l h (suc M) = S.xₙ+yₙ→x₀+y₀
  (S.SeriesOf l M , finiteRows a l h M) (l M , h M)

-- The omitted finite row segment is dominated by the corresponding
-- majorant segment; the majorant segment is below its genuine tail.
outerCut : (a : Rows) (m : Nat → ℝ) →
  (∀ k → R.NonNegative (m k)) →
  (∀ k N → ∣ a k N ∣ ≤ m k) →
  (hm : S._isConvergent (S.SeriesOf m)) →
  (M N : Nat) → M Data.Nat.Base.≤ N →
  ∣ diagonal a N - rowPrefix a M N ∣ ≤
    ∣ S.SeriesOf m M - proj₁ hm ∣
outerCut a m nn bound hm M N h =
  P.≤-trans
    (P.≤-respˡ-≃ (P.∣-∣-cong (S.∑ₙᵐ≃∑₀ᵐ-∑₀ⁿ (λ k → a k N) M N))
      (S.∑-triangle-inequality (λ k → a k N) M N h))
    (P.≤-trans
      (S.∑-mono-≤ (λ k → bound k N) M N h)
      (P.≤-trans
        (P.≤-respˡ-≃ (P.≃-symm (S.∑ₙᵐ≃∑₀ᵐ-∑₀ⁿ m M N))
          (P.+-monoˡ-≤ (R.- (S.SeriesOf m M))
            (S.xₙisIncreasing⇒xₙ≤limxₙ (O.partialSumsIncreasing nn) hm N)))
        (P.≤-respʳ-≃ (P.∣x-y∣≃∣y-x∣ (proj₁ hm) (S.SeriesOf m M))
          P.x≤∣x∣)))

threeErrors : (a b c d : ℝ) →
  ∣ a - d ∣ ≤ ((∣ a - b ∣ + ∣ b - c ∣) + ∣ c - d ∣)
threeErrors a b c d =
  P.≤-respˡ-≃
    (P.∣-∣-cong (let open P.ℝ-Solver in
      solve 4 (λ a b c d → ((a ⊖ b) ⊕ (b ⊖ c)) ⊕ (c ⊖ d) ⊜ a ⊖ d)
        P.≃-refl a b c d))
    (P.≤-trans (P.∣x+y∣≤∣x∣+∣y∣ ((a - b) + (b - c)) (c - d))
      (P.+-mono-≤ (P.∣x+y∣≤∣x∣+∣y∣ (a - b) (b - c)) P.≤-refl))

-- No hypothesis of diagonal convergence: build the actual modulus.
diagonalLimit : (a : Rows) (l m : Nat → ℝ) →
  (∀ k → R.NonNegative (m k)) →
  (∀ k N → ∣ a k N ∣ ≤ m k) →
  (∀ k → S._ConvergesTo_ (a k) (l k)) →
  (hm : S._isConvergent (S.SeriesOf m)) →
  (hl : S._isConvergent (S.SeriesOf l)) →
  S._ConvergesTo_ (diagonal a) (proj₁ hl)
diagonalLimit a l m nn bound rows hm hl = S.con*
  (λ { (suc k) →
    let
      eps = (+ 1 / (suc k)) ⋆
      third = (+ 1 / 3) ⋆
      eta = third * eps
      etaPos = P.posx,y⇒posx*y
        (P.posp⇒posp⋆ (+ 1 / 3) (QP.positive⁻¹ (+ 1 / 3)))
        (P.posp⇒posp⋆ (+ 1 / (suc k)) (QP.positive⁻¹ (+ 1 / (suc k))))
      maj = S.ε-from-convergence hm eta etaPos
      lim = S.ε-from-convergence hl eta etaPos
      M = suc (proj₁ maj ⊔ proj₁ lim)
      mCut = P.<⇒≤ (proj₂ maj M (s≤s (NP.m≤m⊔n (proj₁ maj) (proj₁ lim))))
      lCut = P.<⇒≤ (proj₂ lim M (s≤s (NP.m≤n⊔m (proj₁ maj) (proj₁ lim))))
      fixed = S.ε-from-convergence (S.SeriesOf l M , finiteRows a l rows M) eta etaPos
      N0 = M ⊔ proj₁ fixed
      total : (eta + eta + eta) ≃ eps
      total = let open P.ℝ-Solver in
        solve 1 (λ e → Κ (+ 1 / 3) ⊗ e ⊕ Κ (+ 1 / 3) ⊗ e ⊕ Κ (+ 1 / 3) ⊗ e ⊜ e)
          P.≃-refl eps
    in N0 , λ N hN →
      let
        M≤N = NP.≤-trans (NP.m≤m⊔n M (proj₁ fixed))
          (NP.≤-trans (NP.n≤1+n N0) hN)
        rowCut = P.<⇒≤ (proj₂ fixed N
          (NP.≤-trans (s≤s (NP.m≤n⊔m M (proj₁ fixed))) hN))
      in P.≤-respʳ-≃ total
        (P.≤-trans (threeErrors (diagonal a N) (rowPrefix a M N) (S.SeriesOf l M) (proj₁ hl))
          (P.+-mono-≤ (P.+-mono-≤
            (P.≤-trans (outerCut a m nn bound hm M N M≤N) mCut) rowCut) lCut)) })
