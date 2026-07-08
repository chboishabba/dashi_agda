module DASHI.Physics.ClaySupportingResidualDomination where

------------------------------------------------------------------------
-- Elementary, fully-proved residual-domination / controlled-decomposition
-- row algebra for the NS profile kernels.
--
-- Companion to `DASHI.Physics.ClaySupportingSchurRecombination` and
-- `DASHI.Physics.ClaySupportingElementaryLemmas`.  As in those modules,
-- every declaration here is a genuine Agda proof over concrete data:
-- there are NO `postulate`s and NO added axioms.
--
-- This supplies the NS package §A1/§A2 "relation-to-kernel" domination
-- algebra:
--
--   rowSum-mono              pointwise ≤ lifts to row sums
--   rowSum-+                 the row sum splits over a pointwise kernel sum
--   rowSum-*                 a scalar factors out of a row sum
--   controlledDecompRowBound the NS-4' controlled decomposition at row level:
--                              Kᵃᶜᵗ ≤ Kᶠᵀ+Kᵃᵈᵛ+Kᵗʳᵃⁿˢ+Kʳᵉˢ (pointwise)
--                              ⇒ Rᵃᶜᵗ ≤ Rᶠᵀ+Rᵃᵈᵛ+Rᵗʳᵃⁿˢ+Rʳᵉˢ
--   residualDomRowBound      the NS-2 residual domination at row level:
--                              Kʳᵉˢ ≤ λ_FT Kᶠᵀ+λ_adv Kᵃᵈᵛ+λ_tr Kᵗʳᵃⁿˢ
--                              ⇒ Rʳᵉˢ ≤ λ_FT Rᶠᵀ+λ_adv Rᵃᵈᵛ+λ_tr Rᵗʳᵃⁿˢ
--
-- Honesty boundary (unchanged and deliberate): this does NOT discharge any
-- open analytic Clay leaf.  It is the domination *algebra* only; the
-- profile-specific N⁻² decay inputs (the actual analytic estimates that
-- bound each individual profile row sum) remain open and are NOT asserted
-- here.  What is proved is that once the pointwise kernel inequalities hold,
-- the corresponding row-sum inequalities follow rigorously -- exactly the
-- bookkeeping the package flags as "domination algebra, no new primitive".
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties
  using ( +-assoc; +-comm; *-distribˡ-+; *-zeroʳ
        ; +-mono-≤; ≤-refl; ≤-trans )
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans; subst)

------------------------------------------------------------------------
-- §0.  Row sum of a kernel row over a finite index list.
--   rowSum js k = Σ_{j ∈ js} k j.

rowSum : {J : Set} → List J → (J → ℕ) → ℕ
rowSum []       k = 0
rowSum (j ∷ js) k = k j + rowSum js k

------------------------------------------------------------------------
-- §1.  Monotonicity: a pointwise ≤ between kernel rows lifts to row sums.

rowSum-mono :
  {J : Set} (js : List J) (k1 k2 : J → ℕ) →
  (∀ j → k1 j ≤ k2 j) →
  rowSum js k1 ≤ rowSum js k2
rowSum-mono []       k1 k2 h = ≤-refl
rowSum-mono (j ∷ js) k1 k2 h =
  +-mono-≤ (h j) (rowSum-mono js k1 k2 h)

------------------------------------------------------------------------
-- §2.  The row sum is additive over a pointwise kernel sum.
--   Σ_j (f j + g j) = (Σ_j f j) + (Σ_j g j).

rowSum-+ :
  {J : Set} (js : List J) (f g : J → ℕ) →
  rowSum js (λ j → f j + g j) ≡ rowSum js f + rowSum js g
rowSum-+ []       f g = refl
rowSum-+ (j ∷ js) f g =
  trans (cong ((f j + g j) +_) (rowSum-+ js f g))
        (lem (f j) (g j) (rowSum js f) (rowSum js g))
  where
    -- (a+b)+(c+d) = (a+c)+(b+d)
    lem : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
    lem a b c d =
      trans (+-assoc a b (c + d))
        (trans (cong (a +_) (sym (+-assoc b c d)))
          (trans (cong (λ z → a + (z + d)) (+-comm b c))
            (trans (cong (a +_) (+-assoc c b d))
                   (sym (+-assoc a c (b + d))))))

------------------------------------------------------------------------
-- §3.  A scalar factors out of a row sum.
--   Σ_j (c · f j) = c · Σ_j f j.

rowSum-* :
  {J : Set} (js : List J) (c : ℕ) (f : J → ℕ) →
  rowSum js (λ j → c * f j) ≡ c * rowSum js f
rowSum-* []       c f = sym (*-zeroʳ c)
rowSum-* (j ∷ js) c f =
  trans (cong (c * f j +_) (rowSum-* js c f))
        (sym (*-distribˡ-+ c (f j) (rowSum js f)))

------------------------------------------------------------------------
-- §4.  Controlled decomposition at the row level (NS-4').
--
-- If the actual kernel is pointwise dominated by the sum of the four
-- profile kernels, then the actual row sum is dominated by the sum of the
-- four profile row sums.

controlledDecompRowBound :
  {J : Set} (js : List J) (kAct kFT kAdv kTr kRes : J → ℕ) →
  (∀ j → kAct j ≤ ((kFT j + kAdv j) + kTr j) + kRes j) →
  rowSum js kAct
    ≤ ((rowSum js kFT + rowSum js kAdv) + rowSum js kTr) + rowSum js kRes
controlledDecompRowBound js kAct kFT kAdv kTr kRes h =
  ≤-trans
    (rowSum-mono js kAct
       (λ j → ((kFT j + kAdv j) + kTr j) + kRes j) h)
    (subst
      (λ z → rowSum js (λ j → ((kFT j + kAdv j) + kTr j) + kRes j) ≤ z)
      eq ≤-refl)
  where
    eq : rowSum js (λ j → ((kFT j + kAdv j) + kTr j) + kRes j)
       ≡ ((rowSum js kFT + rowSum js kAdv) + rowSum js kTr) + rowSum js kRes
    eq =
      trans (rowSum-+ js (λ j → (kFT j + kAdv j) + kTr j) kRes)
        (cong (_+ rowSum js kRes)
          (trans (rowSum-+ js (λ j → kFT j + kAdv j) kTr)
            (cong (_+ rowSum js kTr)
              (rowSum-+ js kFT kAdv))))

------------------------------------------------------------------------
-- §5.  Residual domination at the row level (NS-2).
--
-- If the residual kernel is pointwise dominated by the weighted sum of the
-- three parent profile kernels, then the residual row sum is dominated by
-- the same weighted sum of the parent row sums -- so the residual profile
-- contributes no new primitive, only this domination algebra.

residualDomRowBound :
  {J : Set} (js : List J) (kRes kFT kAdv kTr : J → ℕ)
  (λFT λAdv λTr : ℕ) →
  (∀ j → kRes j ≤ ((λFT * kFT j + λAdv * kAdv j) + λTr * kTr j)) →
  rowSum js kRes
    ≤ ((λFT * rowSum js kFT + λAdv * rowSum js kAdv) + λTr * rowSum js kTr)
residualDomRowBound js kRes kFT kAdv kTr λFT λAdv λTr h =
  ≤-trans
    (rowSum-mono js kRes
       (λ j → (λFT * kFT j + λAdv * kAdv j) + λTr * kTr j) h)
    (subst
      (λ z → rowSum js (λ j → (λFT * kFT j + λAdv * kAdv j) + λTr * kTr j) ≤ z)
      eq ≤-refl)
  where
    eq : rowSum js (λ j → (λFT * kFT j + λAdv * kAdv j) + λTr * kTr j)
       ≡ ((λFT * rowSum js kFT + λAdv * rowSum js kAdv) + λTr * rowSum js kTr)
    eq =
      trans (rowSum-+ js (λ j → λFT * kFT j + λAdv * kAdv j) (λ j → λTr * kTr j))
        (cong₂ _+_
          (trans (rowSum-+ js (λ j → λFT * kFT j) (λ j → λAdv * kAdv j))
            (cong₂ _+_ (rowSum-* js λFT kFT) (rowSum-* js λAdv kAdv)))
          (rowSum-* js λTr kTr))
