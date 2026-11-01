module DASHI.Geometry.LCP.NatGlue where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _⊔_; _*_; s≤s)
open import Data.Nat.Properties as ℕₚ
open import Relation.Binary.PropositionalEquality using (_≡_; sym)

------------------------------------------------------------------------
-- Small, dependable helpers

-- i < suc i
i<suci : ∀ (i : ℕ) → i < suc i
i<suci i = ℕₚ.n<1+n i

-- Backwards compat alias (used in older notes)
s<i : ∀ (i : ℕ) → i < suc i
s<i = i<suci

-- If i < j and j ≤ k then i < k
<-≤-trans' : ∀ {i j k : ℕ} → i < j → j ≤ k → i < k
<-≤-trans' = ℕₚ.<-≤-trans

-- k ≤ k + n
≤-k+ : ∀ (k n : ℕ) → k ≤ k + n
≤-k+ k n = ℕₚ.m≤m+n k n

-- m ≤ m + n (alias)
m≤m+n' : ∀ (m n : ℕ) → m ≤ m + n
m≤m+n' = ≤-k+

-- n ≤ m + n
n≤m+n' : ∀ (m n : ℕ) → n ≤ m + n
n≤m+n' m n =
  let n≤n+m = ℕₚ.m≤m+n n m
  in ℕₚ.≤-trans n≤n+m (ℕₚ.≤-reflexive (ℕₚ.+-comm n m))

-- m ≤ n ⇒ m ≤ suc n
≤-suc : ∀ {m n : ℕ} → m ≤ n → m ≤ suc n
≤-suc = ℕₚ.m≤n⇒m≤1+n

-- Monotonicity of suc on ≤
suc-mono≤ : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
suc-mono≤ = s≤s

-- Max (⊔) bounds
≤-⊔-l : ∀ (a b : ℕ) → a ≤ (a ⊔ b)
≤-⊔-l a b = ℕₚ.m≤m⊔n a b

≤-⊔-r : ∀ (a b : ℕ) → b ≤ (a ⊔ b)
≤-⊔-r a b =
  ℕₚ.≤-trans (ℕₚ.m≤m⊔n b a)
             (ℕₚ.≤-reflexive (ℕₚ.⊔-comm b a))

≤-from-⊔-l : ∀ {a b N : ℕ} → N ≡ (a ⊔ b) → a ≤ N
≤-from-⊔-l {a} {b} {N} eq =
  ℕₚ.≤-trans (≤-⊔-l a b) (ℕₚ.≤-reflexive (sym eq))

≤-from-⊔-r : ∀ {a b N : ℕ} → N ≡ (a ⊔ b) → b ≤ N
≤-from-⊔-r {a} {b} {N} eq =
  ℕₚ.≤-trans (≤-⊔-r a b) (ℕₚ.≤-reflexive (sym eq))

-- ≤ trans re-export
≤-trans' : ∀ {m n k : ℕ} → m ≤ n → n ≤ k → m ≤ k
≤-trans' = ℕₚ.≤-trans

-- A common bound for Banach‑LCP
mul-κ-lower :
  ∀ (κ′ : ℕ) {n k : ℕ}
  → k ≤ n
  → k ≤ n * (suc κ′)
mul-κ-lower κ′ {n} k≤n =
  ℕₚ.≤-trans k≤n (ℕₚ.m≤m*n n (suc κ′))
