module DASHI.Physics.ClaySupportingKPSummabilityFromSizeDecay where

------------------------------------------------------------------------
-- Elementary, fully-proved KP summability algebra (YM P06→P07→KP).
--
-- Companion to `...ClaySupportingPolymerCounting` and
-- `...ClaySupportingP06DiameterShell`.  Every declaration here is a
-- genuine Agda proof over concrete ℕ data: there are NO `postulate`s
-- and NO added axioms.
--
-- The plan asks for the conditional bridge:
--
--   #{X : |X| = n} ≤ Cpolyⁿ  ∧  |ζ(X)| ≤ A·e^{−κn}  ∧  Cpoly·e^{a−κ} < 1
--                                     ⇒  Σ_{X∋v} |ζ(X)|·e^{a·|X|}  <  ∞.
--
-- This module proves the ℕ-algebraic content of that bridge: once the
-- per-size skeleton count and per-size activity decay are bounded by
-- geometric series with respective bases C and R, the N-th partial KP
-- sum is bounded by A · Σ_{n=0}^{N} (C·R)ⁿ, i.e. A · geomSum (C·R) N.
--
-- Honesty boundary (unchanged and deliberate): the convergence condition
-- Cpoly·e^{a−κ} < 1 is a **real-valued inequality** that cannot be
-- expressed inside the ℕ-only arithmetic of this module.  This module
-- therefore does NOT assert that the infinite KP sum converges; it
-- proves the finite algebraic bound.  The actual convergence (infinite
-- geometric series being finite) is a real-analytic step that the
-- consuming module must supply by linking C·R < 1 to the real-valued
-- polymer decay (P10) and the size-shell counting (P06).  What is
-- proved here is the purely algebraic inequality that any such
-- consuming module can invoke.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n)
open import Data.Nat.Properties
  using ( *-assoc; *-comm; *-distribˡ-+; *-distribʳ-+
        ; +-mono-≤; ≤-refl; ≤-trans; *-mono-≤ )
open import Relation.Binary.PropositionalEquality
  using (cong; sym; trans; subst)

open import DASHI.Physics.ClaySupportingElementaryLemmas
  using (pow; geomSum)

------------------------------------------------------------------------
-- Helper: equality implies inequality (over ℕ).

≡⇒≤ : ∀ {x y} → x ≡ y → x ≤ y
≡⇒≤ refl = ≤-refl

------------------------------------------------------------------------
-- §1.  The KP partial sum (finite, n = 1 … N).

kpPartialSum : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ
kpPartialSum count _    zero    = 0
kpPartialSum count term (suc N) =
  count (suc N) * term (suc N) + kpPartialSum count term N

------------------------------------------------------------------------
-- §2.  ℕ arithmetic lemma:  Cⁿ·Rⁿ = (C·R)ⁿ.

private
  pow-* : ∀ a b n → pow a n * pow b n ≡ pow (a * b) n
  pow-* a b zero    = refl
  pow-* a b (suc n) =
    trans (*-assoc a (pow a n) (b * pow b n))
      (trans (cong (a *_)
               (trans (sym (*-assoc (pow a n) b (pow b n)))
                 (trans (cong (_* pow b n) (*-comm (pow a n) b))
                        (*-assoc b (pow a n) (pow b n)))))
             (trans (sym (*-assoc a b (pow a n * pow b n)))
                    (cong ((a * b) *_) (pow-* a b n))))

------------------------------------------------------------------------
-- §3.  Per-term bound.
--
-- Given  count n ≤ Cⁿ  and  term n ≤ A·Rⁿ, the product satisfies
--   count n · term n  ≤  A · (C·R)ⁿ.

kpTermBound :
  (C A R n : ℕ) (count term : ℕ → ℕ) →
  count n ≤ pow C n →
  term n ≤ A * pow R n →
  count n * term n ≤ A * pow (C * R) n
kpTermBound C A R n count term cb tb =
  ≤-trans (*-mono-≤ cb tb) (≡⇒≤ eq)
  where
    -- Cⁿ·(A·Rⁿ) = (Cⁿ·A)·Rⁿ = (A·Cⁿ)·Rⁿ = A·(Cⁿ·Rⁿ) = A·(C·R)ⁿ
    eq : pow C n * (A * pow R n) ≡ A * pow (C * R) n
    eq =
      trans (sym (*-assoc (pow C n) A (pow R n)))
        (trans (cong (_* pow R n) (*-comm (pow C n) A))
          (trans (*-assoc A (pow C n) (pow R n))
                 (cong (A *_) (pow-* C R n))))

------------------------------------------------------------------------
-- §4.  Summation bound.
--
-- The N-th partial KP sum is dominated by A times the geometric sum of
-- ratio (C·R).  The n = 0 term (which geomSum includes) absorbs the
-- offset between the sum from n=1 and the sum from n=0.

kpSummationBound :
  (C A R : ℕ) (count term : ℕ → ℕ) →
  (∀ n → count n ≤ pow C n) →
  (∀ n → term n ≤ A * pow R n) →
  ∀ N → kpPartialSum count term N ≤ A * geomSum (C * R) N
kpSummationBound C A R count term cb tb zero    =
  z≤n   -- kpPartialSum ... zero = 0  ≤  A * geomSum (C*R) zero = A
kpSummationBound C A R count term cb tb (suc N) =
  ≤-trans
    (+-mono-≤ (kpTermBound C A R (suc N) count term (cb (suc N)) (tb (suc N)))
              (kpSummationBound C A R count term cb tb N))
    (≡⇒≤ (sym (*-distribˡ-+ A (pow (C * R) (suc N)) (geomSum (C * R) N))))
