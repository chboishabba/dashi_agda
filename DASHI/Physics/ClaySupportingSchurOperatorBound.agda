module DASHI.Physics.ClaySupportingSchurOperatorBound where

------------------------------------------------------------------------
-- Elementary, fully-proved Schur-test + profile-recombination algebra (NS §III).
--
-- Companion to `DASHI.Physics.ClaySupportingForcedTailRowColumnBounds`,
-- `...SchurRecombination` and `...ResidualDomination`.  Every declaration
-- here is a genuine Agda proof over concrete natural numbers: there are NO
-- `postulate`s and NO added axioms.
--
-- The plan asks: row/column bounds ⇒ ℓ² operator bound (Schur test), and
-- profile recombination ⇒ total weighted Schur bound.  Over ℕ the N⁻²
-- statements are in cleared-denominator form  "‖M‖ ≤ C/(N+1)²"  ↔
-- (N+1)²·‖M‖ ≤ C.  The two genuinely-analytic facts enter as hypotheses:
--
--   Schur test        :  ‖M‖·‖M‖ ≤ rowB · colB          (analytic input)
--   subadditivity     :  ‖ΣM_α‖ ≤ Σ ‖M_α‖               (analytic input)
--
-- and the module proves the ℕ-algebra that turns the N⁻² row/column bounds
-- into the operator bound and recombines the profiles:
--
--   sq-reflect            a·a ≤ b·b ⇒ a ≤ b       (ℕ square-root reflection)
--   schurTestOpBound      Schur test + N⁻² row & column ⇒ (N+1)²·‖M‖ ≤ C
--   profileRecombine      per-profile (N+1)²·‖M_α‖ ≤ C_α + subadditivity
--                         ⇒ (N+1)²·‖M‖ ≤ Σ C_α
--   fourProfileSchurBound the four-profile instance (FT, adv, trans, res)
--
-- Honesty boundary (unchanged): this discharges no open Clay leaf.  The
-- Schur test and the operator-norm subadditivity are real functional-analytic
-- facts about ℓ² operators and are taken as hypotheses; the profile-specific
-- N⁻² row/column inputs are supplied by
-- `...ForcedTailRowColumnBounds`/`...ResidualDomination` under their own open
-- hypotheses.  What is proved is that once those inputs hold, the total
-- weighted-Schur operator bound (N+1)²·‖M‖ ≤ C follows rigorously.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ; suc; _+_; _*_; _≤_; _<_)
open import Data.Nat.Properties
  using ( *-assoc; *-comm; *-mono-≤; *-mono-<
        ; ≤-refl; ≤-trans; ≮⇒≥; <⇒≱ )
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)

------------------------------------------------------------------------
-- §1.  Square-root reflection over ℕ:  a·a ≤ b·b ⇒ a ≤ b.

sq-reflect : ∀ {a b} → a * a ≤ b * b → a ≤ b
sq-reflect {a} {b} h = ≮⇒≥ (λ (b<a : b < a) → <⇒≱ (*-mono-< b<a b<a) h)

------------------------------------------------------------------------
-- §2.  Interchange helper:  (n·x)·(n·y) = (n·x·n)·y is repackaged as
--   (n·x)·(n·y) = (n·n)·(x·y)  so the Schur product factors cleanly.

private
  mul-swap : ∀ n x y → (n * x) * (n * y) ≡ (n * n) * (x * y)
  mul-swap n x y =
    trans (*-assoc n x (n * y))
      (trans (cong (n *_) (sym (*-assoc x n y)))
        (trans (cong (λ z → n * (z * y)) (*-comm x n))
          (trans (cong (n *_) (*-assoc n x y))
                 (sym (*-assoc n n (x * y))))))

------------------------------------------------------------------------
-- §3.  Schur test ⇒ operator bound.
--
-- With n := (N+1), from the Schur test ‖M‖² ≤ rowB·colB and the cleared
-- N⁻² row/column bounds n²·rowB ≤ C, n²·colB ≤ C we get
--   (n²·‖M‖)² = n⁴·‖M‖² ≤ (n²·rowB)(n²·colB) ≤ C·C,
-- and sq-reflect gives n²·‖M‖ ≤ C.

schurTestOpBound :
  (opNorm rowB colB N C : ℕ) →
  opNorm * opNorm ≤ rowB * colB →          -- Schur test (analytic input)
  (suc N * suc N) * rowB ≤ C →              -- N⁻² row bound
  (suc N * suc N) * colB ≤ C →              -- N⁻² column bound
  (suc N * suc N) * opNorm ≤ C
schurTestOpBound opNorm rowB colB N C schur rowN colN =
  sq-reflect sq≤
  where
    n² : ℕ
    n² = suc N * suc N

    -- (n²·‖M‖)² = n²²·(‖M‖·‖M‖) ≤ n²²·(rowB·colB) = (n²·rowB)(n²·colB) ≤ C·C
    sq≤ : (n² * opNorm) * (n² * opNorm) ≤ C * C
    sq≤ =
      subst (λ z → z ≤ C * C) (sym (mul-swap n² opNorm opNorm))
        (≤-trans
          (subst (λ z → (n² * n²) * (opNorm * opNorm) ≤ z)
                 (sym (mul-swap n² rowB colB))
                 (*-mono-≤ (≤-refl {n² * n²}) schur))
          (*-mono-≤ rowN colN))

------------------------------------------------------------------------
-- §4.  Profile recombination (triangle inequality consequence).
--
-- M = Σ_α M_α, so ‖M‖ ≤ Σ ‖M_α‖ (subadditivity, an input).  If each profile
-- obeys the N⁻² operator bound n²·‖M_α‖ ≤ C_α, then multiplying subadditivity
-- through by n² and summing gives n²·‖M‖ ≤ Σ C_α.

profileRecombine :
  (opTot op1 op2 op3 op4 N C1 C2 C3 C4 : ℕ) →
  opTot ≤ ((op1 + op2) + op3) + op4 →             -- subadditivity (input)
  (suc N * suc N) * op1 ≤ C1 →
  (suc N * suc N) * op2 ≤ C2 →
  (suc N * suc N) * op3 ≤ C3 →
  (suc N * suc N) * op4 ≤ C4 →
  (suc N * suc N) * opTot ≤ ((C1 + C2) + C3) + C4
profileRecombine opTot op1 op2 op3 op4 N C1 C2 C3 C4
                 sub h1 h2 h3 h4 =
  ≤-trans
    (*-mono-≤ (≤-refl {suc N * suc N}) sub)
    (subst (λ z → z ≤ ((C1 + C2) + C3) + C4) (sym distr)
      (+-mono₄ h1 h2 h3 h4))
  where
    open import Data.Nat.Properties using (*-distribˡ-+; +-mono-≤)

    n² : ℕ
    n² = suc N * suc N

    distr : n² * (((op1 + op2) + op3) + op4)
          ≡ ((n² * op1 + n² * op2) + n² * op3) + n² * op4
    distr =
      trans (*-distribˡ-+ n² ((op1 + op2) + op3) op4)
        (cong (_+ n² * op4)
          (trans (*-distribˡ-+ n² (op1 + op2) op3)
            (cong (_+ n² * op3)
                  (*-distribˡ-+ n² op1 op2))))

    +-mono₄ :
      ∀ {a b c d A B C D} → a ≤ A → b ≤ B → c ≤ C → d ≤ D →
      ((a + b) + c) + d ≤ ((A + B) + C) + D
    +-mono₄ pa pb pc pd =
      +-mono-≤ (+-mono-≤ (+-mono-≤ pa pb) pc) pd

------------------------------------------------------------------------
-- §5.  Four-profile total weighted-Schur operator bound.
--
-- Instantiating §3 for each of the four profiles {FT, adv, trans, res} and
-- recombining via §4 gives the total operator bound  n²·‖M‖ ≤ Σ_α C_α.

fourProfileSchurBound :
  (opTot opFT opAdv opTr opRes N : ℕ)
  (rFT cFT rAdv cAdv rTr cTr rRes cRes : ℕ)
  (CFT CAdv CTr CRes : ℕ) →
  opTot ≤ ((opFT + opAdv) + opTr) + opRes →       -- subadditivity (input)
  -- per-profile Schur tests (analytic inputs)
  opFT  * opFT  ≤ rFT  * cFT  →
  opAdv * opAdv ≤ rAdv * cAdv →
  opTr  * opTr  ≤ rTr  * cTr  →
  opRes * opRes ≤ rRes * cRes →
  -- per-profile N⁻² row/column bounds
  (suc N * suc N) * rFT  ≤ CFT  → (suc N * suc N) * cFT  ≤ CFT  →
  (suc N * suc N) * rAdv ≤ CAdv → (suc N * suc N) * cAdv ≤ CAdv →
  (suc N * suc N) * rTr  ≤ CTr  → (suc N * suc N) * cTr  ≤ CTr  →
  (suc N * suc N) * rRes ≤ CRes → (suc N * suc N) * cRes ≤ CRes →
  (suc N * suc N) * opTot ≤ ((CFT + CAdv) + CTr) + CRes
fourProfileSchurBound opTot opFT opAdv opTr opRes N
  rFT cFT rAdv cAdv rTr cTr rRes cRes CFT CAdv CTr CRes
  sub sFT sAdv sTr sRes
  rFTb cFTb rAdvb cAdvb rTrb cTrb rResb cResb =
  profileRecombine opTot opFT opAdv opTr opRes N CFT CAdv CTr CRes sub
    (schurTestOpBound opFT  rFT  cFT  N CFT  sFT  rFTb  cFTb)
    (schurTestOpBound opAdv rAdv cAdv N CAdv sAdv rAdvb cAdvb)
    (schurTestOpBound opTr  rTr  cTr  N CTr  sTr  rTrb  cTrb)
    (schurTestOpBound opRes rRes cRes N CRes sRes rResb cResb)
