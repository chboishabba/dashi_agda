module DASHI.Physics.ClaySupportingFiniteShellDissipation where

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties
  using ( +-mono-≤; ≤-refl; ≤-trans; *-mono-≤; *-assoc; *-comm
        ; *-distribˡ-+; *-zeroʳ )
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import DASHI.Physics.ClaySupportingShellEnergyBudget using (sum)

----------------------------------------------------------------------
-- §1  Helper lemmas for sum
----------------------------------------------------------------------

sum-mono : (f g : Nat → Nat) (R : Nat) → (∀ N → f N ≤ g N) →
  sum f R ≤ sum g R
sum-mono f g zero h = h zero
sum-mono f g (suc R) h =
  +-mono-≤ (h (suc R)) (sum-mono f g R h)

sum-* : (c : Nat) (f : Nat → Nat) (R : Nat) →
  sum (λ N → c * f N) R ≡ c * sum f R
sum-* c f zero = refl
sum-* c f (suc R) =
  trans (cong (c * f (suc R) +_) (sum-* c f R))
        (sym (*-distribˡ-+ c (f (suc R)) (sum f R)))

----------------------------------------------------------------------
-- §2  Hypothesis type aliases
----------------------------------------------------------------------

ShellStrongDominatedByDissipation :
  (shellNormSq shellGradSq : Nat → Nat) (C_shell : Nat) → Set
ShellStrongDominatedByDissipation shellNormSq shellGradSq C_shell =
  ∀ N → shellNormSq N ≤ C_shell * shellGradSq N

FiniteShellAlmostOrthogonality :
  (shellGradSq : Nat → Nat) (totalGradSq C_LP R : Nat) → Set
FiniteShellAlmostOrthogonality shellGradSq totalGradSq C_LP R =
  sum shellGradSq R ≤ C_LP * totalGradSq

GlobalDissipationBudget :
  (totalGradSq dissipationBudget : Nat) → Set
GlobalDissipationBudget totalGradSq dissipationBudget =
  totalGradSq ≤ dissipationBudget

FiniteShellStrongBudget :
  (shellNormSq : Nat → Nat) (R C_shell C_LP dissipationBudget : Nat) → Set
FiniteShellStrongBudget shellNormSq R C_shell C_LP dissipationBudget =
  sum shellNormSq R ≤ (C_shell * C_LP) * dissipationBudget

----------------------------------------------------------------------
-- §3  Lemma: sum of shell norms ≤ C_shell * sum of shell gradients
----------------------------------------------------------------------

sumShellBound :
  (shellNormSq shellGradSq : Nat → Nat) (C_shell R : Nat) →
  ShellStrongDominatedByDissipation shellNormSq shellGradSq C_shell →
  sum shellNormSq R ≤ C_shell * sum shellGradSq R
sumShellBound shellNormSq shellGradSq C_shell R shellBound =
  subst (λ z → sum shellNormSq R ≤ z) factor mono
  where
    mono : sum shellNormSq R ≤ sum (λ N → C_shell * shellGradSq N) R
    mono = sum-mono shellNormSq (λ N → C_shell * shellGradSq N) R shellBound

    factor : sum (λ N → C_shell * shellGradSq N) R ≡ C_shell * sum shellGradSq R
    factor = sum-* C_shell shellGradSq R

----------------------------------------------------------------------
-- §4  Lemma: sum ≤ (C_shell * C_LP) * totalGradSq via orthogonality
----------------------------------------------------------------------

sumBoundFromOrthogonality :
  (shellNormSq shellGradSq : Nat → Nat) (R C_shell C_LP totalGradSq : Nat) →
  ShellStrongDominatedByDissipation shellNormSq shellGradSq C_shell →
  FiniteShellAlmostOrthogonality shellGradSq totalGradSq C_LP R →
  sum shellNormSq R ≤ (C_shell * C_LP) * totalGradSq
sumBoundFromOrthogonality
  shellNormSq shellGradSq R C_shell C_LP totalGradSq shellBound ortho =
  subst (λ z → sum shellNormSq R ≤ z) assoc chain
  where
    step1 : sum shellNormSq R ≤ C_shell * sum shellGradSq R
    step1 = sumShellBound shellNormSq shellGradSq C_shell R shellBound

    step2 : C_shell * sum shellGradSq R ≤ C_shell * (C_LP * totalGradSq)
    step2 = *-mono-≤ (≤-refl {C_shell}) ortho

    assoc : C_shell * (C_LP * totalGradSq) ≡ (C_shell * C_LP) * totalGradSq
    assoc = sym (*-assoc C_shell C_LP totalGradSq)

    chain : sum shellNormSq R ≤ C_shell * (C_LP * totalGradSq)
    chain = ≤-trans step1 step2

----------------------------------------------------------------------
-- §5  Main theorem: chain all three hypotheses to FiniteShellStrongBudget
----------------------------------------------------------------------

finiteShellStrongBudgetFromDissipation :
  (shellNormSq shellGradSq : Nat → Nat) (R C_shell C_LP : Nat) →
  (totalGradSq dissipationBudget : Nat) →
  ShellStrongDominatedByDissipation shellNormSq shellGradSq C_shell →
  FiniteShellAlmostOrthogonality shellGradSq totalGradSq C_LP R →
  GlobalDissipationBudget totalGradSq dissipationBudget →
  FiniteShellStrongBudget shellNormSq R C_shell C_LP dissipationBudget
finiteShellStrongBudgetFromDissipation
  shellNormSq shellGradSq R C_shell C_LP totalGradSq dissipationBudget
  shellBound ortho leray =
  let
    stepA : sum shellNormSq R ≤ (C_shell * C_LP) * totalGradSq
    stepA = sumBoundFromOrthogonality
              shellNormSq shellGradSq R C_shell C_LP totalGradSq
              shellBound ortho

    stepB : (C_shell * C_LP) * totalGradSq ≤ (C_shell * C_LP) * dissipationBudget
    stepB = *-mono-≤ (≤-refl {C_shell * C_LP}) leray
  in
  ≤-trans stepA stepB
