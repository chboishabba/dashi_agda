module DASHI.Physics.ClaySupportingSchurRecombination where

------------------------------------------------------------------------
-- Elementary, fully-proved cross-profile Schur recombination algebra.
--
-- Companion to `DASHI.Physics.ClaySupportingElementaryLemmas`, consuming
-- its finite Cauchy/Schur cross-product algebra in the one high-value NS
-- place the plan names: the profile cross-matrix step (§III, eqns (1)→(2)).
-- Every declaration is a genuine Agda proof; there are NO `postulate`s and
-- NO added axioms.
--
-- Scope / honesty boundary (unchanged): this supplies the correct
-- CROSS-term recombination algebra with the common analytic scale factored
-- out.  It does NOT supply — and does not pretend to supply — the missing
-- profile-specific decay input (the N⁻² estimate); that input appears here
-- only as an explicit hypothesis of the form  r_p·c_q ≤ A_pq · f, i.e. the
-- open leaf is left as a parameter, not asserted.
--
-- Key exports:
--   sumL-map-*ʳ            Σ_j (a_j · f) = (Σ_j a_j) · f      (factor a scale out)
--   crossFactoredBound     cart xs ys ≤* map(·f) as  ⟹  (Σx)(Σy) ≤ (Σa)·f
--   fourProfileFactoredBound   the {FT,adv,trans,res} eqn (1)→(2) instance
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (*-distribʳ-+)
open import Data.List.Base using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)

open import DASHI.Physics.ClaySupportingElementaryLemmas
  using (sumL; cart; _≤*_; []; _∷_; schurCrossBound)

------------------------------------------------------------------------
-- §1.  Factoring a common scale out of a finite sum:  Σ (aⱼ·f) = (Σ aⱼ)·f.
--
-- This is the algebra that pulls the common N⁻² factor out of the
-- cross-matrix sum, giving the right-hand side of eqn (2).

sumL-map-*ʳ : ∀ (f : ℕ) (as : List ℕ) → sumL (map (_* f) as) ≡ sumL as * f
sumL-map-*ʳ f []       = refl
sumL-map-*ʳ f (a ∷ as) =
  trans (cong ((a * f) +_) (sumL-map-*ʳ f as))
        (sym (*-distribʳ-+ f a (sumL as)))

------------------------------------------------------------------------
-- §2.  Cross-matrix bound with the common scale factored out.
--
-- If every cross term xᵢ·yⱼ is dominated by Aₖ·f (a bound with a common
-- factor f), then  (Σ xᵢ)·(Σ yⱼ) = Σ xᵢyⱼ ≤ (Σ Aₖ)·f.
-- This is precisely eqn (1) ⟹ eqn (2) with f playing the role of N⁻².

crossFactoredBound :
  ∀ (xs ys as : List ℕ) (f : ℕ) →
  cart xs ys ≤* map (_* f) as →
  sumL xs * sumL ys ≤ sumL as * f
crossFactoredBound xs ys as f dom =
  subst (λ z → sumL xs * sumL ys ≤ z)
        (sumL-map-*ʳ f as)
        (schurCrossBound xs ys (map (_* f) as) dom)

------------------------------------------------------------------------
-- §3.  The four-profile instance (P = {FT, adv, trans, res}).
--
-- With row quantities r₁..r₄ and column quantities c₁..c₄, if each of the
-- sixteen cross terms satisfies  r_p·c_q ≤ A_{pq}·f, then
--     (Σ r_p)·(Σ c_q)  ≤  (Σ_{p,q} A_{pq})·f.
-- Reading f = N⁻², this is exactly the NS §III eqn (2):
--     R(N)·C(N) ≤ (Σ_{p,q} A_{pq})·N⁻².

fourProfileFactoredBound :
  ∀ (r1 r2 r3 r4 c1 c2 c3 c4 f : ℕ)
    (A11 A12 A13 A14 A21 A22 A23 A24
     A31 A32 A33 A34 A41 A42 A43 A44 : ℕ) →
  r1 * c1 ≤ A11 * f → r1 * c2 ≤ A12 * f → r1 * c3 ≤ A13 * f → r1 * c4 ≤ A14 * f →
  r2 * c1 ≤ A21 * f → r2 * c2 ≤ A22 * f → r2 * c3 ≤ A23 * f → r2 * c4 ≤ A24 * f →
  r3 * c1 ≤ A31 * f → r3 * c2 ≤ A32 * f → r3 * c3 ≤ A33 * f → r3 * c4 ≤ A34 * f →
  r4 * c1 ≤ A41 * f → r4 * c2 ≤ A42 * f → r4 * c3 ≤ A43 * f → r4 * c4 ≤ A44 * f →
  sumL (r1 ∷ r2 ∷ r3 ∷ r4 ∷ []) * sumL (c1 ∷ c2 ∷ c3 ∷ c4 ∷ [])
    ≤ sumL ( A11 ∷ A12 ∷ A13 ∷ A14
         ∷ A21 ∷ A22 ∷ A23 ∷ A24
         ∷ A31 ∷ A32 ∷ A33 ∷ A34
         ∷ A41 ∷ A42 ∷ A43 ∷ A44 ∷ []) * f
fourProfileFactoredBound r1 r2 r3 r4 c1 c2 c3 c4 f
  A11 A12 A13 A14 A21 A22 A23 A24 A31 A32 A33 A34 A41 A42 A43 A44
  h11 h12 h13 h14 h21 h22 h23 h24 h31 h32 h33 h34 h41 h42 h43 h44 =
  crossFactoredBound (r1 ∷ r2 ∷ r3 ∷ r4 ∷ []) (c1 ∷ c2 ∷ c3 ∷ c4 ∷ [])
    ( A11 ∷ A12 ∷ A13 ∷ A14
    ∷ A21 ∷ A22 ∷ A23 ∷ A24
    ∷ A31 ∷ A32 ∷ A33 ∷ A34
    ∷ A41 ∷ A42 ∷ A43 ∷ A44 ∷ []) f
    ( h11 ∷ h12 ∷ h13 ∷ h14
    ∷ h21 ∷ h22 ∷ h23 ∷ h24
    ∷ h31 ∷ h32 ∷ h33 ∷ h34
    ∷ h41 ∷ h42 ∷ h43 ∷ h44 ∷ [])
