module DASHI.Physics.YangMills.BalabanComputedPolynomialSolver where

------------------------------------------------------------------------
-- Close the final gap in the axiomatic-real polynomial socket.
--
-- `Algebra.Solver.Ring.solve` traditionally expects the normal forms to be
-- definitionally equal, so callers usually finish with `refl`.  With DASHI's
-- computable formal-difference coefficients two normal forms can instead be
-- propositionally equal through the coefficient decision procedure while their
-- interpretations are not definitionally identical.  This wrapper computes the
-- normal-form comparison and transports the returned proof through the solver.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Maybe.Base using (Maybe; just)
open import Data.Product.Base using (_×_; proj₁; proj₂)
open import Data.Vec.Base as Vec using (allFin; map)
open import Data.Vec.N-ary using
  ( N-ary
  ; _$ⁿ_
  ; curryⁿ
  ; Eq
  ; curryⁿ-cong
  ; Eq-to-Eqʰ
  )

open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver )
open RealPolynomialSolver using
  ( Polynomial
  ; normalise
  ; var
  )

------------------------------------------------------------------------
-- A proof-relevant, indexed `isJust` witness.  Supplying `computed` forces
-- Agda to normalize the coefficient comparison at compile time.
------------------------------------------------------------------------

data IsJust {A : Set} : Maybe A → Set where
  computed : ∀ {x} → IsJust (just x)

extractJust : ∀ {A : Set} {m : Maybe A} → IsJust m → A
extractJust {m = just x} computed = x

closedPair :
  ∀ n →
  N-ary n (Polynomial n) (Polynomial n × Polynomial n) →
  Polynomial n × Polynomial n
closedPair n f = f $ⁿ Vec.map var (allFin n)

solveComputed :
  ∀ n
  (f : N-ary n (Polynomial n) (Polynomial n × Polynomial n)) →
  IsJust
    (RealPolynomialSolver._≟N_
      (normalise (proj₁ (closedPair n f)))
      (normalise (proj₂ (closedPair n f)))) →
  Eq n _≡_
    (curryⁿ (RealPolynomialSolver.⟦ proj₁ (closedPair n f) ⟧))
    (curryⁿ (RealPolynomialSolver.⟦ proj₂ (closedPair n f) ⟧))
solveComputed n f witness =
  RealPolynomialSolver.solve n f
    (Eq-to-Eqʰ n _≡_
      (curryⁿ-cong _≡_
        (RealPolynomialSolver.⟦ normalise (proj₁ (closedPair n f)) ⟧N)
        (RealPolynomialSolver.⟦ normalise (proj₂ (closedPair n f)) ⟧N)
        (λ ρ →
          RealPolynomialSolver.⟦ extractJust witness ⟧N-cong ρ)))
