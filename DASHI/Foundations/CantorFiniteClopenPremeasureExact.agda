module DASHI.Foundations.CantorFiniteClopenPremeasureExact where

------------------------------------------------------------------------
-- FINITE CLOPEN ALGEBRA OF THE BINARY / CANTOR PRODUCT SPACE
--
-- CantorProjectiveCylinderMeasureExact proves one-cylinder projective
-- consistency.  Here an event at depth n is an arbitrary selection of the 2^n
-- binary cylinders.  The resulting finite Boolean algebra has exact rational
-- complement and disjoint-union laws, and refinement preserves measure.
--
-- This is the finite-algebra/premeasure layer required before a genuine
-- sigma-additive extension theorem.  It does not assert Caratheodory extension.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

------------------------------------------------------------------------
-- Full powerset of a depth-n binary cylinder layer, represented recursively.
------------------------------------------------------------------------

data ClopenEvent : Nat → Set where
  off on : ClopenEvent zero
  branch : ∀ {n} → ClopenEvent n → ClopenEvent n → ClopenEvent (suc n)

clopenMass : ∀ {n} → ClopenEvent n → ℚ
clopenMass off = 0ℚ
clopenMass on = 1ℚ
clopenMass (branch left right) =
  ½ * (clopenMass left + clopenMass right)

complement : ∀ {n} → ClopenEvent n → ClopenEvent n
complement off = on
complement on = off
complement (branch left right) =
  branch (complement left) (complement right)

complementInvolutive : ∀ {n} (event : ClopenEvent n) →
  complement (complement event) ≡ event
complementInvolutive off = refl
complementInvolutive on = refl
complementInvolutive (branch left right)
  rewrite complementInvolutive left | complementInvolutive right = refl

private
  complementRearrange : (a b c d : ℚ) →
    ½ * (a + b) + ½ * (c + d)
    ≡ ½ * ((a + c) + (b + d))
  complementRearrange = solve-∀

clopenMassComplement : ∀ {n} (event : ClopenEvent n) →
  clopenMass event + clopenMass (complement event) ≡ 1ℚ
clopenMassComplement off = solve-∀
clopenMassComplement on = solve-∀
clopenMassComplement (branch left right)
  rewrite complementRearrange
    (clopenMass left) (clopenMass right)
    (clopenMass (complement left)) (clopenMass (complement right))
        | clopenMassComplement left
        | clopenMassComplement right = solve-∀

------------------------------------------------------------------------
-- Boolean union and a proof-relevant disjointness relation.
------------------------------------------------------------------------

union : ∀ {n} → ClopenEvent n → ClopenEvent n → ClopenEvent n
union off right = right
union on right = on
union (branch l₁ r₁) (branch l₂ r₂) =
  branch (union l₁ l₂) (union r₁ r₂)

data Disjoint : ∀ {n} → ClopenEvent n → ClopenEvent n → Set where
  offLeft : (right : ClopenEvent zero) → Disjoint off right
  offRight : Disjoint on off
  branchDisjoint :
    ∀ {n} {l₁ r₁ l₂ r₂ : ClopenEvent n} →
    Disjoint l₁ l₂ → Disjoint r₁ r₂ →
    Disjoint (branch l₁ r₁) (branch l₂ r₂)

private
  disjointRearrange : (a b c d : ℚ) →
    ½ * ((a + c) + (b + d))
    ≡ ½ * (a + b) + ½ * (c + d)
  disjointRearrange = solve-∀

clopenFiniteAdditivity :
  ∀ {n} {left right : ClopenEvent n} →
  Disjoint left right →
  clopenMass (union left right)
  ≡ clopenMass left + clopenMass right
clopenFiniteAdditivity (offLeft off) = solve-∀
clopenFiniteAdditivity (offLeft on) = solve-∀
clopenFiniteAdditivity offRight = solve-∀
clopenFiniteAdditivity
  (branchDisjoint {l₁ = l₁} {r₁ = r₁} {l₂ = l₂} {r₂ = r₂}
    leftDisjoint rightDisjoint)
  rewrite clopenFiniteAdditivity leftDisjoint
        | clopenFiniteAdditivity rightDisjoint
        | disjointRearrange
            (clopenMass l₁) (clopenMass r₁)
            (clopenMass l₂) (clopenMass r₂) = refl

------------------------------------------------------------------------
-- Refinement replaces each selected depth-n cylinder by both children.  This
-- is the inclusion of a finite clopen algebra into the next cylinder layer.
------------------------------------------------------------------------

refine : ∀ {n} → ClopenEvent n → ClopenEvent (suc n)
refine off = branch off off
refine on = branch on on
refine (branch left right) = branch (refine left) (refine right)

refinementPreservesMass : ∀ {n} (event : ClopenEvent n) →
  clopenMass (refine event) ≡ clopenMass event
refinementPreservesMass off = solve-∀
refinementPreservesMass on = solve-∀
refinementPreservesMass (branch left right)
  rewrite refinementPreservesMass left
        | refinementPreservesMass right = refl

refinementCommutesWithComplement : ∀ {n} (event : ClopenEvent n) →
  refine (complement event) ≡ complement (refine event)
refinementCommutesWithComplement off = refl
refinementCommutesWithComplement on = refl
refinementCommutesWithComplement (branch left right)
  rewrite refinementCommutesWithComplement left
        | refinementCommutesWithComplement right = refl

refinementCommutesWithUnion : ∀ {n} (left right : ClopenEvent n) →
  refine (union left right) ≡ union (refine left) (refine right)
refinementCommutesWithUnion off right = refl
refinementCommutesWithUnion on right = refl
refinementCommutesWithUnion (branch l₁ r₁) (branch l₂ r₂)
  rewrite refinementCommutesWithUnion l₁ l₂
        | refinementCommutesWithUnion r₁ r₂ = refl

------------------------------------------------------------------------
-- Unit and empty events exist uniformly at every finite depth.
------------------------------------------------------------------------

emptyEvent fullEvent : (n : Nat) → ClopenEvent n
emptyEvent zero = off
emptyEvent (suc n) = branch (emptyEvent n) (emptyEvent n)
fullEvent zero = on
fullEvent (suc n) = branch (fullEvent n) (fullEvent n)

emptyHasZeroMass : (n : Nat) → clopenMass (emptyEvent n) ≡ 0ℚ
emptyHasZeroMass zero = refl
emptyHasZeroMass (suc n) rewrite emptyHasZeroMass n = solve-∀

fullHasUnitMass : (n : Nat) → clopenMass (fullEvent n) ≡ 1ℚ
fullHasUnitMass zero = refl
fullHasUnitMass (suc n) rewrite fullHasUnitMass n = solve-∀

------------------------------------------------------------------------
-- Boundary: we now have a directed system of finite clopen Boolean algebras
-- carrying a consistent finitely additive probability premeasure.  Extending
-- this to the sigma-algebra generated by cylinders and proving countable
-- additivity remains an actual measure-extension theorem, not a consequence of
-- finite refinement alone.
------------------------------------------------------------------------
