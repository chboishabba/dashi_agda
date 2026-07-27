module DASHI.Physics.Closure.NSTriadKNLerayContractionFromPythagoras where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Jean Leray; Marco Cannone; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin; DASHI repository contributors.
-- Title: "Leray contraction and projected-mode bound from the exact
-- Pythagorean identity".
-- Venue/year: Handbook of Mathematical Fluid Dynamics, Volume 3, 2005;
-- Fourier Analysis and Nonlinear Partial Differential Equations, Springer,
-- 2011; DASHI formal development, 2026.
-- DOI: 10.1016/S1874-5792(05)80006-0;
-- 10.1007/978-3-642-16830-7; repository-original reduction has no DOI.
-- Uses: ||P_k v||^2 = ||v||^2 - correction(k,v), nonnegativity of the
-- rank-one correction, and monotonicity of subtraction by a nonnegative term.
-- Relationship: closes the order-theoretic derivation of Leray contraction.
-- The remaining concrete leaf is the ordered C3 Pythagorean identity and its
-- nonnegative correction term.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record LerayPythagoreanCarrier
    {m v s : Level} : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    Mode : Set m
    Vector : Set v
    Scalar : Set s

    project : Mode → Vector → Vector
    normSquared : Vector → Scalar
    correction : Mode → Vector → Scalar
    subtract : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set s
    zero : Scalar

    correctionNonnegative : ∀ mode value →
      zero ≤ correction mode value

    subtractNonnegativeBelow : ∀ total part →
      zero ≤ part → subtract total part ≤ total

    pythagoreanIdentity : ∀ mode value →
      normSquared (project mode value)
      ≡ subtract (normSquared value) (correction mode value)

open LerayPythagoreanCarrier public

transportLeqLeft :
  ∀ {s} {Scalar : Set s} {_≤_ : Scalar → Scalar → Set s}
    {a b c : Scalar} →
  a ≡ b → _≤_ b c → _≤_ a c
transportLeqLeft refl proof = proof

lerayNormSquaredContraction :
  ∀ {m v s}
    (C : LerayPythagoreanCarrier {m} {v} {s})
    (mode : Mode C)
    (value : Vector C) →
  _≤_ C
    (normSquared C (project C mode value))
    (normSquared C value)
lerayNormSquaredContraction C mode value =
  transportLeqLeft
    (pythagoreanIdentity C mode value)
    (subtractNonnegativeBelow C
      (normSquared C value)
      (correction C mode value)
      (correctionNonnegative C mode value))

record ProjectedModeApplication
    {m v s : Level}
    (C : LerayPythagoreanCarrier {m} {v} {s}) :
    Set (lsuc (m ⊔ v ⊔ s)) where
  field
    modeVector : Mode C → Vector C

open ProjectedModeApplication public

projectedModeNormSquaredBound :
  ∀ {m v s}
    {C : LerayPythagoreanCarrier {m} {v} {s}}
    (A : ProjectedModeApplication C)
    (projectorMode differentiatedMode : Mode C) →
  _≤_ C
    (normSquared C
      (project C projectorMode (modeVector A differentiatedMode)))
    (normSquared C (modeVector A differentiatedMode))
projectedModeNormSquaredBound {C = C} A projectorMode differentiatedMode =
  lerayNormSquaredContraction C projectorMode
    (modeVector A differentiatedMode)

lerayContractionReductionClosed : Bool
lerayContractionReductionClosed = true

lerayContractionReductionClosedIsTrue :
  lerayContractionReductionClosed ≡ true
lerayContractionReductionClosedIsTrue = refl

projectedModeBoundReductionClosed : Bool
projectedModeBoundReductionClosed = true

projectedModeBoundReductionClosedIsTrue :
  projectedModeBoundReductionClosed ≡ true
projectedModeBoundReductionClosedIsTrue = refl

concreteC3LerayPythagoreanIdentityClosed : Bool
concreteC3LerayPythagoreanIdentityClosed = false

concreteC3LerayPythagoreanIdentityClosedIsFalse :
  concreteC3LerayPythagoreanIdentityClosed ≡ false
concreteC3LerayPythagoreanIdentityClosedIsFalse = refl
