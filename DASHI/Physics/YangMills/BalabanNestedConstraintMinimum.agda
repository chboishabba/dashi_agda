module DASHI.Physics.YangMills.BalabanNestedConstraintMinimum where

-- Source-neutral algebra for the cumulative Bałaban constraint calculation.
--
-- The source-specific work still has to identify the actual composed averages,
-- penalty operators, and determinant factors.  This module proves the part that
-- does not depend on those analytic details:
--
--   * sequential feasibility is equivalent to feasibility for the composed map;
--   * a minimizer for one formulation is a minimizer for the other;
--   * sequentially pushed covariance equals covariance pushed through the
--     composed constraint;
--   * any inverse operation respecting pointwise operator equality therefore
--     gives the same nested Schur operator.
--
-- No Yang--Mills estimate, determinant enclosure, or availability flag is
-- introduced here.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)

infixr 9 _∘_
infix  4 _≈_ _⇔_

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)

trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {A B : Set} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

record _⇔_ (A B : Set) : Set where
  constructor iff
  field
    to   : A → B
    from : B → A

open _⇔_ public

-- A two-stage constraint remembers the intermediate coarse variable.  The
-- direct constraint retains only the composed equation.
SequentialFeasible :
  {Fine Middle Coarse : Set} →
  (Fine → Middle) →
  (Middle → Coarse) →
  Coarse →
  Fine →
  Set
SequentialFeasible Q₁ Q₂ z x =
  Σ _ (λ y → (Q₁ x ≡ y) × (Q₂ y ≡ z))

DirectFeasible :
  {Fine Middle Coarse : Set} →
  (Fine → Middle) →
  (Middle → Coarse) →
  Coarse →
  Fine →
  Set
DirectFeasible Q₁ Q₂ z x = Q₂ (Q₁ x) ≡ z

composedConstraint :
  {Fine Middle Coarse : Set} →
  (Fine → Middle) →
  (Middle → Coarse) →
  Fine → Coarse
composedConstraint Q₁ Q₂ = Q₂ ∘ Q₁

directToSequential :
  {Fine Middle Coarse : Set} →
  (Q₁ : Fine → Middle) →
  (Q₂ : Middle → Coarse) →
  (z : Coarse) →
  (x : Fine) →
  DirectFeasible Q₁ Q₂ z x →
  SequentialFeasible Q₁ Q₂ z x
directToSequential Q₁ Q₂ z x direct =
  Q₁ x , (refl , direct)

sequentialToDirect :
  {Fine Middle Coarse : Set} →
  (Q₁ : Fine → Middle) →
  (Q₂ : Middle → Coarse) →
  (z : Coarse) →
  (x : Fine) →
  SequentialFeasible Q₁ Q₂ z x →
  DirectFeasible Q₁ Q₂ z x
sequentialToDirect Q₁ Q₂ z x sequential =
  trans
    (cong Q₂ (proj₁ (proj₂ sequential)))
    (proj₂ (proj₂ sequential))

sequentialFeasibleIffDirect :
  {Fine Middle Coarse : Set} →
  (Q₁ : Fine → Middle) →
  (Q₂ : Middle → Coarse) →
  (z : Coarse) →
  (x : Fine) →
  SequentialFeasible Q₁ Q₂ z x
    ⇔ DirectFeasible Q₁ Q₂ z x
sequentialFeasibleIffDirect Q₁ Q₂ z x =
  iff
    (sequentialToDirect Q₁ Q₂ z x)
    (directToSequential Q₁ Q₂ z x)

-- `Minimises` needs only an objective and a comparison relation.  No order,
-- completeness, or existence principle is postulated.
Minimises :
  {Point Value : Set} →
  (Value → Value → Set) →
  (Point → Value) →
  (Point → Set) →
  Point →
  Set
Minimises _≼_ objective feasible x =
  feasible x ×
  ((y : _) → feasible y → objective x ≼ objective y)

sequentialMinimumToDirect :
  {Fine Middle Coarse Value : Set} →
  (_≼_ : Value → Value → Set) →
  (objective : Fine → Value) →
  (Q₁ : Fine → Middle) →
  (Q₂ : Middle → Coarse) →
  (z : Coarse) →
  (x : Fine) →
  Minimises _≼_ objective (SequentialFeasible Q₁ Q₂ z) x →
  Minimises _≼_ objective (DirectFeasible Q₁ Q₂ z) x
sequentialMinimumToDirect _≼_ objective Q₁ Q₂ z x minimum =
  sequentialToDirect Q₁ Q₂ z x (proj₁ minimum) ,
  λ y direct-y →
    proj₂ minimum y (directToSequential Q₁ Q₂ z y direct-y)

directMinimumToSequential :
  {Fine Middle Coarse Value : Set} →
  (_≼_ : Value → Value → Set) →
  (objective : Fine → Value) →
  (Q₁ : Fine → Middle) →
  (Q₂ : Middle → Coarse) →
  (z : Coarse) →
  (x : Fine) →
  Minimises _≼_ objective (DirectFeasible Q₁ Q₂ z) x →
  Minimises _≼_ objective (SequentialFeasible Q₁ Q₂ z) x
directMinimumToSequential _≼_ objective Q₁ Q₂ z x minimum =
  directToSequential Q₁ Q₂ z x (proj₁ minimum) ,
  λ y sequential-y →
    proj₂ minimum y (sequentialToDirect Q₁ Q₂ z y sequential-y)

sequentialMinimumEqualsDirectMinimum :
  {Fine Middle Coarse Value : Set} →
  (_≼_ : Value → Value → Set) →
  (objective : Fine → Value) →
  (Q₁ : Fine → Middle) →
  (Q₂ : Middle → Coarse) →
  (z : Coarse) →
  (x : Fine) →
  Minimises _≼_ objective (SequentialFeasible Q₁ Q₂ z) x
    ⇔ Minimises _≼_ objective (DirectFeasible Q₁ Q₂ z) x
sequentialMinimumEqualsDirectMinimum _≼_ objective Q₁ Q₂ z x =
  iff
    (sequentialMinimumToDirect _≼_ objective Q₁ Q₂ z x)
    (directMinimumToSequential _≼_ objective Q₁ Q₂ z x)

-- Pointwise equality is the appropriate source-neutral operator equality here;
-- it avoids importing function extensionality.
_≈_ : {A B : Set} → (A → B) → (A → B) → Set
f ≈ g = (x : _) → f x ≡ g x

constrainedCovariance :
  {Fine Coarse : Set} →
  (Fine → Coarse) →
  (Fine → Fine) →
  (Coarse → Fine) →
  Coarse → Coarse
constrainedCovariance Q inverseFine Q* =
  Q ∘ inverseFine ∘ Q*

composedAdjoint :
  {Fine Middle Coarse : Set} →
  (Middle → Fine) →
  (Coarse → Middle) →
  Coarse → Fine
composedAdjoint Q₁* Q₂* = Q₁* ∘ Q₂*

-- Pushing the fine covariance through Q₁ and then Q₂ is definitionally the
-- same operation as pushing it through the composed constraint Q₂ ∘ Q₁.
composedConstrainedCovariance :
  {Fine Middle Coarse : Set} →
  (Q₁ : Fine → Middle) →
  (Q₂ : Middle → Coarse) →
  (inverseFine : Fine → Fine) →
  (Q₁* : Middle → Fine) →
  (Q₂* : Coarse → Middle) →
  constrainedCovariance
    Q₂
    (constrainedCovariance Q₁ inverseFine Q₁*)
    Q₂*
  ≈ constrainedCovariance
      (composedConstraint Q₁ Q₂)
      inverseFine
      (composedAdjoint Q₁* Q₂*)
composedConstrainedCovariance Q₁ Q₂ inverseFine Q₁* Q₂* z = refl

-- Any inverse operation that respects pointwise equality transports the exact
-- covariance identity to the nested Schur operator.  The hypothesis is the
-- ordinary congruence property of the concrete inverse implementation, not a
-- Yang--Mills estimate.
nestedSchurComplementIdentity :
  {Fine Middle Coarse : Set} →
  (Q₁ : Fine → Middle) →
  (Q₂ : Middle → Coarse) →
  (inverseFine : Fine → Fine) →
  (Q₁* : Middle → Fine) →
  (Q₂* : Coarse → Middle) →
  (inverseCoarse : (Coarse → Coarse) → Coarse → Coarse) →
  (inverseCongruence :
    {F G : Coarse → Coarse} →
    F ≈ G →
    inverseCoarse F ≈ inverseCoarse G) →
  inverseCoarse
    (constrainedCovariance
      Q₂
      (constrainedCovariance Q₁ inverseFine Q₁*)
      Q₂*)
  ≈ inverseCoarse
      (constrainedCovariance
        (composedConstraint Q₁ Q₂)
        inverseFine
        (composedAdjoint Q₁* Q₂*))
nestedSchurComplementIdentity
  Q₁ Q₂ inverseFine Q₁* Q₂* inverseCoarse inverseCongruence =
  inverseCongruence
    (composedConstrainedCovariance Q₁ Q₂ inverseFine Q₁* Q₂*)
