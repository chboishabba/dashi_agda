module DASHI.Mathematics.Symmetry.TetragonalIntegralLatticeActionExact where

-- A literal 3-coordinate signed-permutation representation of D4h.
-- It is instantiated on Z by supplying the existing integer negation,
-- but all group/dual laws are formulated over any carrier with
-- involutive negation, making the remaining integer algebra explicit.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
import DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact as D

record Triple (A : Set) : Set where
  constructor xyz
  field
    x y z : A
open Triple public

record SignedCarrier (A : Set) : Set where
  field
    negate : A → A
    negateTwice : (x : A) → negate (negate x) ≡ x
open SignedCarrier public

R : ∀ {A} → SignedCarrier A → Triple A → Triple A
R S (xyz x y z) = xyz (negate S y) x z

V : ∀ {A} → SignedCarrier A → Triple A → Triple A
V S (xyz x y z) = xyz x (negate S y) z

H : ∀ {A} → SignedCarrier A → Triple A → Triple A
H S (xyz x y z) = xyz x y (negate S z)

quarter : ∀ {A} → SignedCarrier A → D.Quarter → Triple A → Triple A
quarter S D.q0 p = p
quarter S D.q1 p = R S p
quarter S D.q2 p = R S (R S p)
quarter S D.q3 p = R S (R S (R S p))

vertical : ∀ {A} → SignedCarrier A → Bool → Triple A → Triple A
vertical S false p = p
vertical S true p = V S p

horizontal : ∀ {A} → SignedCarrier A → Bool → Triple A → Triple A
horizontal S false p = p
horizontal S true p = H S p

act : ∀ {A} → SignedCarrier A → D.D4h → Triple A → Triple A
act S (D.element a b c) p =
  quarter S a (vertical S b (horizontal S c p))

R4 : ∀ {A} (S : SignedCarrier A) (p : Triple A) →
  R S (R S (R S (R S p))) ≡ p
R4 S (xyz x y z) rewrite negateTwice S x | negateTwice S y = refl

V2 : ∀ {A} (S : SignedCarrier A) (p : Triple A) →
  V S (V S p) ≡ p
V2 S (xyz x y z) rewrite negateTwice S y = refl

H2 : ∀ {A} (S : SignedCarrier A) (p : Triple A) →
  H S (H S p) ≡ p
H2 S (xyz x y z) rewrite negateTwice S z = refl

-- In lattice coordinates with a diagonal tetragonal metric
-- M=diag(a,a,c), signed permutations of x,y and z-sign reversal
-- preserve M when the scalar square laws hold. Reciprocal indices
-- transform contragrediently; for these orthogonal integer matrices
-- U^{-T}=U, but not for arbitrary primitive Bravais basis changes.

-- Group-generator relations on *arbitrary* signed coordinate carriers.
-- The scalar involution assumption is the only algebra required.
quarterFour : ∀ {A} (S : SignedCarrier A) (p : Triple A) →
  quarter S D.q1 (quarter S D.q1
    (quarter S D.q1 (quarter S D.q1 p))) ≡ p
quarterFour = R4

verticalReflectConjugatesQuarter :
  ∀ {A} (S : SignedCarrier A) (p : Triple A) →
  V S (R S (V S p)) ≡ R S (R S (R S p))
verticalReflectConjugatesQuarter S (xyz x y z)
  rewrite negateTwice S x | negateTwice S y = refl

horizontalCentralWithR :
  ∀ {A} (S : SignedCarrier A) (p : Triple A) →
  H S (R S p) ≡ R S (H S p)
horizontalCentralWithR S (xyz x y z) = refl

horizontalCentralWithV :
  ∀ {A} (S : SignedCarrier A) (p : Triple A) →
  H S (V S p) ≡ V S (H S p)
horizontalCentralWithV S (xyz x y z) = refl

-- A nontrivial point-wise separation of a quarter-turn and the
-- identity requires a point whose x/y coordinates are distinguishable,
-- and cannot follow for arbitrary A (for example, a one-point A).
