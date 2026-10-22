module DASHI.Foundations.C3O2SignedWindingTransportExact where

-- Exact O(2)=S1 rtimes C2 action on discrete winding lifts.
-- Orientation sign acts on integer winding by inversion.
-- This does not manufacture a physical KK-fibre action from a spatial mirror.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -[1+_]; -_; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

data Parity : Set where
  preserve reverse : Parity

flip : Parity → Parity
flip preserve = reverse
flip reverse = preserve

multiply : Parity → Parity → Parity
multiply preserve q = q
multiply reverse q = flip q

leftUnit : ∀ p → multiply preserve p ≡ p
leftUnit preserve = refl
leftUnit reverse = refl

squareReverse : multiply reverse reverse ≡ preserve
squareReverse = refl

parityAssociative : ∀ p q r →
  multiply (multiply p q) r ≡ multiply p (multiply q r)
parityAssociative preserve preserve preserve = refl
parityAssociative preserve preserve reverse = refl
parityAssociative preserve reverse preserve = refl
parityAssociative preserve reverse reverse = refl
parityAssociative reverse preserve preserve = refl
parityAssociative reverse preserve reverse = refl
parityAssociative reverse reverse preserve = refl
parityAssociative reverse reverse reverse = refl

-- Abstraction for the actual integer/sign action. This avoids silently
-- assuming any sign algebra beyond a paid group automorphism.
record SignedWindingAction : Set₁ where
  field
    Winding : Set
    zero : Winding
    add : Winding → Winding → Winding
    invert : Winding → Winding
    invertTwice : ∀ w → invert (invert w) ≡ w
    invertAdd : ∀ a b → invert (add a b) ≡ add (invert a) (invert b)
open SignedWindingAction public

module Transport (A : SignedWindingAction) where
  action : Parity → Winding A → Winding A
  action preserve w = w
  action reverse w = invert A w

  actionComposition : ∀ p q w →
    action (multiply p q) w ≡ action p (action q w)
  actionComposition preserve preserve w = refl
  actionComposition preserve reverse w = refl
  actionComposition reverse preserve w = refl
  actionComposition reverse reverse w = sym (invertTwice A w)

  record O2DiscreteLift : Set where
    constructor pair
    field
      winding : Winding A
      parity : Parity
  open O2DiscreteLift public

  compose : O2DiscreteLift → O2DiscreteLift → O2DiscreteLift
  compose (pair a p) (pair b q) =
    pair (add A a (action p b)) (multiply p q)

  -- Multiplication of integer winding and reflection parity is the
  -- generalized dihedral semidirect-product law. Associativity requires
  -- the source addition associativity and action distributivity.
