module DASHI.Analysis.WeilTestSpace where

-- Reusable analytic carrier for the Riemann-Weil lane.
--
-- This module deliberately does not choose a fake finite substitute for the
-- classical test-function space.  It records the algebra, admissibility,
-- transform, order, and approximation laws needed by later exact proofs.

open import Agda.Builtin.Equality using (_≡_; refl)

record WeilTestSpace : Set₁ where
  field
    Scalar : Set
    Test : Set
    TransformValue : Set

    zeroS : Scalar
    _+S_ : Scalar → Scalar → Scalar
    nonnegative : Scalar → Set

    nonnegativeZero : nonnegative zeroS
    nonnegativeAdd :
      {x y : Scalar} →
      nonnegative x → nonnegative y → nonnegative (x +S y)
    nonnegativeTransport :
      {x y : Scalar} → x ≡ y → nonnegative x → nonnegative y

    admissible : Test → Set
    involution : Test → Test
    transform : Test → TransformValue
    TransformDefined : Test → Set
    transformDefined :
      (f : Test) → admissible f → TransformDefined f
    involutionAdmissible :
      (f : Test) → admissible f → admissible (involution f)

record DenseDashiFamily (space : WeilTestSpace) : Set₁ where
  open WeilTestSpace space
  field
    DashiTest : Set
    embed : DashiTest → Test
    embeddedAdmissible : (x : DashiTest) → admissible (embed x)

    Approximation : Test → Set
    denseRange : (f : Test) → admissible f → Approximation f

-- Tiny equality combinators are kept local to the zeta lane so downstream
-- bridge modules need no postulated equality transport.
≡-sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
≡-sym refl = refl

≡-trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans refl refl = refl
