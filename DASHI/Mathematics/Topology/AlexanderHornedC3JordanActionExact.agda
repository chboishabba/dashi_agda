module DASHI.Mathematics.Topology.AlexanderHornedC3JordanActionExact where

------------------------------------------------------------------------
-- JORDAN-TYPE CONSUMER: EXACT BUT NOT A GEOMETRY / VOA BRIDGE.
--
-- A commutative magma with the Jordan identity can be tripled
-- componentwise, and the same cyclic coordinate permutation as in
-- the three-satellite geometry acts by product automorphisms.
--
-- Source: Jordan identity (classical). Original: the finite C3
-- componentwise transport proof. This *does not* supply bilinearity,
-- a field, a genuine Albert/Jordan algebra, a VOA, a Monster
-- automorphism, or a map from the geometric exterior pi1.
-- To upgrade the consumer one must add those independent structures.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Mathematics.Topology.AlexanderHornedC3AmbientRotationExact as Ambient

record JordanIdentityMagma : Set₁ where
  field
    Carrier : Set
    product : Carrier → Carrier → Carrier
    commute : ∀ x y → product x y ≡ product y x
    jordanIdentity : ∀ x y →
      product (product x x) (product y x)
        ≡ product (product (product x x) y) x

open JordanIdentityMagma public

TripleOf : JordanIdentityMagma → Set
TripleOf J = Ambient.Triple (Carrier J)

pointwiseProduct : (J : JordanIdentityMagma) →
  TripleOf J → TripleOf J → TripleOf J
pointwiseProduct J (Ambient.xyz a b c) (Ambient.xyz x y z) =
  Ambient.xyz
    (product J a x)
    (product J b y)
    (product J c z)

tripleExt : ∀ {A : Set} {a b c d e f : A} →
  a ≡ d → b ≡ e → c ≡ f →
  Ambient.xyz a b c ≡ Ambient.xyz d e f
tripleExt refl refl refl = refl

pointwiseCommutative : (J : JordanIdentityMagma) →
  ∀ a b → pointwiseProduct J a b ≡ pointwiseProduct J b a
pointwiseCommutative J
  (Ambient.xyz a b c) (Ambient.xyz x y z) =
  tripleExt (commute J a x) (commute J b y) (commute J c z)

pointwiseJordanIdentity : (J : JordanIdentityMagma) →
  ∀ x y →
  pointwiseProduct J (pointwiseProduct J x x)
    (pointwiseProduct J y x)
  ≡ pointwiseProduct J
      (pointwiseProduct J (pointwiseProduct J x x) y) x
pointwiseJordanIdentity J
  (Ambient.xyz a b c) (Ambient.xyz x y z) =
  tripleExt
    (jordanIdentity J a x)
    (jordanIdentity J b y)
    (jordanIdentity J c z)

rotationPreservesPointwiseProduct :
  (J : JordanIdentityMagma) → ∀ x y →
  Ambient.rotateXYZ (pointwiseProduct J x y)
    ≡ pointwiseProduct J
        (Ambient.rotateXYZ x) (Ambient.rotateXYZ y)
rotationPreservesPointwiseProduct J (Ambient.xyz a b c)
  (Ambient.xyz x y z) = refl

rotationHasOrderThree : (J : JordanIdentityMagma) → ∀ x →
  Ambient.rotateXYZ (Ambient.rotateXYZ (Ambient.rotateXYZ x)) ≡ x
rotationHasOrderThree J = Ambient.rotateXYZCubed

-- An actual VOA tensor-cube action would require the existing
-- VertexOperatorAlgebraCore tensor products and a specified
-- VOA-automorphism action. This magma theorem does NOT establish it.
