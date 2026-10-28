module DASHI.Mathematics.Topology.AlexanderHornedC3VOAModeLiftExact where

------------------------------------------------------------------------
-- EXACT CROSS-POLLINATION: HORNED-C3 FINITE ACTOR -> EXISTING
-- PROOF-BEARING RATIONAL VERTEX-ALGEBRA SEED.
--
-- Source of ALL rational-mode algebraic laws:
--   DASHI.Moonshine.TrivialRationalGradedVertexAlgebraExact
-- (Kac/Borcherds source attribution lives in that original owner).
--
-- For any factor group A, set Omega=C3 x A and W=Omega -> Q.
-- The old rational VOA seed is lifted *pointwise* to the SAME W
-- acted upon by the semidirect coordinate action from
-- AlexanderHornedC3FiniteVOAActorExact.
-- This proves exact equivariance of EVERY INTEGER MODE, and lifts
-- vacuum/creation/commutativity/associativity/translation/conformal
-- laws. All claims are pointwise, deliberately avoiding unjustified
-- function extensionality.
--
-- This is not the selected Monster VOA; the A5 specialisation is
-- independently provided by a concrete finite permutation audit.
-- A complete Agda value for the existing VertexOperatorAlgebraCore
-- would additionally require its full Jacobi/Virasoro/graded
-- representations and explicit finite A5 construction; mathematical
-- finite-dimensional commutative VOA result is classical.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ)
import DASHI.Moonshine.TrivialRationalGradedVertexAlgebraExact as Seed
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Rational.Base using (_+_)
import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteVOAActorExact as Actor

RationalState : Actor.ActorFactorGroup → Set
RationalState D = Actor.State D ℚ

vacuum : (D : Actor.ActorFactorGroup) → RationalState D
vacuum D = Actor.constant D 1ℚ

conformalVector : (D : Actor.ActorFactorGroup) → RationalState D
conformalVector D = Actor.constant D 0ℚ

vertexMode : (D : Actor.ActorFactorGroup) →
  RationalState D → ℤ → RationalState D → RationalState D
vertexMode D f n g x = Seed.trivialMode (f x) n (g x)

translation : (D : Actor.ActorFactorGroup) →
  RationalState D → RationalState D
translation D f x = Seed.translationOperator (f x)

modeVacuumIdentity : (D : Actor.ActorFactorGroup) →
  ∀ (f : RationalState D) x →
  vertexMode D (vacuum D) Seed.minusOne f x ≡ f x
modeVacuumIdentity D f x = Seed.vacuumMinusOneIdentity (f x)

modeCreationIdentity : (D : Actor.ActorFactorGroup) →
  ∀ (f : RationalState D) x →
  vertexMode D f Seed.minusOne (vacuum D) x ≡ f x
modeCreationIdentity D f x = Seed.creationMinusOne (f x)

modeCommutative : (D : Actor.ActorFactorGroup) →
  ∀ (f g : RationalState D) x →
  vertexMode D f Seed.minusOne g x
    ≡ vertexMode D g Seed.minusOne f x
modeCommutative D f g x =
  Seed.minusOneProductCommutative (f x) (g x)

modeAssociative : (D : Actor.ActorFactorGroup) →
  ∀ (f g h : RationalState D) x →
  vertexMode D f Seed.minusOne
    (vertexMode D g Seed.minusOne h) x
  ≡ vertexMode D
      (vertexMode D f Seed.minusOne g) Seed.minusOne h x
modeAssociative D f g h x =
  Seed.minusOneProductAssociative (f x) (g x) (h x)

-- A Jordan identity on the EXACT SAME finite VOA state carrier.
-- Pointwise commutative associative products are Jordan. This is not
-- an exceptional Albert or Monster/Griess recognition claim.
sameStateJordanIdentity : (D : Actor.ActorFactorGroup) →
  ∀ (f g : RationalState D) x →
  vertexMode D
    (vertexMode D f Seed.minusOne f) Seed.minusOne
    (vertexMode D g Seed.minusOne f) x
  ≡ vertexMode D
      (vertexMode D
        (vertexMode D f Seed.minusOne f) Seed.minusOne g)
      Seed.minusOne f x
sameStateJordanIdentity D f g x =
  ℚRing.solve-∀ (f x) (g x)

modeTranslationDerivation : (D : Actor.ActorFactorGroup) →
  ∀ (f g : RationalState D) x →
  translation D (vertexMode D f Seed.minusOne g) x
  ≡ Seed.trivialMode (translation D f x) Seed.minusOne (g x)
    +
       Seed.trivialMode (f x) Seed.minusOne (translation D g x)
modeTranslationDerivation D f g x =
  Seed.translationActsAsDerivationOnMinusOneProduct (f x) (g x)

-- Reuse the rational addition from the original source library:
-- local infix is exactly the same operation on rational coordinates.

allConformalModesVanish : (D : Actor.ActorFactorGroup) →
  ∀ n (f : RationalState D) x →
  vertexMode D (conformalVector D) n f x ≡ 0ℚ
allConformalModesVanish D n f x =
  Seed.conformalModesVanish n (f x)

allVertexModesIntertwineRightAction :
  (D : Actor.ActorFactorGroup) →
  ∀ actor (f g : RationalState D) n x →
  Actor.rightAct D actor (vertexMode D f n g) x
  ≡ vertexMode D
      (Actor.rightAct D actor f) n
      (Actor.rightAct D actor g) x
allVertexModesIntertwineRightAction D actor f g n x = refl

vacuumIntertwinesRightAction :
  (D : Actor.ActorFactorGroup) →
  ∀ actor x →
  Actor.rightAct D actor (vacuum D) x ≡ vacuum D x
vacuumIntertwinesRightAction D actor x = refl

conformalIntertwinesRightAction :
  (D : Actor.ActorFactorGroup) →
  ∀ actor x →
  Actor.rightAct D actor (conformalVector D) x
  ≡ conformalVector D x
conformalIntertwinesRightAction D actor x = refl

translationIntertwinesRightAction :
  (D : Actor.ActorFactorGroup) →
  ∀ actor (f : RationalState D) x →
  Actor.rightAct D actor (translation D f) x
  ≡ translation D (Actor.rightAct D actor f) x
translationIntertwinesRightAction D actor f x = refl

rightActionIdentity :
  (D : Actor.ActorFactorGroup) →
  ∀ (f : RationalState D) x →
  Actor.rightAct D (Actor.identityActor D) f x ≡ f x
rightActionIdentity = Actor.rightActIdentity

rightActionComposition :
  (D : Actor.ActorFactorGroup) →
  ∀ g h (f : RationalState D) x →
  Actor.rightAct D (Actor.compose D g h) f x
  ≡ Actor.rightAct D h (Actor.rightAct D g f) x
rightActionComposition = Actor.rightActComposition
