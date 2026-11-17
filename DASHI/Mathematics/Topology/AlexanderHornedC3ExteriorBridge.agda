module DASHI.Mathematics.Topology.AlexanderHornedC3ExteriorBridge where

------------------------------------------------------------------------
-- ABSTRACT VAN KAMPEN / EQUVARIANT COMPLEMENT BRIDGE
--
-- PROVEN HERE: conditional interpretation of all finite-stage horn
-- replacements in a group equipped with a C3 action and compatible
-- meridian relations.  Word-level equivariance, preservation of each
-- replacement, and nontriviality transport from an essential meridian.
--
-- NOT PROVEN HERE: existence of a C3-equivariant wild embedding
-- D^3 -> S^3; equivalence between this algebraic model and the
-- complement pi_1; injectivity of the Hatcher free-group inclusions;
-- existence of an essential meridian; or nontriviality in Out(pi_1).
-- These must be supplied as separate geometric certificates.
--
-- The exterior S^3 minus an embedded closed ball is an OPEN,
-- NONCOMPACT three-manifold; the closed-manifold Poincare theorem
-- does not classify it.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as Finite

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record EquivariantMeridianGroup : Set₁ where
  field
    LoopClass : Set
    identity : LoopClass
    multiply : LoopClass → LoopClass → LoopClass
    invert : LoopClass → LoopClass

    associative : ∀ a b c →
      multiply (multiply a b) c ≡ multiply a (multiply b c)
    identityLeft : ∀ a → multiply identity a ≡ a
    identityRight : ∀ a → multiply a identity ≡ a
    inverseLeft : ∀ a → multiply (invert a) a ≡ identity
    inverseRight : ∀ a → multiply a (invert a) ≡ identity

    rotateLoop : LoopClass → LoopClass
    rotateLoopCubed : ∀ a →
      rotateLoop (rotateLoop (rotateLoop a)) ≡ a
    rotationPreservesIdentity : rotateLoop identity ≡ identity
    rotationPreservesMultiply : ∀ a b →
      rotateLoop (multiply a b)
        ≡ multiply (rotateLoop a) (rotateLoop b)
    rotationPreservesInverse : ∀ a →
      rotateLoop (invert a) ≡ invert (rotateLoop a)

    meridian : Finite.HornAddress → LoopClass
    rotationPreservesMeridian : ∀ a →
      rotateLoop (meridian a)
        ≡ meridian (Finite.rotateAddress a)
    meridianRefinesAsCommutator : ∀ a →
      meridian a ≡
        multiply
          (multiply
            (multiply
              (meridian (Finite.leftChild a))
              (meridian (Finite.rightChild a)))
            (invert (meridian (Finite.leftChild a))))
          (invert (meridian (Finite.rightChild a)))

open EquivariantMeridianGroup public

interpretWord : (G : EquivariantMeridianGroup) →
  Finite.Word → LoopClass G
interpretWord G Finite.unit = identity G
interpretWord G (Finite.generator a) = meridian G a
interpretWord G (Finite.inverseWord a) =
  invert G (interpretWord G a)
interpretWord G (Finite.combine a b) =
  multiply G (interpretWord G a) (interpretWord G b)

interpretRotation : (G : EquivariantMeridianGroup) →
  ∀ w → interpretWord G (Finite.rotateWord w)
    ≡ rotateLoop G (interpretWord G w)
interpretRotation G Finite.unit =
  sym (rotationPreservesIdentity G)
interpretRotation G (Finite.generator a) =
  sym (rotationPreservesMeridian G a)
interpretRotation G (Finite.inverseWord a) =
  trans
    (cong (invert G) (interpretRotation G a))
    (sym (rotationPreservesInverse G (interpretWord G a)))
interpretRotation G (Finite.combine a b) =
  trans
    (cong₂ (multiply G)
      (interpretRotation G a) (interpretRotation G b))
    (sym (rotationPreservesMultiply G
      (interpretWord G a) (interpretWord G b)))

-- The one-step word rewrite becomes equality after interpretation:
-- this is a genuine theorem *conditional on* the meridian relations.
interpretExpansion : (G : EquivariantMeridianGroup) →
  ∀ w → interpretWord G (Finite.expandWord w) ≡ interpretWord G w
interpretExpansion G Finite.unit = refl
interpretExpansion G (Finite.generator a) =
  sym (meridianRefinesAsCommutator G a)
interpretExpansion G (Finite.inverseWord w) =
  cong (invert G) (interpretExpansion G w)
interpretExpansion G (Finite.combine a b) =
  cong₂ (multiply G)
    (interpretExpansion G a) (interpretExpansion G b)

interpretExpansionAtEveryStage : (G : EquivariantMeridianGroup) →
  ∀ n w →
    interpretWord G (Finite.expandN n w) ≡ interpretWord G w
interpretExpansionAtEveryStage G zero w = refl
interpretExpansionAtEveryStage G (suc n) w =
  trans
    (interpretExpansion G (Finite.expandN n w))
    (interpretExpansionAtEveryStage G n w)

record EssentialMeridian (G : EquivariantMeridianGroup) : Set where
  field
    address : Finite.HornAddress
    notIdentity : meridian G address ≢ identity G

-- Exact nontriviality witness, without the tautological x input.
noTrivialMeridianIfEssential :
  (G : EquivariantMeridianGroup) →
  (certificate : EssentialMeridian G) →
  meridian G (EssentialMeridian.address certificate) ≢ identity G
noTrivialMeridianIfEssential G certificate =
  EssentialMeridian.notIdentity certificate
